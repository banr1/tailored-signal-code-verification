/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Generic Half-Round and Ping-Pong Round Execution

Executes a single whisper send/receive half-round (`halfRound_step`), establishes the initial
post-`bobStart` invariant (`inv_at_4`), and composes two half-rounds into a 4-step ping-pong round
(`pingPongRound_wf`) for `cleanCallSteps cls cleanSpqrIdxs`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunRound

open DY (Bytes ExecTrace Participant Trace)
open DY.Bytes (view?)
open DY.DiffieHellman (dhPk)
open DY.Spqr (spqrSend spqrRecv)
open DY.Libsignal.TripleRatchet
  (TRState RecvChain kdfCk createChain findRecvChain setRecvChain isCurrentSnapshot u32Max)
open scoped DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement (Step runSteps StepsWF)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (Runs bobSt0 encSt encMsg encSig parse_encMsg ratchetState recvSt recvKey
   notInit_send notInit_recv mac_ok dec_ok rnd createChain_comm dhPk_rnd_ne
   aliceTr aliceTrOpt StT RndE NetE EvT)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB dhsA o1 keys1 stA0 t4 t5)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (cleanPingPongRound)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase
  (cleanSpqrIdxs ratchetKeyTimestamps append_len le_append_of_le at?_mono at?_append_at
   stepIn_next stepIn_isSome encTrGen encTrGen_length encTrGen_le
   x25519LowOrder_dhPk bytesToLiteral_spqrSendMsg skipTr_zero
   isCurrentSnapshot_self isCurrentSnapshot_non isCurrentSnapshot_ne
   AllRecvChainsHonest allRecvChainsHonest_append_non allRecvChainsHonest_append_st
   stA1Clean trClean2 trClean2_length
   coins2Clean stA2Clean trClean3 trClean3_length
   stB00Clean stB0'Clean stB3Clean trClean4 trClean4_length t4_entry_facts)

/-- Trace after a DH-ratchet `messageDecrypt` with counter `0` (`skip = 0`). -/
def ratchetDecTr (tr : ExecTrace) (me : Participant) (stH : Nat) (st' : TRState)
    (c : RecvChain) (pk seed pq pt key : Bytes) (stOut : TRState) : ExecTrace :=
  let tr1 := (((tr.append (RndE 32)).append (NetE key)).append
      (EvT (.DHRatchet me st'.peer pk (dhPk st'.dhs)))).append
      (EvT (.HonestDH (st'.sessionInfo me) st'.dhs (st'.rIdx - 2)))
  ((tr1.append (EvT (.Received me st'.peer pk 0 pt))).append
    (EvT (.MessageKey (st'.sessionInfo me) .receiver seed pq 0 c.rIdx stH))).append
    (StT me stOut)

theorem ratchetDecTr_length (tr : ExecTrace) (me : Participant) (stH : Nat) (st' : TRState)
    (c : RecvChain) (pk seed pq pt key : Bytes) (stOut : TRState) :
    (ratchetDecTr tr me stH st' c pk seed pq pt key stOut).length = tr.length + 7 := by
  dsimp only [ratchetDecTr]; simp only [append_len]

theorem ratchetDecTr_le (tr : ExecTrace) (me : Participant) (stH : Nat) (st' : TRState)
    (c : RecvChain) (pk seed pq pt key : Bytes) (stOut : TRState) :
    tr ≤ ratchetDecTr tr me stH st' c pk seed pq pt key stOut := by
  dsimp only [ratchetDecTr]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _

/-- Invariant held before each half-round `(sSend, sRecv)` of `cleanPingPongRound`. -/
structure HalfRoundInv (tr : ExecTrace) (sender receiver : Participant)
    (stHSend stHRecv tsSend tsRecv : Nat) (ikS ikR : Bytes)
    (stSend stRecv : TRState) : Prop where
  ne_party : (sender != receiver) = true ∧ (receiver != sender) = true
  at_send : tr.at? stHSend = some (StT sender stSend)
  cur_send : isCurrentSnapshot tr stHSend = true
  at_recv : tr.at? stHRecv = some (StT receiver stRecv)
  cur_recv : isCurrentSnapshot tr stHRecv = true
  send_meta : stSend.peer = receiver ∧ stSend.myIk = ikS ∧ stSend.peerIk = ikR ∧ stSend.ns = 0
  recv_meta : stRecv.peer = sender ∧ stRecv.myIk = ikR ∧ stRecv.peerIk = ikS
  dhs_eq : stSend.dhs = rnd tsSend 32 ∧ stRecv.dhs = rnd tsRecv 32
  ts_lt : tsRecv < tsSend ∧ tsSend < tr.length
  ts_mem : tsSend ∈ ratchetKeyTimestamps
  rk_cks : (stSend.rk, stSend.cks) = createChain stRecv.rk (dhPk stRecv.dhs) stSend.dhs
  spqr_send : stSend.spqr.view? DY.Spqr.InitState.SubF = none
  spqr_recv : stRecv.spqr.view? DY.Spqr.InitState.SubF = none
  chains_send : ∀ c ∈ stSend.recv, ∃ ts ∈ ratchetKeyTimestamps, ts < tsSend ∧ c.ratchetKey = dhPk (rnd ts 32)
  chains_recv : ∀ c ∈ stRecv.recv, ∃ ts ∈ ratchetKeyTimestamps, ts < tsSend ∧ c.ratchetKey = dhPk (rnd ts 32)
  honest_all : AllRecvChainsHonest tr

private theorem findRecvChain_none_of_lt {cs : List RecvChain} {tsSend : Nat}
    (hcs : ∀ c ∈ cs, ∃ ts ∈ ratchetKeyTimestamps, ts < tsSend ∧ c.ratchetKey = dhPk (rnd ts 32)) :
    findRecvChain cs (dhPk (rnd tsSend 32)) = none := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    obtain ⟨ts, _, hlt, hrk⟩ := hcs c List.mem_cons_self
    have hne : c.ratchetKey ≠ dhPk (rnd tsSend 32) := by
      rw [hrk]; exact dhPk_rnd_ne (Nat.ne_of_lt hlt)
    unfold findRecvChain List.find?
    have hbeq : (c.ratchetKey == dhPk (rnd tsSend 32)) = false := beq_false_of_ne hne
    rw [hbeq]
    exact ih (fun c' hc' => hcs c' (List.mem_cons_of_mem c hc'))

private theorem mem_setRecvChain {cs : List RecvChain} {cnew x : RecvChain}
    (hx : x ∈ setRecvChain cs cnew) : x ∈ cs ∨ x = cnew := by
  unfold setRecvChain at hx
  obtain ⟨d, hd, heq⟩ := List.mem_map.mp hx
  cases hdk : (d.ratchetKey == cnew.ratchetKey)
  · rw [hdk] at heq
    exact Or.inl (heq ▸ hd)
  · rw [hdk] at heq
    exact Or.inr heq.symm

theorem halfRound_step {tr : ExecTrace} {sender receiver : Participant}
    {stHSend stHRecv tsSend tsRecv cl : Nat} {ikS ikR : Bytes}
    {stSend stRecv : TRState}
    (hinv : HalfRoundInv tr sender receiver stHSend stHRecv tsSend tsRecv ikS ikR stSend stRecv)
    (hcl : cl = 0 ∨ cl = 32 ∨ cl = 64)
    (htsNew : tr.length + 7 ∈ ratchetKeyTimestamps) :
    let L := tr.length
    let sSend := Step.messageEncrypt sender stHSend cl (L + 2)
    let sRecv := Step.messageDecrypt receiver stHRecv (L + 6) (L + 2) 1
    let coins := rnd (L + 1) cl
    let pqKey := (spqrSend stSend.spqr coins).2.1
    let pqMsg := (spqrSend stSend.spqr coins).2.2
    let pt := rnd L 32
    let rs := ratchetState stRecv (dhPk stSend.dhs) (rnd (L + 7) 32)
    let c' : RecvChain := { rs.2 with chainKey := (kdfCk rs.2.chainKey).1, index := 1 }
    let stRecvTarget : TRState :=
      { rs.1 with recv := setRecvChain rs.1.recv c', spqr := recvSt stRecv.spqr pqMsg }
    ∃ (tr1 tr2 : ExecTrace) (stSendNext stRecvOut : TRState),
      sSend.PreCond tr ∧ sSend.LocalOk tr ∧ sSend.ok tr = true ∧ sSend.next tr = tr1 ∧
      sRecv.PreCond tr1 ∧ sRecv.LocalOk tr1 ∧ sRecv.ok tr1 = true ∧ sRecv.next tr1 = tr2 ∧
      tr1.getMessageSentAt (L + 6) = some (encMsg stSend coins pqKey pt) ∧
      tr ≤ tr1 ∧ tr1 ≤ tr2 ∧ tr1.length = L + 7 ∧ tr2.length = L + 14 ∧
      tr1 = encTrGen tr sender stHSend cl stSend pqKey ∧
      tr2 = ratchetDecTr tr1 receiver stHRecv rs.1 rs.2
        (dhPk stSend.dhs) (kdfCk rs.2.chainKey).2 pqKey pt (recvKey stRecv.spqr pqMsg) stRecvOut ∧
      stSendNext = encSt stSend coins ∧
      stRecvOut = stRecvTarget ∧
      HalfRoundInv tr2 receiver sender (L + 13) (L + 5) (L + 7) tsSend ikR ikS stRecvOut stSendNext := by
  intro L sSend sRecv coins pqKey pqMsg pt rs0 c0' stRecvTarget
  let stSendNext := encSt stSend coins
  let tr1 := encTrGen tr sender stHSend cl stSend pqKey
  let dhsNew := rnd (L + 7) 32
  let rs := ratchetState stRecv (dhPk stSend.dhs) dhsNew
  let c' : RecvChain := { rs.2 with chainKey := (kdfCk rs.2.chainKey).1, index := 1 }
  let stRecvOut : TRState :=
    { rs.1 with recv := setRecvChain rs.1.recv c', spqr := recvSt stRecv.spqr pqMsg }
  let tr2 := ratchetDecTr tr1 receiver stHRecv rs.1 rs.2
    (dhPk stSend.dhs) (kdfCk rs.2.chainKey).2 pqKey pt (recvKey stRecv.spqr pqMsg) stRecvOut
  have hns : stSend.ns ≠ u32Max := by rw [hinv.send_meta.2.2.2]; decide
  have hpqSend : (((tr.append (RndE 32)).append (RndE cl)).append
      (NetE (spqrSend stSend.spqr coins).2.1)).at? (L + 2) = some (NetE pqKey) :=
    at?_append_at _ (NetE pqKey) (by simp only [append_len, L])
  have hrSend := Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase.Runs.messageEncryptGen
    hinv.at_send hns hpqSend
  have hnext1 : sSend.next tr = tr1 :=
    (stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ tr).trans hrSend.2
  have hok1 : sSend.ok tr = true :=
    (stepIn_isSome DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ tr).trans
      (congrArg Option.isSome hrSend.1)
  have hlen1 : tr1.length = L + 7 := encTrGen_length _ _ _ _ _ _
  have hle1 : tr ≤ tr1 := encTrGen_le _ _ _ _ _ _
  have hatMsg1 : tr1.at? (L + 6) = some (NetE (encMsg stSend coins pqKey pt)) := by
    dsimp only [tr1, encTrGen]
    exact at?_append_at _ _ (by simp only [append_len, L])
  have hmsg1 : tr1.getMessageSentAt (L + 6) = some (encMsg stSend coins pqKey pt) := by
    rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hatMsg1]
  have hcurSend1 : isCurrentSnapshot tr1 (L + 5) = true := by
    dsimp only [tr1, encTrGen]
    exact isCurrentSnapshot_non _ rfl
      (isCurrentSnapshot_self _ _ _ (by simp only [append_len, L]))
  have hatSend1 : tr1.at? (L + 5) = some (StT sender stSendNext) := by
    dsimp only [tr1, encTrGen]
    exact at?_mono (Trace.append_le _ _)
      (at?_append_at _ _ (by simp only [append_len, L]))
  have hcurRecv1 : isCurrentSnapshot tr1 stHRecv = true := by
    dsimp only [tr1, encTrGen]
    refine isCurrentSnapshot_non _ rfl (isCurrentSnapshot_ne (by
      iterate 5 refine at?_mono (Trace.append_le _ _) ?_
      exact hinv.at_recv) hinv.ne_party.1 ?_)
    iterate 5 refine isCurrentSnapshot_non _ rfl ?_
    exact hinv.cur_recv
  have hatRecv1 : tr1.at? stHRecv = some (StT receiver stRecv) := at?_mono hle1 hinv.at_recv
  have hfind : findRecvChain stRecv.recv (encSig stSend coins pqKey pt).ratchetKey = none := by
    dsimp only [encSig]; rw [hinv.dhs_eq.1]
    exact findRecvChain_none_of_lt hinv.chains_recv
  have hlow : DY.Libsignal.TripleRatchet.x25519LowOrder
      (encSig stSend coins pqKey pt).ratchetKey = false :=
    x25519LowOrder_dhPk _
  have hrs_eq : ratchetState stRecv (encSig stSend coins pqKey pt).ratchetKey (rnd tr1.length 32) =
      (rs.1, rs.2) := by
    dsimp only [encSig, rs, dhsNew]; rw [hlen1]
  have hcons : DY.Libsignal.TripleRatchet.consumeMessageKey rs.2
      (encSig stSend coins pqKey pt).counter = some ((kdfCk rs.2.chainKey).2, c') := by
    dsimp only [encSig, rs, ratchetState, c']
    rw [hinv.send_meta.2.2.2]; rfl
  have hspqr : spqrRecv rs.1.spqr (encSig stSend coins pqKey pt).pqRatchet 1 =
      some (recvSt stRecv.spqr pqMsg, recvKey stRecv.spqr pqMsg) := by
    dsimp only [encSig, rs, ratchetState, pqMsg]
    unfold spqrRecv DY.Spqr.spqrEmptyMsg
    rw [bytesToLiteral_spqrSendMsg, hinv.spqr_recv]; rfl
  have hpqRecv : ((tr1.append (RndE 32)).append (NetE (recvKey stRecv.spqr pqMsg))).at? (L + 2) =
      some (NetE pqKey) := by
    refine at?_mono (le_append_of_le (Trace.append_le _ _) _) ?_
    dsimp only [tr1, encTrGen]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ (NetE pqKey) (by simp only [append_len, L]))
  have hcc : createChain stRecv.rk (dhPk stSend.dhs) stRecv.dhs = (stSend.rk, stSend.cks) := by
    rw [createChain_comm stRecv.rk stSend.dhs stRecv.dhs, ← hinv.rk_cks]
  have hseed : (kdfCk stSend.cks).2 = (kdfCk rs.2.chainKey).2 := by
    dsimp only [rs, ratchetState]; rw [hcc]
  have hpeerIk : rs.1.peerIk = stSend.myIk := by
    have h0 : rs.1.peerIk = stRecv.peerIk := rfl
    rw [h0, hinv.recv_meta.2.2, hinv.send_meta.2.1]
  have hmyIk : rs.1.myIk = stSend.peerIk := by
    have h0 : rs.1.myIk = stRecv.myIk := rfl
    rw [h0, hinv.recv_meta.2.1, hinv.send_meta.2.2.1]
  have hmac := mac_ok (stS := stSend) (stR := rs.1) (coins := coins) (pq := pqKey) (m := pt)
    hseed hpeerIk hmyIk
  have hdec := dec_ok (stS := stSend) (coins := coins) (pq := pqKey) (m := pt) hseed
  have hrRecv0 := Runs.messageDecrypt_ratchet (tr := tr1) (me := receiver) (stH := stHRecv)
    (msgH := L + 6) (pqH := L + 2) (idx := 1) (st := stRecv) (st' := rs.1)
    (t := encMsg stSend coins pqKey pt) (msg := encSig stSend coins pqKey pt)
    (c := rs.2) (c' := c') (pq := pqKey) (seed := (kdfCk rs.2.chainKey).2) (m := pt)
    (spqr' := recvSt stRecv.spqr pqMsg) (key := recvKey stRecv.spqr pqMsg)
    hatRecv1 hatMsg1 (parse_encMsg _ _ _ _) rfl hfind hlow hrs_eq hcons hspqr hpqRecv
    hmac hdec (stOut := stRecvOut) rfl
  have hrRecv : Runs (DY.Libsignal.TripleRatchet.messageDecrypt receiver stHRecv (L + 6) (L + 2) 1)
      tr1 (L + 13) tr2 := by
    obtain ⟨hr1, hr2⟩ := hrRecv0
    have hcnt0 : (encSig stSend coins pqKey pt).counter = 0 := hinv.send_meta.2.2.2
    have hidx0 : rs.2.index = 0 := rfl
    have hsz : (encSig stSend coins pqKey pt).counter.toNat - rs.2.index.toNat = 0 := by
      rw [hcnt0, hidx0]; rfl
    refine ⟨?_, ?_⟩
    · rw [skipTr_zero _ _ _ _ _ _ hsz] at hr1
      convert hr1 using 2
      simp only [append_len, hlen1]
    · rw [skipTr_zero _ _ _ _ _ _ hsz] at hr2
      rw [hr2]
      dsimp only [encSig, tr2, ratchetDecTr]
      rw [hinv.send_meta.2.2.2]
  have hnext2 : sRecv.next tr1 = tr2 :=
    (stepIn_next DY.Libsignal.TripleRatchet.messageDecrypt.reachability _ tr1).trans hrRecv.2
  have hok2 : sRecv.ok tr1 = true :=
    (stepIn_isSome DY.Libsignal.TripleRatchet.messageDecrypt.reachability _ tr1).trans
      (congrArg Option.isSome hrRecv.1)
  have hlen2 : tr2.length = L + 14 := by
    rw [ratchetDecTr_length, hlen1]
  have hle2 : tr1 ≤ tr2 := ratchetDecTr_le _ _ _ _ _ _ _ _ _ _ _
  have hhon1 : AllRecvChainsHonest tr1 := by
    dsimp only [tr1, encTrGen]
    refine allRecvChainsHonest_append_non _ rfl (allRecvChainsHonest_append_st ?_ ?_)
    · iterate 5 refine allRecvChainsHonest_append_non _ rfl ?_
      exact hinv.honest_all
    · intro c hc
      obtain ⟨ts, hmem, _, hrk⟩ := hinv.chains_send c hc
      exact ⟨ts, hmem, hrk⟩
  have hchains_out : ∀ c ∈ stRecvOut.recv,
      ∃ ts ∈ ratchetKeyTimestamps, ts < L + 7 ∧ c.ratchetKey = dhPk (rnd ts 32) := by
    intro c hc
    dsimp only [stRecvOut] at hc
    rcases mem_setRecvChain hc with hprev | rfl
    · dsimp only [rs, ratchetState] at hprev
      have hsub := List.mem_of_mem_drop hprev
      rw [List.mem_append, List.mem_singleton] at hsub
      rcases hsub with hold | rfl
      · obtain ⟨ts, hmem, _, hrk⟩ := hinv.chains_recv c hold
        exact ⟨ts, hmem, by have := hinv.ts_lt.2; omega, hrk⟩
      · exact ⟨tsSend, hinv.ts_mem, by have := hinv.ts_lt.2; omega, congrArg dhPk hinv.dhs_eq.1⟩
    · exact ⟨tsSend, hinv.ts_mem, by have := hinv.ts_lt.2; omega, congrArg dhPk hinv.dhs_eq.1⟩
  have hhon2 : AllRecvChainsHonest tr2 := by
    dsimp only [tr2, ratchetDecTr]
    refine allRecvChainsHonest_append_st ?_ (fun c hc => ?_)
    · iterate 6 refine allRecvChainsHonest_append_non _ rfl ?_
      exact hhon1
    · obtain ⟨ts, hmem, _, hrk⟩ := hchains_out c hc
      exact ⟨ts, hmem, hrk⟩
  have hatRecv2 : tr2.at? (L + 13) = some (StT receiver stRecvOut) := by
    dsimp only [tr2, ratchetDecTr]
    exact at?_append_at _ _ (by simp only [append_len, hlen1])
  have hcurRecv2 : isCurrentSnapshot tr2 (L + 13) = true := by
    dsimp only [tr2, ratchetDecTr]
    exact isCurrentSnapshot_self _ _ _ (by simp only [append_len, hlen1])
  have hcurSend2 : isCurrentSnapshot tr2 (L + 5) = true := by
    dsimp only [tr2, ratchetDecTr]
    refine isCurrentSnapshot_ne (by
      iterate 6 refine at?_mono (Trace.append_le _ _) ?_
      exact hatSend1) hinv.ne_party.2 ?_
    iterate 6 refine isCurrentSnapshot_non _ rfl ?_
    exact hcurSend1
  have hrk2 : (stRecvOut.rk, stRecvOut.cks) =
      createChain stSendNext.rk (dhPk stSendNext.dhs) stRecvOut.dhs := by
    dsimp only [stRecvOut, rs, ratchetState, stSendNext, encSt]; rw [hcc]
  have hinv2 : HalfRoundInv tr2 receiver sender (L + 13) (L + 5) (L + 7) tsSend
      ikR ikS stRecvOut stSendNext :=
    { ne_party := ⟨hinv.ne_party.2, hinv.ne_party.1⟩
      at_send := hatRecv2
      cur_send := hcurRecv2
      at_recv := at?_mono hle2 hatSend1
      cur_recv := hcurSend2
      send_meta := ⟨hinv.recv_meta.1, hinv.recv_meta.2.1, hinv.recv_meta.2.2, rfl⟩
      recv_meta := ⟨hinv.send_meta.1, hinv.send_meta.2.1, hinv.send_meta.2.2.1⟩
      dhs_eq := ⟨rfl, hinv.dhs_eq.1⟩
      ts_lt := ⟨by have := hinv.ts_lt.2; omega, by omega⟩
      ts_mem := htsNew
      rk_cks := hrk2
      spqr_send := notInit_recv _ _
      spqr_recv := notInit_send _ _
      chains_send := hchains_out
      chains_recv := fun c hc => by
        obtain ⟨ts, hmem, _, hrk⟩ := hinv.chains_send c hc
        exact ⟨ts, hmem, by have := hinv.ts_lt.2; omega, hrk⟩
      honest_all := hhon2 }
  exact ⟨tr1, tr2, stSendNext, stRecvOut,
    hinv.cur_send, ⟨hcl, Or.inl rfl⟩, hok1, hnext1,
    hcurRecv1, trivial, hok2, hnext2, hmsg1, hle1, hle2, hlen1, hlen2,
    rfl, rfl, rfl, rfl, hinv2⟩

theorem inv_at_4 (cls : Nat → Nat) :
    HalfRoundInv (trClean4 cls) "bob" "alice" 54 43 45 24
      (DY.Libsignal.PQXDH.serializedIk (dhPk ikB))
      (DY.Libsignal.PQXDH.serializedIk (dhPk ikA))
      (stB3Clean cls) (stA2Clean cls) := by
  have hcur_tr3_43 : isCurrentSnapshot (trClean3 cls) 43 = true := by
    dsimp only [trClean3, encTrGen]
    exact isCurrentSnapshot_non _ rfl
      (isCurrentSnapshot_self _ _ _ (by simp only [append_len, trClean2_length]))
  have hst_tr3_43 : (trClean3 cls).at? 43 = some (StT "alice" (stA2Clean cls)) := by
    dsimp only [trClean3, encTrGen, stA2Clean]
    have hc : rnd ((trClean2 cls).length + 1) (cls 1) = coins2Clean cls := by
      rw [trClean2_length]; rfl
    rw [hc]
    exact at?_mono (Trace.append_le _ _)
      (at?_append_at _ _ (by simp only [append_len, trClean2_length]))
  have hst_tr4_43 : (trClean4 cls).at? 43 = some (StT "alice" (stA2Clean cls)) := by
    dsimp only [trClean4]
    iterate 10 refine at?_mono (Trace.append_le _ _) ?_
    exact hst_tr3_43
  have hcur_tr4_43 : isCurrentSnapshot (trClean4 cls) 43 = true := by
    dsimp only [trClean4]
    refine isCurrentSnapshot_ne (by
      iterate 9 refine at?_mono (Trace.append_le _ _) ?_
      exact hst_tr3_43) rfl ?_
    iterate 9 refine isCurrentSnapshot_non _ rfl ?_
    exact hcur_tr3_43
  have hcur_tr4_54 : isCurrentSnapshot (trClean4 cls) 54 = true := by
    dsimp only [trClean4]
    exact isCurrentSnapshot_self _ _ _ (by simp only [append_len, trClean3_length])
  have hst_tr4_54 : (trClean4 cls).at? 54 = some (StT "bob" (stB3Clean cls)) := by
    dsimp only [trClean4]
    exact at?_append_at _ _ (by simp only [append_len, trClean3_length])
  have hhon_t4 : AllRecvChainsHonest t4 := t4_entry_facts.2.2.2.2
  have hstA0_chains : ∀ c ∈ stA0.recv,
      ∃ ts ∈ ratchetKeyTimestamps, ts < 45 ∧ c.ratchetKey = dhPk (rnd ts 32) := by
    intro c hc
    dsimp only [stA0, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt] at hc
    rw [List.mem_singleton] at hc; subst hc
    exact ⟨10, by decide, by decide, rfl⟩
  have hhon_t5 : AllRecvChainsHonest t5 := by
    dsimp only [t5, aliceTr, aliceTrOpt]
    refine allRecvChainsHonest_append_st ?_ (fun c hc => ?_)
    · iterate 8 refine allRecvChainsHonest_append_non _ rfl ?_
      exact hhon_t4
    · obtain ⟨ts, hm, _, hrk⟩ := hstA0_chains c hc
      exact ⟨ts, hm, hrk⟩
  have hhon_tr2 : AllRecvChainsHonest (trClean2 cls) := by
    dsimp only [trClean2, encTrGen]
    refine allRecvChainsHonest_append_non _ rfl (allRecvChainsHonest_append_st ?_ ?_)
    · iterate 5 refine allRecvChainsHonest_append_non _ rfl ?_
      exact hhon_t5
    · intro c hc
      obtain ⟨ts, hm, _, hrk⟩ := hstA0_chains c hc
      exact ⟨ts, hm, hrk⟩
  have hhon_tr3 : AllRecvChainsHonest (trClean3 cls) := by
    dsimp only [trClean3, encTrGen]
    refine allRecvChainsHonest_append_non _ rfl (allRecvChainsHonest_append_st ?_ ?_)
    · iterate 5 refine allRecvChainsHonest_append_non _ rfl ?_
      exact hhon_tr2
    · intro c hc
      obtain ⟨ts, hm, _, hrk⟩ := hstA0_chains c hc
      exact ⟨ts, hm, hrk⟩
  have hstB3_chains : ∀ c ∈ (stB3Clean cls).recv,
      ∃ ts ∈ ratchetKeyTimestamps, ts < 45 ∧ c.ratchetKey = dhPk (rnd ts 32) := by
    intro c hc
    dsimp only [stB3Clean] at hc
    rw [List.mem_singleton] at hc; subst hc
    exact ⟨24, by decide, by decide, rfl⟩
  have hhon_tr4 : AllRecvChainsHonest (trClean4 cls) := by
    dsimp only [trClean4]
    refine allRecvChainsHonest_append_st ?_ (fun c hc => ?_)
    · iterate 9 refine allRecvChainsHonest_append_non _ rfl ?_
      exact hhon_tr3
    · obtain ⟨ts, hm, _, hrk⟩ := hstB3_chains c hc
      exact ⟨ts, hm, hrk⟩
  have hrk : ((stB3Clean cls).rk, (stB3Clean cls).cks) =
      createChain (stA2Clean cls).rk (dhPk (stA2Clean cls).dhs) (stB3Clean cls).dhs := by
    dsimp only [stB3Clean, stB0'Clean, ratchetState, stB00Clean, bobSt0,
      stA2Clean, stA1Clean, encSt, stA0, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt]
    have hk : o1.keys = keys1 := rfl
    have hs : o1.spk = dhPk spkB := rfl
    rw [hk, hs, createChain_comm keys1.rk dhsA spkB]
  exact
    { ne_party := ⟨rfl, rfl⟩
      at_send := hst_tr4_54
      cur_send := hcur_tr4_54
      at_recv := hst_tr4_43
      cur_recv := hcur_tr4_43
      send_meta := ⟨rfl, rfl, rfl, rfl⟩
      recv_meta := ⟨rfl, rfl, rfl⟩
      dhs_eq := ⟨rfl, rfl⟩
      ts_lt := ⟨by decide, by rw [trClean4_length]; decide⟩
      ts_mem := by decide
      rk_cks := hrk
      spqr_send := notInit_recv _ _
      spqr_recv := notInit_send _ _
      chains_send := hstB3_chains
      chains_recv := hstA0_chains
      honest_all := hhon_tr4 }

theorem stepsWF_cons {s : Step} {ss : List Step} {tr tr' : ExecTrace}
    (hp : s.PreCond tr) (hl : s.LocalOk tr) (hnext : s.next tr = tr')
    (hrest : StepsWF ss tr') : StepsWF (s :: ss) tr :=
  ⟨hp, hl, hnext ▸ hrest⟩

/-- Executes one 4-step ping-pong round `rd` from `HalfRoundInv`, advancing the trace by 28 entries
and re-establishing `HalfRoundInv` for round `rd + 1`. -/
theorem pingPongRound_wf {tr : ExecTrace} {cls : Nat → Nat}
    {rd aSt bSt curLen tsB tsA : Nat} {stB stA : TRState}
    (hcur : tr.length = curLen)
    (hinv : HalfRoundInv tr "bob" "alice" bSt aSt tsB tsA
      (DY.Libsignal.PQXDH.serializedIk (dhPk ikB))
      (DY.Libsignal.PQXDH.serializedIk (dhPk ikA)) stB stA)
    (hcl1 : cls (2 + 2 * rd) = 0 ∨ cls (2 + 2 * rd) = 32 ∨ cls (2 + 2 * rd) = 64)
    (hcl2 : cls (2 + 2 * rd + 1) = 0 ∨ cls (2 + 2 * rd + 1) = 32 ∨ cls (2 + 2 * rd + 1) = 64)
    (hidx1 : cleanSpqrIdxs (4 + 4 * rd + 1) = 1)
    (hidx2 : cleanSpqrIdxs (4 + 4 * rd + 3) = 1)
    (hts1 : curLen + 7 ∈ ratchetKeyTimestamps)
    (hts2 : curLen + 21 ∈ ratchetKeyTimestamps) :
    let (rs, aNext, bNext, lenNext) := cleanPingPongRound cls cleanSpqrIdxs rd aSt bSt curLen
    ∃ (trOut : ExecTrace) (stBOut stAOut : TRState),
      runSteps rs tr = trOut ∧
      StepsWF rs tr ∧
      (∀ i < 4, ∀ s, rs[i]? = some s → s.ok (runSteps (rs.take i) tr) = true) ∧
      (∃ mB tsM, tsM ∈ ratchetKeyTimestamps ∧
        (runSteps (rs.take 1) tr).getMessageSentAt (curLen + 6) = some mB ∧
        DY.Libsignal.TripleRatchet.parseTrSignalMsg mB ≠ none ∧
        (∀ sig, DY.Libsignal.TripleRatchet.parseTrSignalMsg mB = some sig →
          sig.ratchetKey = dhPk (rnd tsM 32))) ∧
      (∃ mA tsM, tsM ∈ ratchetKeyTimestamps ∧
        (runSteps (rs.take 3) tr).getMessageSentAt (curLen + 20) = some mA ∧
        DY.Libsignal.TripleRatchet.parseTrSignalMsg mA ≠ none ∧
        (∀ sig, DY.Libsignal.TripleRatchet.parseTrSignalMsg mA = some sig →
          sig.ratchetKey = dhPk (rnd tsM 32))) ∧
      tr ≤ trOut ∧ trOut.length = lenNext ∧ lenNext = curLen + 28 ∧
      HalfRoundInv trOut "bob" "alice" bNext aNext (curLen + 21) (curLen + 7)
        (DY.Libsignal.PQXDH.serializedIk (dhPk ikB))
        (DY.Libsignal.PQXDH.serializedIk (dhPk ikA)) stBOut stAOut := by
  subst hcur
  dsimp only [cleanPingPongRound]
  rw [hidx1, hidx2]
  have h1 := halfRound_step hinv hcl1 hts1
  rcases h1 with ⟨tr1, tr2, stSend1, stRecv1,
    hp1, hl1, hok1, hn1, hp2, hl2, hok2, hn2, hmsg1, hle1, hle2, hlen1, hlen2,
    _, _, _, _, hinv2⟩
  have h2 := halfRound_step hinv2 hcl2 (by rw [hlen2]; exact hts2)
  rcases h2 with ⟨tr3, tr4, stSend2, stRecv2,
    hp3, hl3, hok3, hn3, hp4, hl4, hok4, hn4, hmsg3, hle3, hle4, hlen3, hlen4,
    _, _, _, _, hinv4⟩
  rw [hlen2] at hp3 hl3 hok3 hn3 hp4 hl4 hok4 hn4 hmsg3 hlen3 hlen4 hinv4
  have h20 : tr.length + 14 + 6 = tr.length + 7 + 7 + 6 := by omega
  have h16 : tr.length + 14 + 2 = tr.length + 7 + 7 + 2 := by omega
  have h19 : tr.length + 14 + 5 = tr.length + 7 + 7 + 5 := by omega
  have h27 : tr.length + 14 + 13 = tr.length + 7 + 7 + 7 + 6 := by omega
  have h28 : tr.length + 14 + 14 = tr.length + 7 + 7 + 7 + 7 := by omega
  have hinv4' : HalfRoundInv tr4 "bob" "alice"
      (tr.length + 7 + 7 + 7 + 6) (tr.length + 7 + 7 + 5) (tr.length + 21) (tr.length + 7)
      (DY.Libsignal.PQXDH.serializedIk (dhPk ikB))
      (DY.Libsignal.PQXDH.serializedIk (dhPk ikA)) stRecv2 stSend2 := by
    rw [← h27, ← h19]
    simpa only [show tr.length + 14 + 7 = tr.length + 21 by omega] using hinv4
  refine ⟨tr4, stRecv2, stSend2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, hinv4'⟩
  · simp only [runSteps, hn1, hn2]
    rw [← h16] at *; rw [hn3, ← h20, hn4]
  · refine stepsWF_cons hp1 hl1 hn1 (stepsWF_cons hp2 hl2 hn2 ?_)
    rw [← h16, ← h20]
    exact stepsWF_cons hp3 hl3 hn3 (stepsWF_cons hp4 hl4 hn4 trivial)
  · intro i hi4 s hs
    match i with
    | 0 => simp at hs; subst hs; exact hok1
    | 1 => simp [runSteps, hn1] at hs ⊢; subst hs; exact hok2
    | 2 =>
      simp [runSteps, hn1, hn2] at hs ⊢; subst hs
      rw [← h16]; exact hok3
    | 3 =>
      simp [runSteps, hn1, hn2] at hs ⊢; subst hs
      rw [← h16] at *; rw [hn3, ← h20]; exact hok4
    | n + 4 => omega
  · refine ⟨encMsg stB (rnd (tr.length + 1) (cls (2 + 2 * rd)))
        (spqrSend stB.spqr (rnd (tr.length + 1) (cls (2 + 2 * rd)))).2.1 (rnd tr.length 32),
        tsB, hinv.ts_mem, ?_, ?_, ?_⟩
    · simp only [List.take, runSteps, hn1]; exact hmsg1
    · rw [parse_encMsg]; exact Option.some_ne_none _
    · intro sig hsig; rw [parse_encMsg] at hsig; injection hsig with hsig'
      rw [← hsig']; dsimp only [encSig]; rw [hinv.dhs_eq.1]
  · refine ⟨encMsg stRecv1 (rnd (tr.length + 14 + 1) (cls (2 + 2 * rd + 1)))
        (spqrSend stRecv1.spqr (rnd (tr.length + 14 + 1) (cls (2 + 2 * rd + 1)))).2.1
        (rnd (tr.length + 14) 32),
        tr.length + 7, hts1, ?_, ?_, ?_⟩
    · simp only [List.take, runSteps, hn1, hn2]
      rw [← h16, hn3, show tr.length + 20 = tr.length + 14 + 6 by omega]
      exact hmsg3
    · rw [parse_encMsg]; exact Option.some_ne_none _
    · intro sig hsig; rw [parse_encMsg] at hsig; injection hsig with hsig'
      rw [← hsig']; dsimp only [encSig]; rw [hinv2.dhs_eq.1]
  · exact Trace.le_trans _ _ _ (Trace.le_trans _ _ _ hle1 hle2) (Trace.le_trans _ _ _ hle3 hle4)
  · exact hlen4.trans h28

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunRound
