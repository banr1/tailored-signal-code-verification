/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace0

/-!
# Clean Prefix Symbolic Execution and Half-Round Invariant

Defines closed-form symbolic states, messages, and SPQR salts for the 24-call clean prefix
(parameterized over `cls : Nat → Nat` and `spqrIdxs : Nat → UInt32`). Symbolically executes the
initial handshake calls `0..3` (`trClean1`, `trClean2`, `trClean3`) and proves the role-symmetric
half-round step specifications (`SyncPair`, `halfRound_send_spec`, `halfRound_full_spec`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace

open scoped DY.Libsignal.Composed
attribute [local instance]
  DY.Libsignal.Composed.instBytesFunctor_symbolic
  DY.Libsignal.Composed.instBytesLength_symbolic
  DY.Libsignal.Composed.instAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instExecTraceTypes_symbolic
  DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecEntryT
  DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasSubF
  DY.Libsignal.Composed.instHasSubFAttackerKnowledge
  DY.Libsignal.Composed.instHasSubFLength

open DY (Bytes Participant Trace Traceful ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk)
open DY.Libsignal.TripleRatchet
  (TRState TRSignalMsg TREvent RecvChain SessionInfo messageVersion maxReceiverChains
   kdfCk createChain findRecvChain setRecvChain consumeMessageKey parseTrSignalMsg)
open DY.Libsignal.Composed.Refinement
  (Step VisEntry Ghost OpaqueSymbolSemantics
   setupTrace runTrace runSteps storedStates availableStates storedSecrets
   honestKeysOf honestSaltsOf TrialCtx ownKeys whisperTrials gamma)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (Runs RndE NetE EvT EvP EvC StT StP rnd encMsg encSt encSig parse_encMsg mac_ok dec_ok
   bobSt0 bobOut bobAgreement_honest ratchetState recvSt skipTr createChain_comm dhPk_rnd_ne)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB pqskB bh1 kh1 o1 keys1 dhsA dhsB1 stA0 stB00 stB0' cB cB' cB'' seedB0 seedB1
   t1 t2 t3 t4 t5 t4_length t5_length seedB0_eq)
open Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas
  (spqrRecv_init_zero spqrRecv_init_pos)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux
  (pqSecretsList t1Pure t2Pure t3Pure t4Pure t1_eq_pure t2_eq_pure t3_eq_pure t4_eq_pure)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (r0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (cleanPingPongRound cleanCallSteps ssClean cleanMsgIdx cleanRecvTerm cleanPreKeyRep)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoSetup
  (setupTrace_r0_eq_t4 step0_next_t4 t5_getMessageSentAt_25 t5_getMessageSentAt_26
   cleanPreKeyRep_ek_ct)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace0
  (length_append le_append_of_le at?_append_of_lt at?_append_self at?_append_eq at?_mono getMessageSentAt_mono
   x25519LowOrder_dhPk bytesToLiteral_spqrSendMsg
   encTrGen step_messageEncrypt_next length_encTrGen encTrGen_le
   encTrGen_at?_pq encTrGen_getMessageSentAt_pq encTrGen_at?_st encTrGen_at?_msg
   encTrGen_getMessageSentAt_msg
   decSt0 decTr0 step_messageDecrypt0_next length_decTr0 decTr0_le decTr0_at?_st
   skippedStoredEvents skippedStoredEvents_nil skippedStoredEvents_append_non
   skippedStoredEvents_append_skipped skippedStoredEvents_encTrGen skippedStoredEvents_decTr0
   storedSecrets_append_pub storedSecrets_encTrGen storedSecrets_decTr0
   storedStates_append_pub storedStates_encTrGen storedStates_decTr0 honestKeysOf_append)

/-- Upper bound on the randomness timestamps of receiver-chain ratchet keys in `recv`. -/
def RecvTimestampsLt (bound : Nat) (recv : List RecvChain) : Prop :=
  ∀ c ∈ recv, ∃ ts, ts < bound ∧ c.ratchetKey = dhPk (rnd ts 32)

theorem recvTimestampsLt_mono {b₁ b₂ : Nat} (hle : b₁ ≤ b₂) {recv : List RecvChain}
    (h : RecvTimestampsLt b₁ recv) : RecvTimestampsLt b₂ recv := by
  intro c hc
  obtain ⟨ts, hlt, heq⟩ := h c hc
  exact ⟨ts, Nat.lt_of_lt_of_le hlt hle, heq⟩

theorem findRecvChain_eq_none_of_lt {bound ts : Nat} {recv : List RecvChain}
    (h : RecvTimestampsLt bound recv) (hle : bound ≤ ts) :
    findRecvChain recv (dhPk (rnd ts 32)) = none := by
  induction recv with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨ts_c, hlt, hrk⟩ := h c List.mem_cons_self
    have hne : c.ratchetKey ≠ dhPk (rnd ts 32) := by
      rw [hrk]
      exact dhPk_rnd_ne (by omega)
    have hbeq : (c.ratchetKey == dhPk (rnd ts 32)) = false := beq_false_of_ne hne
    unfold findRecvChain List.find?
    rw [hbeq]
    exact ih (fun x hx => h x (List.mem_cons_of_mem c hx))

theorem recvTimestampsLt_decSt0 {bound b₁ tsP : Nat} {st : TRState} {newDhs pqm : Bytes}
    (h : RecvTimestampsLt bound st.recv) (hb : bound ≤ b₁) (hts : tsP < b₁) :
    RecvTimestampsLt b₁ (decSt0 st (rnd tsP 32) newDhs pqm).recv := by
  intro x hx
  unfold decSt0 setRecvChain at hx
  rw [List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : y ∈ st.recv ++
      [{ ratchetKey := dhPk (rnd tsP 32),
         chainKey := (createChain st.rk (dhPk (rnd tsP 32)) st.dhs).2,
         index := 0, rIdx := st.rIdx + 2 }] :=
    List.mem_of_mem_drop hy
  cases heq : (y.ratchetKey == (ratchetState st (dhPk (rnd tsP 32)) newDhs).2.ratchetKey) with
  | true =>
    simp only [↓reduceIte]
    exact ⟨tsP, hts, rfl⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rcases List.mem_append.mp hy' with hmem | hmem
    · obtain ⟨ts_y, hlt_y, hrk_y⟩ := h y hmem
      exact ⟨ts_y, Nat.lt_of_lt_of_le hlt_y hb, hrk_y⟩
    · rw [List.mem_singleton] at hmem
      subst hmem
      exact ⟨tsP, hts, rfl⟩

def pqKeyOf (st : TRState) (cl curLen : Nat) : Bytes :=
  (DY.Spqr.spqrSend st.spqr (rnd (curLen + 1) cl)).2.1

def pqMsgOf (st : TRState) (cl curLen : Nat) : Bytes :=
  (DY.Spqr.spqrSend st.spqr (rnd (curLen + 1) cl)).2.2

def sendStOf (st : TRState) (cl curLen : Nat) : TRState :=
  encSt st (rnd (curLen + 1) cl)

def sendMsgOf (st : TRState) (cl curLen : Nat) : Bytes :=
  encMsg st (rnd (curLen + 1) cl) (pqKeyOf st cl curLen) (rnd curLen 32)

def recvStOf (rSt sSt : TRState) (cl curLen : Nat) : TRState :=
  decSt0 rSt sSt.dhs (rnd (curLen + 7) 32) (pqMsgOf sSt cl curLen)

def stA1c (cls : Nat → Nat) : TRState := sendStOf stA0 (cls 0) 31
def stA2c (cls : Nat → Nat) : TRState := sendStOf (stA1c cls) (cls 1) 38
def pqKey0 (cls : Nat → Nat) : Bytes := pqKeyOf stA0 (cls 0) 31
def pqKey1 (cls : Nat → Nat) : Bytes := pqKeyOf (stA1c cls) (cls 1) 38
def pqm1c (cls : Nat → Nat) : Bytes := pqMsgOf (stA1c cls) (cls 1) 38

def stB1c (cls : Nat → Nat) : TRState :=
  { stB0' with
    recv := [cB''],
    spqr := recvSt (DY.Spqr.spqrInit keys1.pqr DY.Libsignal.TripleRatchet.spqrB2A) (pqm1c cls) }

def bobInitKey (idx : UInt32) : Bytes :=
  if idx = 0 then DY.Spqr.zeroKey
  else DY.Spqr.spqrChainKey keys1.pqr
    (DY.Spqr.encodeSpqrDirectionParams DY.Spqr.Direction.a2b)
    (DY.Spqr.encodeSpqrIndexTerm idx)

def bobSkipEntry : SessionInfo × Bytes × UInt32 × Bytes :=
  (stB0'.sessionInfo "bob", dhPk dhsA, 0, seedB0)

/-- Active `(sender, receiver, senderState, receiverState)` entering half-round `h` (`0..10`). -/
def hrConfig (cls : Nat → Nat) : Nat → Participant × Participant × TRState × TRState
  | 0 => ("bob", "alice", stB1c cls, stA2c cls)
  | h + 1 =>
    let (me, peer, sSt, rSt) := hrConfig cls h
    let curLen := 55 + 14 * h
    let cl := cls (2 + h)
    (peer, me, recvStOf rSt sSt cl curLen, sendStOf sSt cl curLen)

def hrStates (cls : Nat → Nat) (h : Nat) : List (DY.PersistentLocalState.LocalState TRState) :=
  let (me, peer, sSt, rSt) := hrConfig cls h
  let curLen := 55 + 14 * h
  let cl := cls (2 + h)
  [⟨me, sendStOf sSt cl curLen⟩, ⟨peer, recvStOf rSt sSt cl curLen⟩]

/-- Stored `LocalState TRState` entries across clean calls `0..23`. -/
def allStates24 (cls : Nat → Nat) : List (DY.PersistentLocalState.LocalState TRState) :=
  [⟨"alice", stA0⟩, ⟨"alice", stA1c cls⟩, ⟨"alice", stA2c cls⟩, ⟨"bob", stB1c cls⟩] ++
    (List.range 10).flatMap (hrStates cls)

/-- Honest SPQR salts (`zeroKey` and the 12 `spqrSend` keys) across clean calls `0..23`. -/
def allSalts13 (cls : Nat → Nat) : List Bytes :=
  [DY.Spqr.zeroKey, pqKey0 cls, pqKey1 cls] ++
    (List.range 10).map fun h =>
      let (_, _, sSt, _) := hrConfig cls h
      pqKeyOf sSt (cls (2 + h)) (55 + 14 * h)

/-- Honest wire message sent at clean send index `j` (`0 ≤ j < 12`). -/
def cleanSendMsg (cls : Nat → Nat) (j : Nat) : Bytes :=
  if j = 0 then sendMsgOf stA0 (cls 0) 31
  else if j = 1 then sendMsgOf (stA1c cls) (cls 1) 38
  else
    let h := j - 2
    let (_, _, sSt, _) := hrConfig cls h
    sendMsgOf sSt (cls (2 + h)) (55 + 14 * h)

private theorem isCanonicalKey_dhPk (sk : Bytes) :
    DY.Libsignal.PQXDH.isCanonicalKey (dhPk sk) = true := by
  have hv : (dhPk sk).view? DY.X25519.Variant.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF
      ({ sk := sk } : DY.DiffieHellman.DhPk.SubF Bytes)
  have hl : DY.Libsignal.PQXDH.x25519LowOrder (dhPk sk) = false := x25519LowOrder_dhPk sk
  unfold DY.Libsignal.PQXDH.isCanonicalKey
  rw [hv, hl]; rfl

theorem at?_append_at {E : Type} [DY.ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) {i : Nat}
    (hi : tr.length = i) : (tr.append e).at? i = some e := by
  subst hi; exact Trace.at?_append tr e

private theorem skipTr_one (tr : ExecTrace) (s : SessionInfo) (pk : Bytes) (c : RecvChain)
    (src : Nat) (h1 : 1 - c.index.toNat = 1) (hi0 : c.index = 0) :
    skipTr tr s pk c src 1 =
      tr.append (EvT (.SkippedKeyStored s pk 0 (kdfCk c.chainKey).2 c.rIdx src)) := by
  dsimp only [skipTr]
  change ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk c.rIdx src c.chainKey c.index
    (1 - c.index.toNat)).run tr).2.val = _
  rw [h1, hi0]
  unfold DY.Libsignal.TripleRatchet.logSkippedKeys
  exact (Runs.bind
    (Runs.logEvent tr (TREvent.SkippedKeyStored s pk 0 (kdfCk c.chainKey).2 c.rIdx src))
    (by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; exact Runs.pure PUnit.unit _)).2

def trClean1 (cls : Nat → Nat) : ExecTrace :=
  encTrGen t5 "alice" 30 stA0 (cls 0) (pqKey0 cls)

def trClean2 (cls : Nat → Nat) : ExecTrace :=
  encTrGen (trClean1 cls) "alice" 36 (stA1c cls) (cls 1) (pqKey1 cls)

def trClean3 (cls : Nat → Nat) (idx : UInt32) : ExecTrace :=
  let tr := trClean2 cls
  let tr1 := (tr.append (RndE 32)).append (NetE (bobInitKey idx))
  let tr5 := (((tr1.append (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
      (kemPk pqskB) none o1.ek o1.ct keys1))).append
      (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB1)))).append
      (EvT (.HonestDH (stB0'.sessionInfo "bob") dhsB1 0))).append
      (EvC (.HandshakeSession (stB0'.sessionInfo "bob") 47))
  let trS := tr5.append (EvT (.SkippedKeyStored (stB0'.sessionInfo "bob") (dhPk dhsA) 0 seedB0 2 54))
  ((trS.append (EvT (.Received "bob" "alice" (dhPk dhsA) 1 (rnd 38 32)))).append
    (EvT (.MessageKey (stB0'.sessionInfo "bob") .receiver seedB1 (pqKey1 cls)
      1 2 54))).append
    (StT "bob" (stB1c cls))

theorem t5_at?_30 : t5.at? 30 = some (StT "alice" stA0) := by
  dsimp only [t5, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt]
  have hdhs : rnd (t4.length + 2) 32 = dhsA := by rw [t4_length]
  rw [hdhs]
  exact at?_append_at _ _ (by simp only [length_append, t4_length])

theorem step1_enc_next (cls : Nat → Nat) :
    (Step.messageEncrypt "alice" 30 (cls 0) 33).next t5 = trClean1 cls := by
  have hns : stA0.ns ≠ DY.Libsignal.TripleRatchet.u32Max := by decide
  have h := step_messageEncrypt_next (cl := cls 0) t5_at?_30 hns (by rw [t5_length])
  dsimp only at h
  rw [t5_length] at h
  exact h

theorem step2_enc_next (cls : Nat → Nat) :
    (Step.messageEncrypt "alice" 36 (cls 1) 40).next (trClean1 cls) = trClean2 cls := by
  have hlen1 : (trClean1 cls).length = 38 := by
    unfold trClean1; rw [length_encTrGen, t5_length]
  have hst36 : (trClean1 cls).at? 36 = some (StT "alice" (stA1c cls)) := by
    unfold trClean1 stA1c sendStOf
    have hc : rnd (t5.length + 1) (cls 0) = rnd 32 (cls 0) := by rw [t5_length]
    rw [← hc]
    exact encTrGen_at?_st t5 "alice" 30 stA0 (cls 0) (pqKey0 cls) (by rw [t5_length])
  have hns : (stA1c cls).ns ≠ DY.Libsignal.TripleRatchet.u32Max := by
    show (1 : UInt32) ≠ DY.Libsignal.TripleRatchet.u32Max; decide
  have h := step_messageEncrypt_next (cl := cls 1) hst36 hns (by rw [hlen1])
  dsimp only at h
  rw [hlen1] at h
  exact h

theorem trClean2_eq (cls : Nat → Nat) (spqrIdxs : Nat → UInt32) :
    runTrace r0 (ssClean cls spqrIdxs 3) = trClean2 cls ∧
    (trClean2 cls).length = 45 ∧
    t5 ≤ trClean2 cls ∧
    trClean1 cls ≤ trClean2 cls := by
  have hss : ssClean cls spqrIdxs 3 =
      [Step.aliceStart "alice" "bob" 4 6 bh1,
       Step.messageEncrypt "alice" 30 (cls 0) 33,
       Step.messageEncrypt "alice" 36 (cls 1) 40] := rfl
  have hs1 := step1_enc_next cls
  have hs2 := step2_enc_next cls
  have hlen1 : (trClean1 cls).length = 38 := by
    unfold trClean1; rw [length_encTrGen, t5_length]
  have hlen2 : (trClean2 cls).length = 45 := by
    unfold trClean2; rw [length_encTrGen, hlen1]
  have hle1 : t5 ≤ trClean1 cls := encTrGen_le _ _ _ _ _ _
  have hle2 : trClean1 cls ≤ trClean2 cls := encTrGen_le _ _ _ _ _ _
  refine ⟨?_, hlen2, Trace.le_trans _ _ _ hle1 hle2, hle2⟩
  rw [hss]; unfold runTrace; simp only [runSteps, setupTrace_r0_eq_t4, step0_next_t4, hs1, hs2]

theorem step3_bobStart_next (cls : Nat → Nat) (idx : UInt32) :
    (Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 idx).next (trClean2 cls) =
      trClean3 cls idx := by
  dsimp only [Step.next, Step.toInput]
  erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next
    DY.Libsignal.Composed.bobStart.reachability ("bob", "alice", kh1, 1, ⟨25, 26, 44⟩, 40, idx)
    (trClean2 cls)]
  have ha1 : t4.at? 1 = some (EvP (.IdentityRegistered "alice" (dhPk ikA) (DY.Signature.vk ikA) true)) := by
    rw [t4_eq_pure]; unfold t4Pure t3Pure t2Pure t1Pure
      Symbolic.Proofs.Tests.Shared.Composed.Runs.genPQPrekeyTr
      Symbolic.Proofs.Tests.Shared.Composed.Runs.genSignedPrekeyTr
      Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr
    simp only [length_append, Symbolic.DYBridge.DY.Trace.length_eq_1]
    repeat rw [at?_append_of_lt _ _ (by simp only [length_append, Symbolic.DYBridge.DY.Trace.length_eq_1]; omega)]
    exact at?_append_at _ _ (by simp only [length_append, Symbolic.DYBridge.DY.Trace.length_eq_1])
  have hb9 : t4.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
    rw [t4_eq_pure]; unfold t4Pure t3Pure t2Pure t1Pure
      Symbolic.Proofs.Tests.Shared.Composed.Runs.genPQPrekeyTr
      Symbolic.Proofs.Tests.Shared.Composed.Runs.genSignedPrekeyTr
      Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr
    simp only [length_append, Symbolic.DYBridge.DY.Trace.length_eq_1]
    repeat rw [at?_append_of_lt _ _ (by simp only [length_append, Symbolic.DYBridge.DY.Trace.length_eq_1]; omega)]
    exact at?_append_at _ _ (by simp only [length_append, Symbolic.DYBridge.DY.Trace.length_eq_1])
  have hs13 : t4.at? 13 = some (StP "bob" { kind := .signedPrekey, sk := spkB }) := by
    rw [t4_eq_pure]; unfold t4Pure t3Pure t2Pure t1Pure
      Symbolic.Proofs.Tests.Shared.Composed.Runs.genPQPrekeyTr
      Symbolic.Proofs.Tests.Shared.Composed.Runs.genSignedPrekeyTr
      Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr
    simp only [length_append, Symbolic.DYBridge.DY.Trace.length_eq_1]
    repeat rw [at?_append_of_lt _ _ (by simp only [length_append, Symbolic.DYBridge.DY.Trace.length_eq_1]; omega)]
    exact at?_append_at _ _ (by simp only [length_append, Symbolic.DYBridge.DY.Trace.length_eq_1])
  have hp19 : t4.at? 19 = some (StP "bob" { kind := .pqPrekey, sk := pqskB }) := by
    rw [t4_eq_pure]; unfold t4Pure t3Pure t2Pure t1Pure
      Symbolic.Proofs.Tests.Shared.Composed.Runs.genPQPrekeyTr
      Symbolic.Proofs.Tests.Shared.Composed.Runs.genSignedPrekeyTr
      Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr
    simp only [length_append, Symbolic.DYBridge.DY.Trace.length_eq_1]
    repeat rw [at?_append_of_lt _ _ (by simp only [length_append, Symbolic.DYBridge.DY.Trace.length_eq_1]; omega)]
    exact at?_append_at _ _ (by simp only [length_append, Symbolic.DYBridge.DY.Trace.length_eq_1])
  have hlen1 : (trClean1 cls).length = 38 := by unfold trClean1; rw [length_encTrGen, t5_length]
  have hlen2 : (trClean2 cls).length = 45 := by unfold trClean2; rw [length_encTrGen, hlen1]
  have h45 : t4 ≤ t5 := by
    dsimp only [t5, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt]
    exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _) _) _
  have h52 : t5 ≤ trClean2 cls :=
    Trace.le_trans _ _ _ (encTrGen_le _ _ _ _ _ _) (encTrGen_le _ _ _ _ _ _)
  have h42 : t4 ≤ trClean2 cls := Trace.le_trans _ _ _ h45 h52
  have hek : (trClean2 cls).at? 25 = some (NetE o1.ek) := by
    have h25 := t5_getMessageSentAt_25
    rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at h25
    cases hx : (t5.at? 25 : Option DY.Network.ExecEntryT) with
    | none => rw [hx] at h25; cases h25
    | some e => rw [hx] at h25; cases e; cases h25; exact at?_mono h52 hx
  have hct : (trClean2 cls).at? 26 = some (NetE o1.ct) := by
    have h26 := t5_getMessageSentAt_26
    rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at h26
    cases hx : (t5.at? 26 : Option DY.Network.ExecEntryT) with
    | none => rw [hx] at h26; cases h26
    | some e => rw [hx] at h26; cases e; cases h26; exact at?_mono h52 hx
  let c1 := rnd 39 (cls 1)
  let m1_c := rnd 38 32
  have hmsg : (trClean2 cls).at? 44 = some (NetE (encMsg (stA1c cls) c1 (pqKey1 cls) m1_c)) := by
    unfold trClean2
    have hc : rnd ((trClean1 cls).length + 1) (cls 1) = c1 := by rw [hlen1]
    have hm : rnd (trClean1 cls).length 32 = m1_c := by rw [hlen1]
    rw [← hc, ← hm]
    exact encTrGen_at?_msg (trClean1 cls) "alice" 36 (stA1c cls) (cls 1) (pqKey1 cls)
      (by rw [hlen1])
  have hpq40 : (trClean2 cls).at? 40 = some (NetE (pqKey1 cls)) := by
    unfold trClean2
    have h := encTrGen_at?_pq (trClean1 cls) "alice" 36 (stA1c cls) (cls 1) (pqKey1 cls)
      (by rw [hlen1])
    rw [hlen1] at h
    exact h
  have hpq : (((trClean2 cls).append (RndE 32)).append (NetE (bobInitKey idx))).at? 40 =
      some (NetE (pqKey1 cls)) := by
    rw [at?_append_of_lt _ _ (by rw [length_append, hlen2]; omega),
        at?_append_of_lt _ _ (by rw [hlen2]; omega)]
    exact hpq40
  have hrs : ratchetState (bobSt0 "alice" ikB spkB (dhPk ikA) keys1
      (encSig (stA1c cls) c1 (pqKey1 cls) m1_c))
      (encSig (stA1c cls) c1 (pqKey1 cls) m1_c).ratchetKey
      (rnd (trClean2 cls).length 32) = (stB0', cB) := by
    rw [hlen2]; rfl
  have hcons : consumeMessageKey cB (encSig (stA1c cls) c1 (pqKey1 cls) m1_c).counter =
      some (seedB1, cB'') := rfl
  have hrecv : DY.Spqr.spqrRecv stB0'.spqr (encSig (stA1c cls) c1 (pqKey1 cls) m1_c).pqRatchet idx =
      some ((stB1c cls).spqr, bobInitKey idx) := by
    change DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys1.pqr DY.Libsignal.TripleRatchet.spqrB2A)
      (pqm1c cls) idx = some (recvSt _ (pqm1c cls), bobInitKey idx)
    unfold bobInitKey
    by_cases hz : idx = 0
    · subst hz
      simp only [↓reduceIte]
      exact spqrRecv_init_zero keys1.pqr (pqm1c cls) .b2a
        (bytesToLiteral_spqrSendMsg (stA1c cls).spqr (rnd 39 (cls 1)))
    · simp only [hz, ↓reduceIte]
      exact spqrRecv_init_pos keys1.pqr (pqm1c cls) .b2a idx hz
        (bytesToLiteral_spqrSendMsg (stA1c cls).spqr (rnd 39 (cls 1)))
  have hseed1 : (kdfCk (stA1c cls).cks).2 = seedB1 := by
    change (kdfCk (kdfCk stA0.cks).1).2 = (kdfCk (kdfCk cB.chainKey).1).2
    have hck : stA0.cks = cB.chainKey := by
      show (createChain keys1.rk (dhPk spkB) dhsA).2 = (createChain keys1.rk (dhPk dhsA) spkB).2
      rw [createChain_comm keys1.rk dhsA spkB]
    rw [hck]
  have hset : setRecvChain stB0'.recv cB'' = [cB''] := by
    simp [setRecvChain, stB0', ratchetState, cB'', cB', cB, stB00, bobSt0, maxReceiverChains]
  have hrun := Runs.bobStart (kh := kh1) (mh := ⟨25, 26, 44⟩) (keys := keys1)
    (msg := encSig (stA1c cls) c1 (pqKey1 cls) m1_c)
    (t := encMsg (stA1c cls) c1 (pqKey1 cls) m1_c)
    (st' := stB0') (c := cB) (c' := cB'') (seed := seedB1)
    (pq := pqKey1 cls) (m := m1_c)
    (at?_mono h42 hb9) (at?_mono h42 hs13) (at?_mono h42 hp19) rfl (at?_mono h42 ha1) hek hct
    (isCanonicalKey_dhPk _)
    (bobAgreement_honest ikA (rnd t4.length 32) ikB spkB pqskB (rnd (t4.length + 1) 32))
    hmsg (parse_encMsg _ _ _ _) rfl (x25519LowOrder_dhPk dhsA) hrs hcons hrecv hpq
    (mac_ok (stR := stB0') (coins := c1) (pq := pqKey1 cls) (m := m1_c) hseed1 rfl rfl)
    (dec_ok (coins := c1) (pq := pqKey1 cls) (m := m1_c) hseed1)
    (stOut := stB1c cls) (by unfold stB1c; rw [hset])
  have h2 := hrun.2
  let bo := bobOut ikB spkB pqskB (dhPk ikA) o1.ek o1.ct keys1
  have hb1 : bo.ikB = dhPk ikB := rfl
  have hb2 : bo.ikA = dhPk ikA := rfl
  have hb3 : bo.spk = dhPk spkB := rfl
  have hb4 : bo.pqpk = kemPk pqskB := rfl
  have hb5 : bo.opk = none := rfl
  have hb6 : bo.ek = o1.ek := rfl
  have hb7 : bo.ct = o1.ct := rfl
  have hb8 : bo.keys = keys1 := rfl
  rw [hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8] at h2
  have hcnt : (encSig (stA1c cls) c1 (pqKey1 cls) m1_c).counter = 1 := rfl
  have hrk_eq : (encSig (stA1c cls) c1 (pqKey1 cls) m1_c).ratchetKey = dhPk dhsA := rfl
  have hpeer : stB0'.peer = "alice" := rfl
  have hdhsB : stB0'.dhs = dhsB1 := rfl
  have hridxB : stB0'.rIdx - 2 = 0 := rfl
  rw [hcnt, hrk_eq, hpeer, hdhsB, hridxB] at h2
  have hlen_tr1 : (((trClean2 cls).append (RndE 32)).append (NetE (bobInitKey idx))).length = 47 := by
    simp only [length_append, hlen2]
  have hchild : (((((((trClean2 cls).append (RndE 32)).append (NetE (bobInitKey idx))).append
      (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
        (kemPk pqskB) none o1.ek o1.ct keys1))).append
      (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB1)))).append
      (EvT (.HonestDH (stB0'.sessionInfo "bob") dhsB1 0))).append
      (EvC (.HandshakeSession (stB0'.sessionInfo "bob")
        (((trClean2 cls).append (RndE 32)).append (NetE (bobInitKey idx))).length))).length = 51 := by
    simp only [length_append, hlen2]
  rw [hlen_tr1] at h2 hchild
  have hidx0 : cB.index = 0 := rfl
  have hskip := skipTr_one
    (((((((trClean2 cls).append (RndE 32)).append (NetE (bobInitKey idx))).append
      (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
        (kemPk pqskB) none o1.ek o1.ct keys1))).append
      (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB1)))).append
      (EvT (.HonestDH (stB0'.sessionInfo "bob") dhsB1 0))).append
      (EvC (.HandshakeSession (stB0'.sessionInfo "bob") 47)))
    (stB0'.sessionInfo "bob") (dhPk dhsA) cB 54 rfl hidx0
  have h54 : 51 + ((1 : UInt32).toNat - cB.index.toNat) + 2 = 54 := rfl
  have hcBr : cB.rIdx = 2 := rfl
  rw [hchild, h54, hskip] at h2
  simp only [hcBr] at h2
  exact h2

/-- Role-symmetric invariant relating the active sender state `sSt` and receiver state `rSt` at
trace length `curLen` before each ping-pong half-round. -/
structure SyncPair (me peer : Participant) (sSt rSt : TRState) (tsS curLen : Nat) : Prop where
  peer_s : sSt.peer = peer
  peer_r : rSt.peer = me
  ik_my : sSt.myIk = rSt.peerIk
  ik_peer : sSt.peerIk = rSt.myIk
  dhs_s : sSt.dhs = rnd tsS 32
  tsS_lt : tsS < curLen
  ns_zero : sSt.ns = 0
  rk_eq : sSt.rk = (createChain rSt.rk (dhPk rSt.dhs) sSt.dhs).1
  cks_eq : sSt.cks = (createChain rSt.rk (dhPk rSt.dhs) sSt.dhs).2
  spqr_s : sSt.spqr.view? DY.Spqr.InitState.SubF = none
  spqr_r : rSt.spqr.view? DY.Spqr.InitState.SubF = none
  recv_r : RecvTimestampsLt tsS rSt.recv
  recv_s : RecvTimestampsLt curLen sSt.recv

theorem syncPair_initial (cls : Nat → Nat) :
    SyncPair "bob" "alice" (stB1c cls) (stA2c cls) 45 55 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (createChain (createChain keys1.rk (dhPk dhsA) spkB).1 (dhPk dhsA) dhsB1).1 =
      (createChain (createChain keys1.rk (dhPk spkB) dhsA).1 (dhPk dhsA) dhsB1).1
    rw [createChain_comm keys1.rk dhsA spkB]
  · show (createChain (createChain keys1.rk (dhPk dhsA) spkB).1 (dhPk dhsA) dhsB1).2 =
      (createChain (createChain keys1.rk (dhPk spkB) dhsA).1 (dhPk dhsA) dhsB1).2
    rw [createChain_comm keys1.rk dhsA spkB]
  · exact Symbolic.Proofs.Tests.Shared.Composed.Runs.notInit_recv _ _
  · exact Symbolic.Proofs.Tests.Shared.Composed.Runs.notInit_send _ _
  · intro c hc
    change c ∈ [{ ratchetKey := dhPk spkB, chainKey := keys1.ck, index := 0, rIdx := 1 }] at hc
    rw [List.mem_singleton] at hc; subst hc
    exact ⟨10, by omega, rfl⟩
  · intro c hc
    change c ∈ [cB''] at hc
    rw [List.mem_singleton] at hc; subst hc
    exact ⟨24, by omega, rfl⟩

theorem halfRound_send_spec {tr : ExecTrace} {me peer : Participant} {sStH : Nat}
    {sSt rSt : TRState} {tsS curLen cl : Nat}
    (hlen : tr.length = curLen) (hmin : 22 ≤ curLen)
    (hsSt : tr.at? sStH = some (StT me sSt))
    (hsync : SyncPair me peer sSt rSt tsS curLen) :
    let sSend := Step.messageEncrypt me sStH cl (curLen + 2)
    let tr1 := sSend.next tr
    tr1 = encTrGen tr me sStH sSt cl (pqKeyOf sSt cl curLen) ∧
    tr1.length = curLen + 7 ∧
    tr ≤ tr1 ∧
    tr1.at? (curLen + 5) = some (StT me (sendStOf sSt cl curLen)) ∧
    tr1.at? (curLen + 6) = some (NetE (sendMsgOf sSt cl curLen)) ∧
    tr1.getMessageSentAt (curLen + 6) = some (sendMsgOf sSt cl curLen) ∧
    honestKeysOf tr [sSend] = [pqKeyOf sSt cl curLen] ∧
    storedStates r0 tr1 = storedStates r0 tr ++ [⟨me, sendStOf sSt cl curLen⟩] ∧
    storedSecrets tr1 = storedSecrets tr ∧
    skippedStoredEvents tr1 = skippedStoredEvents tr := by
  have hns : sSt.ns ≠ DY.Libsignal.TripleRatchet.u32Max := by rw [hsync.ns_zero]; decide
  have hnext : (Step.messageEncrypt me sStH cl (curLen + 2)).next tr =
      encTrGen tr me sStH sSt cl (pqKeyOf sSt cl curLen) := by
    have h := step_messageEncrypt_next (cl := cl) hsSt hns (show curLen + 2 = tr.length + 2 by omega)
    dsimp only at h
    unfold pqKeyOf
    rw [hlen] at h
    exact h
  have hlen1 : (encTrGen tr me sStH sSt cl (pqKeyOf sSt cl curLen)).length = curLen + 7 := by
    rw [length_encTrGen, hlen]
  have hmin0 : (setupTrace r0).length ≤ tr.length := by
    rw [setupTrace_r0_eq_t4, t4_length]; omega
  refine ⟨hnext, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hnext, hlen1]
  · rw [hnext]; exact encTrGen_le _ _ _ _ _ _
  · rw [hnext]; unfold sendStOf; rw [← hlen]
    exact encTrGen_at?_st tr me sStH sSt cl _ rfl
  · rw [hnext]; unfold sendMsgOf; rw [← hlen]
    exact encTrGen_at?_msg tr me sStH sSt cl _ rfl
  · rw [hnext]; unfold sendMsgOf; rw [← hlen]
    exact encTrGen_getMessageSentAt_msg tr me sStH sSt cl _ rfl
  · unfold honestKeysOf Step.publishedSpqrKey?
      DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx
      DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx
    have hne3 : ¬ (curLen + 2 = tr.length + 3) := by omega
    simp only [hne3, ↓reduceIte, hnext]
    have hpq := encTrGen_getMessageSentAt_pq tr me sStH sSt cl (pqKeyOf sSt cl curLen)
    rw [hlen] at hpq
    rw [show tr.length + 2 = curLen + 2 by omega, hpq]; rfl
  · rw [hnext, storedStates_encTrGen r0 tr me sStH sSt cl _ hmin0, hlen]; rfl
  · rw [hnext]; exact storedSecrets_encTrGen _ _ _ _ _ _
  · rw [hnext]; exact skippedStoredEvents_encTrGen _ _ _ _ _ _

theorem halfRound_full_spec {tr : ExecTrace} {me peer : Participant} {sStH rStH : Nat}
    {sSt rSt : TRState} {tsS curLen cl : Nat} {idx : UInt32}
    (hlen : tr.length = curLen) (hmin : 22 ≤ curLen)
    (hsSt : tr.at? sStH = some (StT me sSt))
    (hrSt : tr.at? rStH = some (StT peer rSt))
    (hsync : SyncPair me peer sSt rSt tsS curLen) :
    let sSend := Step.messageEncrypt me sStH cl (curLen + 2)
    let sRecv := Step.messageDecrypt peer rStH (curLen + 6) (curLen + 2) idx
    let tr1 := sSend.next tr
    let tr2 := sRecv.next tr1
    let sSt1 := sendStOf sSt cl curLen
    let rSt1 := recvStOf rSt sSt cl curLen
    tr2.length = curLen + 14 ∧
    tr ≤ tr2 ∧
    tr2.at? (curLen + 5) = some (StT me sSt1) ∧
    tr2.at? (curLen + 13) = some (StT peer rSt1) ∧
    honestKeysOf tr [sSend, sRecv] = [pqKeyOf sSt cl curLen] ∧
    storedStates r0 tr2 = storedStates r0 tr ++ [⟨me, sSt1⟩, ⟨peer, rSt1⟩] ∧
    storedSecrets tr2 = storedSecrets tr ∧
    skippedStoredEvents tr2 = skippedStoredEvents tr ∧
    SyncPair peer me rSt1 sSt1 (curLen + 7) (curLen + 14) := by
  dsimp only
  have hts_lt : tsS < curLen := hsync.tsS_lt
  obtain ⟨hnext1, hlen1, hle1, hst1, hmsg1, _, hkeys1, hstates1, hsec1, hskip1⟩ :=
    halfRound_send_spec (cl := cl) hlen hmin hsSt hsync
  set tr1 := (Step.messageEncrypt me sStH cl (curLen + 2)).next tr
  have hrSt1 : tr1.at? rStH = some (StT peer rSt) := at?_mono hle1 hrSt
  have hpq1 : tr1.at? (curLen + 2) = some (NetE (pqKeyOf sSt cl curLen)) := by
    rw [hnext1]; unfold pqKeyOf; rw [← hlen]
    exact encTrGen_at?_pq tr me sStH sSt cl _ rfl
  have hfind : findRecvChain rSt.recv (dhPk sSt.dhs) = none := by
    rw [hsync.dhs_s]
    exact findRecvChain_eq_none_of_lt hsync.recv_r (Nat.le_refl tsS)
  have hnext2 : (Step.messageDecrypt peer rStH (curLen + 6) (curLen + 2) idx).next tr1 =
      decTr0 tr1 peer rStH rSt sSt.dhs (pqKeyOf sSt cl curLen)
        (pqMsgOf sSt cl curLen) (rnd curLen 32) := by
    exact step_messageDecrypt0_next hrSt1 hmsg1 hpq1 (by omega) hsync.ns_zero
      hsync.spqr_r hfind hsync.cks_eq hsync.ik_my.symm hsync.ik_peer.symm
  have hlen2 : ((Step.messageDecrypt peer rStH (curLen + 6) (curLen + 2) idx).next tr1).length =
      curLen + 14 := by
    rw [hnext2, length_decTr0, hlen1]
  have hle2 : tr1 ≤ (Step.messageDecrypt peer rStH (curLen + 6) (curLen + 2) idx).next tr1 := by
    rw [hnext2]; exact decTr0_le _ _ _ _ _ _ _ _
  have hmin1 : (setupTrace r0).length ≤ tr1.length := by
    rw [setupTrace_r0_eq_t4, t4_length]; omega
  refine ⟨hlen2, Trace.le_trans _ _ _ hle1 hle2, at?_mono hle2 hst1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hnext2]; unfold recvStOf
    have h := decTr0_at?_st tr1 peer rStH rSt sSt.dhs (pqKeyOf sSt cl curLen)
      (pqMsgOf sSt cl curLen) (rnd curLen 32) (i := curLen + 13) (by rw [hlen1])
    rw [hlen1] at h
    exact h
  · rw [show [Step.messageEncrypt me sStH cl (curLen + 2),
              Step.messageDecrypt peer rStH (curLen + 6) (curLen + 2) idx] =
        [Step.messageEncrypt me sStH cl (curLen + 2)] ++
        [Step.messageDecrypt peer rStH (curLen + 6) (curLen + 2) idx] from rfl,
      honestKeysOf_append, hkeys1]
    simp [honestKeysOf, Step.publishedSpqrKey?]
  · rw [hnext2, storedStates_decTr0 r0 tr1 peer rStH rSt sSt.dhs _ _ _ hmin1,
        hstates1, hlen1, List.append_assoc]; rfl
  · rw [hnext2, storedSecrets_decTr0, hsec1]
  · rw [hnext2, skippedStoredEvents_decTr0, hskip1]
  · refine ⟨hsync.peer_r, hsync.peer_s, hsync.ik_peer.symm, hsync.ik_my.symm,
      rfl, by omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (createChain (createChain rSt.rk (dhPk sSt.dhs) rSt.dhs).1
          (dhPk sSt.dhs) (rnd (curLen + 7) 32)).1 =
        (createChain sSt.rk (dhPk sSt.dhs) (rnd (curLen + 7) 32)).1
      rw [hsync.rk_eq, createChain_comm rSt.rk sSt.dhs rSt.dhs]
    · show (createChain (createChain rSt.rk (dhPk sSt.dhs) rSt.dhs).1
          (dhPk sSt.dhs) (rnd (curLen + 7) 32)).2 =
        (createChain sSt.rk (dhPk sSt.dhs) (rnd (curLen + 7) 32)).2
      rw [hsync.rk_eq, createChain_comm rSt.rk sSt.dhs rSt.dhs]
    · exact Symbolic.Proofs.Tests.Shared.Composed.Runs.notInit_recv _ _
    · exact Symbolic.Proofs.Tests.Shared.Composed.Runs.notInit_send _ _
    · exact recvTimestampsLt_mono (by omega) hsync.recv_s
    · have hdhs := hsync.dhs_s
      unfold recvStOf
      rw [hdhs]
      exact recvTimestampsLt_decSt0 hsync.recv_r (by omega) (by omega)

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace
