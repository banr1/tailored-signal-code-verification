/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoStateSafe
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTraceTop

/-!
# Certified Prefix DAG Walk Across States, Sends, and Salts

Propagates `StateWitness`, `SendStepOut`, and `honestSalts` `TermAt` witnesses across Calls `0..3`
and all 10 ping-pong half-rounds (`walk_calls_0_to_2`, `walk_hr_send`, `walk_hr_prefix`), and
derives `SafeMemo2` for every serialized local `TRState` along clean prefixes.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk1

open scoped DY.Libsignal.Composed
open DY (Bytes ExecTrace Participant)
open DY.DiffieHellman (dhPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.PQXDH (serializedIk)
open DY.Libsignal.TripleRatchet
  (TRState TRSignalMsg RecvChain spqrA2B spqrB2A lit litByte
   hmac kdfCk kdfRk createChain setRecvChain maxReceiverChains parseTrSignalMsg)
open DY.Libsignal.Composed.Refinement
  (OpaqueSymbolSemantics Ghost VisEntry TrialCtx MacTagForgeryOrCollision
   runTrace prefixTerms principalTerms plaintextTerms storedStates storedSecrets
   honestSaltsOf randTerm)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (rnd encMsg encSt encSig parse_encMsg ratchetState createChain_comm dhPk_rnd_ne recvSt)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB o1 keys1 dhsA dhsB1 stA0 stB00 stB0' cB cB' cB'' seedB0 seedB0_eq)
open Symbolic.BugInjection.Proofs.Common443.Census443Memo (memoOK_spqrRecvState_pack)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0 (evictedI0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (r0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (ValidCoinLens whisperOrReplayIndices ssClean cleanRecvTerm cleanPreKeyRep)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagSize dagOp dagBytes honestSaltIds)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoCombinators
  (SafeMemo TermAt safeMemo_lit_short safeMemo_plaintext)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTermAt
  (safeMemo_spqrInit)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrials
  (isKdfOp isConcatOp termAt_strLit)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace0 (decSt0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace
  (pqKeyOf pqMsgOf sendStOf sendMsgOf recvStOf stA1c stA2c pqKey0 pqKey1 pqm1c stB1c
   hrConfig hrStates allStates24 allSalts13 cleanSendMsg)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTraceTop
  (summary_at_3 summary_at_whisperOrReplay)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPinsEv
  (sendPtTs sendWmacId recvDhsTs recvSkId)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins (PrefixPinned)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk0
  (isRandOp isDhPkOp checkDhRand termAt_lit_b termAt_rand_b termAt_concat_b
   termAt_dhPk_b termAt_dh_b termAt_kdf_b norm_dhPk createChain_dhPk
   handshake_termAt pqSecrets_safeMemo)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalkSend
  (getSendRow SendStepOut send_step_at cls0 encSt_toDRState decSt0_toDRState hrConfig_toDRState)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoStateSafe
  (SafeMemo2 safeMemo_toSafeMemo2 safeMemo2_trState_of_dr not_macTagForgery_of_sendStep)

def checkCreateChain (rk_id s1 pk1 ts1 s2 pk2 ts2 dh_id prk_id rk2_id c2_id cks_id : Nat) : Bool :=
  decide (prk_id < dagSize) && decide (rk2_id < dagSize) &&
  decide (c2_id < dagSize) && decide (cks_id < dagSize) &&
  checkDhRand s1 pk1 s2 pk2 dh_id ts1 ts2 &&
  isKdfOp (dagOp prk_id) rk_id dh_id &&
  isKdfOp (dagOp rk2_id) prk_id 16 &&
  isConcatOp (dagOp c2_id) rk2_id 17 &&
  isKdfOp (dagOp cks_id) prk_id c2_id

theorem termAt_createChain_dhPk {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {rk : Bytes}
    {rk_id s1 pk1 ts1 s2 pk2 ts2 dh_id prk_id rk2_id c2_id cks_id : Nat}
    (hok : checkCreateChain rk_id s1 pk1 ts1 s2 pk2 ts2 dh_id prk_id rk2_id c2_id cks_id = true)
    (trk : TermAt dagSize dagOp dagBytes S g pts rk rk_id)
    (tsk1 : TermAt dagSize dagOp dagBytes S g pts (rnd ts1 32) s1)
    (tpk1 : TermAt dagSize dagOp dagBytes S g pts (dhPk (rnd ts1 32)) pk1)
    (tsk2 : TermAt dagSize dagOp dagBytes S g pts (rnd ts2 32) s2)
    (tpk2 : TermAt dagSize dagOp dagBytes S g pts (dhPk (rnd ts2 32)) pk2) :
    TermAt dagSize dagOp dagBytes S g pts (DY.DiffieHellman.dh (dhPk (rnd ts1 32)) (rnd ts2 32)) dh_id ∧
    TermAt dagSize dagOp dagBytes S g pts (hmac rk (DY.DiffieHellman.dh (dhPk (rnd ts1 32)) (rnd ts2 32))) prk_id ∧
    TermAt dagSize dagOp dagBytes S g pts (createChain rk (dhPk (rnd ts1 32)) (rnd ts2 32)).1 rk2_id ∧
    TermAt dagSize dagOp dagBytes S g pts (createChain rk (dhPk (rnd ts1 32)) (rnd ts2 32)).2 cks_id := by
  unfold checkCreateChain at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hprk_lt, hrk2_lt⟩, hc2_lt⟩, hcks_lt⟩,
    hdh_op⟩, hprk_op⟩, hrk2_op⟩, hc2_op⟩, hcks_op⟩ := hok
  have tb01 : TermAt dagSize dagOp dagBytes S g pts (litByte 1) 2 := termAt_lit_b (id := 2) (by decide +kernel)
  have tb02 : TermAt dagSize dagOp dagBytes S g pts (litByte 2) 3 := termAt_lit_b (id := 3) (by decide +kernel)
  have twrlbl : TermAt dagSize dagOp dagBytes S g pts (lit "WhisperRatchet") 10 :=
    termAt_strLit (by decide) (by decide +kernel)
  have twri1 := termAt_concat_b (id := 16) (by decide +kernel) twrlbl tb01
  have twri2 := termAt_concat_b (id := 17) (by decide +kernel) twrlbl tb02
  have tdh := termAt_dh_b hdh_op tsk1 tpk1 tsk2 tpk2
  have tprk := termAt_kdf_b (Bool.and_eq_true_iff.mpr ⟨decide_eq_true hprk_lt, hprk_op⟩) trk tdh
  have trk2 := termAt_kdf_b (Bool.and_eq_true_iff.mpr ⟨decide_eq_true hrk2_lt, hrk2_op⟩) tprk twri1
  have tc2 := termAt_concat_b (Bool.and_eq_true_iff.mpr ⟨decide_eq_true hc2_lt, hc2_op⟩) trk2 twri2
  have tcks := termAt_kdf_b (Bool.and_eq_true_iff.mpr ⟨decide_eq_true hcks_lt, hcks_op⟩) tprk tc2
  rw [createChain_dhPk rk (rnd ts1 32) (rnd ts2 32)]
  exact ⟨tdh, tprk, trk2, tcks⟩

structure ChainMeta where
  ts : Nat
  pk_id : Nat
  ck_id : Nat
  index : UInt32
  rIdx : Nat
  deriving DecidableEq, Repr

/-- DAG node IDs and ratchet counters describing one of the 24 clean local `TRState`s. -/
structure StateMeta where
  isBob : Bool
  rk_id : Nat
  dhs_ts : Nat
  sk_id : Nat
  pk_id : Nat
  cks_id : Nat
  ns : UInt32
  pn : UInt32
  rIdx : Nat
  chains : List ChainMeta
  deriving DecidableEq, Repr

def stepSendMeta (m : StateMeta) (j : Nat) : StateMeta :=
  { m with cks_id := (getSendRow j).nck_id, ns := m.ns + 1 }

def stepRecvMeta (mR mS : StateMeta) (j m : Nat) : StateMeta :=
  let nsk := recvSkId m
  let cmNew : ChainMeta := ⟨mS.dhs_ts, mS.pk_id, (getSendRow j).nck_id, 1, mR.rIdx + 2⟩
  { isBob := mR.isBob, rk_id := nsk + 4, dhs_ts := recvDhsTs m, sk_id := nsk, pk_id := nsk + 1,
    cks_id := nsk + 6, ns := 0, pn := if mR.ns = 0 then 0 else mR.ns - 1, rIdx := mR.rIdx + 2,
    chains := (mR.chains ++ [cmNew]).drop ((mR.chains.length + 1) - maxReceiverChains) }

def meta0 : StateMeta := ⟨false, 93, 24, 67, 69, 95, 0, 0, 1, [⟨10, 29, 85, 0, 1⟩]⟩
def meta1 : StateMeta := stepSendMeta meta0 0
def meta2 : StateMeta := stepSendMeta meta1 1
def meta3 : StateMeta := ⟨true, 160, 45, 156, 157, 162, 0, 0, 2, [⟨24, 69, 125, 2, 2⟩]⟩

def hrConfigMeta : Nat → StateMeta × StateMeta
  | 0 => (meta3, meta2)
  | H + 1 =>
    let (mS, mR) := hrConfigMeta H
    (stepRecvMeta mR mS (2 + H) (1 + H), stepSendMeta mS (2 + H))

def hrMetas (H : Nat) : List StateMeta :=
  let (mS, mR) := hrConfigMeta H
  [stepSendMeta mS (2 + H), stepRecvMeta mR mS (2 + H) (1 + H)]

def stateMetas : List StateMeta :=
  [meta0, meta1, meta2, meta3] ++ (List.range 10).flatMap hrMetas

def getStateMeta (i : Nat) : StateMeta := stateMetas.getD i meta0

def hrStepCheck (H : Nat) : Bool :=
  let (mS, mR) := hrConfigMeta H
  let j := 2 + H
  let m := 1 + H
  let r := getSendRow j
  let nsk := recvSkId m
  let curLen := 55 + 14 * H
  (r.pk_id == mS.pk_id) &&
  (r.myIk_id == (if mS.isBob then 31 else 30)) &&
  (r.peerIk_id == (if mS.isBob then 30 else 31)) &&
  (r.old_cks_id == mS.cks_id) &&
  (r.ctr == mS.ns) &&
  (r.prev == mS.pn) &&
  (r.salt_id == honestSaltIds.getD (3 + H) 0) &&
  (sendPtTs j == curLen) &&
  (recvDhsTs m == curLen + 7) &&
  decide (nsk + 1 < dagSize) &&
  isRandOp (dagOp nsk) (curLen + 7) 32 &&
  isDhPkOp (dagOp (nsk + 1)) nsk &&
  checkCreateChain mS.rk_id mS.sk_id mS.pk_id mS.dhs_ts nsk (nsk + 1) (curLen + 7)
    (nsk + 2) (nsk + 3) (nsk + 4) (nsk + 5) (nsk + 6) &&
  mR.chains.all (fun cm => decide (cm.ts < mS.dhs_ts))

theorem all_hr_steps_ok : (List.range 10).all hrStepCheck = true := by
  decide +kernel

theorem all_stateMetas_chains_ok :
    stateMetas.all (fun m => !m.chains.isEmpty && m.chains.all (fun cm => decide (1 ≤ cm.rIdx))) = true := by
  decide +kernel

def ChainRel (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List Bytes)
    (c : RecvChain) (cm : ChainMeta) : Prop :=
  c.ratchetKey = dhPk (rnd cm.ts 32) ∧
  c.index = cm.index ∧
  c.rIdx = cm.rIdx ∧
  TermAt dagSize dagOp dagBytes S g pts c.ratchetKey cm.pk_id ∧
  TermAt dagSize dagOp dagBytes S g pts c.chainKey cm.ck_id

/-- Relates a clean local `TRState` `ls` (via its coin-erased counterpart `ls₀`) to `StateMeta` `m`
with `TermAt` witnesses for all ratchet roots and `SafeMemo` on `spqr`. -/
structure StateWitness (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List Bytes)
    (ls ls₀ : DY.PersistentLocalState.LocalState TRState) (m : StateMeta) : Prop where
  hpart : ls.participant = (if m.isBob then "bob" else "alice")
  hpart0 : ls₀.participant = (if m.isBob then "bob" else "alice")
  hdr : ls.state.toDRState = ls₀.state.toDRState
  hinit : ls₀.state.initiator = !m.isBob
  hpeer : ls₀.state.peer = (if m.isBob then "alice" else "bob")
  hns : ls₀.state.ns = m.ns
  hpn : ls₀.state.pn = m.pn
  hrIdx : ls₀.state.rIdx = m.rIdx
  hdhs_eq : ls₀.state.dhs = rnd m.dhs_ts 32
  spqr_sm : SafeMemo dagSize dagOp dagBytes S g pts ls.state.spqr
  t_myIk : TermAt dagSize dagOp dagBytes S g pts ls₀.state.myIk (if m.isBob then 31 else 30)
  t_peerIk : TermAt dagSize dagOp dagBytes S g pts ls₀.state.peerIk (if m.isBob then 30 else 31)
  t_rk : TermAt dagSize dagOp dagBytes S g pts ls₀.state.rk m.rk_id
  t_dhs : TermAt dagSize dagOp dagBytes S g pts ls₀.state.dhs m.sk_id
  t_pk : TermAt dagSize dagOp dagBytes S g pts (dhPk ls₀.state.dhs) m.pk_id
  t_cks : TermAt dagSize dagOp dagBytes S g pts ls₀.state.cks m.cks_id
  t_sid : TermAt dagSize dagOp dagBytes S g pts ls₀.state.sid 88
  hchains : List.Forall₂ (ChainRel S g pts) ls₀.state.recv m.chains

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction h with
  | nil => cases hx
  | cons hr _ ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨y, hy, hry⟩ := ih hx'
      exact ⟨y, List.mem_cons_of_mem _ hy, hry⟩

private theorem forall₂_getLast {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (hne : ys ≠ []) :
    ∃ x y, xs.getLast? = some x ∧ y ∈ ys ∧ R x y := by
  induction h with
  | nil => exact absurd rfl hne
  | @cons a b _ _ hr hrest ih =>
    cases hrest with
    | nil => exact ⟨a, b, rfl, List.mem_cons_self, hr⟩
    | cons _ _ =>
      obtain ⟨x, y, hlast, hy, hxy⟩ := ih (by simp)
      exact ⟨x, y, hlast, List.mem_cons_of_mem _ hy, hxy⟩

theorem StateWitness.safeMemo2 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {ls ls₀ : DY.PersistentLocalState.LocalState TRState} {m : StateMeta}
    (sw : StateWitness S g pts ls ls₀ m)
    (hm_ok : (!m.chains.isEmpty && m.chains.all (fun cm => decide (1 ≤ cm.rIdx))) = true) :
    SafeMemo2 S g pts (DY.Comparse.serialize ls) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, decide_eq_true_eq] at hm_ok
  obtain ⟨hne, hall_rIdx⟩ := hm_ok
  obtain ⟨cLast, cmLast, hlast, hcm_mem, hcRel⟩ := forall₂_getLast sw.hchains hne
  have hp_party : ls₀.participant = "alice" ∨ ls₀.participant = "bob" := by
    rw [sw.hpart0]; cases m.isBob <;> simp
  have hp_peer : ls₀.state.peer = "alice" ∨ ls₀.state.peer = "bob" := by
    rw [sw.hpeer]; cases m.isBob <;> simp
  refine safeMemo2_trState_of_dr (sw.hpart.trans sw.hpart0.symm) sw.hdr hp_party hp_peer sw.spqr_sm
    ?_ ?_ hlast (hcRel.2.2.1 ▸ hall_rIdx cmLast hcm_mem)
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · exact sw.t_myIk.safeMemo
    · exact sw.t_peerIk.safeMemo
    · exact sw.t_rk.safeMemo
    · exact sw.t_dhs.safeMemo
    · exact sw.t_cks.safeMemo
    · exact sw.t_sid.safeMemo
  · intro c hc
    obtain ⟨cm, _, hcr⟩ := forall₂_mem_left sw.hchains hc
    exact ⟨hcr.2.2.2.1.safeMemo, hcr.2.2.2.2.safeMemo⟩

theorem stateWitness_send {cls : Nat → Nat} {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {me : Participant} {sSt sSt₀ : TRState} {m : StateMeta} {j curLen : Nat}
    (sw : StateWitness S g pts ⟨me, sSt⟩ ⟨me, sSt₀⟩ m)
    (hs : SendStepOut (cls := cls) S g pts sSt j)
    (hcur : sendPtTs j = curLen) :
    StateWitness S g pts ⟨me, sendStOf sSt (cls j) curLen⟩ ⟨me, sendStOf sSt₀ 0 curLen⟩
      (stepSendMeta m j) := by
  have hdr' : (sendStOf sSt (cls j) curLen).toDRState = (sendStOf sSt₀ 0 curLen).toDRState :=
    encSt_toDRState sw.hdr
  have hcks_eq : (sendStOf sSt (cls j) curLen).cks = (sendStOf sSt₀ 0 curLen).cks :=
    congrArg (·.cks) hdr'
  refine ⟨sw.hpart, sw.hpart0, hdr', sw.hinit, sw.hpeer, ?_, sw.hpn, sw.hrIdx, sw.hdhs_eq,
    hcur ▸ hs.spqr_sm, sw.t_myIk, sw.t_peerIk, sw.t_rk, sw.t_dhs, sw.t_pk, ?_, sw.t_sid, sw.hchains⟩
  · change sSt₀.ns + 1 = m.ns + 1; rw [sw.hns]
  · have t1 : TermAt dagSize dagOp dagBytes S g pts (sendStOf sSt (cls j) curLen).cks
        (getSendRow j).nck_id := hcur ▸ hs.cks_next
    exact hcks_eq ▸ t1

theorem forall₂_append_one {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    {a : α} {b : β} (h : List.Forall₂ R xs ys) (hab : R a b) :
    List.Forall₂ R (xs ++ [a]) (ys ++ [b]) := by
  induction h with
  | nil => exact List.Forall₂.cons hab List.Forall₂.nil
  | cons hr _ ih => exact List.Forall₂.cons hr ih

private theorem forall₂_drop {α β : Type} {R : α → β → Prop} :
    ∀ (k : Nat) {xs : List α} {ys : List β},
      List.Forall₂ R xs ys → List.Forall₂ R (xs.drop k) (ys.drop k)
  | 0, _, _, h => h
  | _ + 1, _, _, List.Forall₂.nil => List.Forall₂.nil
  | k + 1, _ :: _, _ :: _, List.Forall₂.cons _ h => forall₂_drop k h

private theorem setRecvChain_drop_append {chains : List RecvChain} {c c' : RecvChain} {k : Nat}
    (hne : ∀ y ∈ chains, y.ratchetKey ≠ c'.ratchetKey)
    (heq : c.ratchetKey = c'.ratchetKey) :
    setRecvChain ((chains ++ [c]).drop k) c' = (chains ++ [c']).drop k := by
  unfold setRecvChain
  rw [List.map_drop, List.map_append]
  have h1 : chains.map (fun y => if (y.ratchetKey == c'.ratchetKey) then c' else y) = chains := by
    induction chains with
    | nil => rfl
    | cons y ys ih =>
      have hy : (y.ratchetKey == c'.ratchetKey) = false :=
        beq_false_of_ne (hne y List.mem_cons_self)
      simp only [List.map_cons, hy, Bool.false_eq_true, ↓reduceIte]
      exact congrArg (y :: ·) (ih (fun z hz => hne z (List.mem_cons_of_mem _ hz)))
  have h2 : [c].map (fun y => if (y.ratchetKey == c'.ratchetKey) then c' else y) = [c'] := by
    simp [heq]
  rw [h1, h2]

theorem stateWitness_recv {cls : Nat → Nat} {S : OpaqueSymbolSemantics} {g : Ghost}
    {vis : List VisEntry} {pts : List Bytes} {nSends nRecvs H : Nat}
    {peer : Participant} {rSt rSt₀ sSt sSt₀ : TRState} {mR mS : StateMeta}
    (hp : PrefixPinned cls S g vis nSends nRecvs)
    (hH : H < 10)
    (hm_lt : 1 + H < nRecvs)
    (hcfg : hrConfigMeta H = (mS, mR))
    (swR : StateWitness S g pts ⟨peer, rSt⟩ ⟨peer, rSt₀⟩ mR)
    (swS : StateWitness S g pts ⟨if mS.isBob then "bob" else "alice", sSt⟩
            ⟨if mS.isBob then "bob" else "alice", sSt₀⟩ mS)
    (hsync : createChain rSt₀.rk (dhPk sSt₀.dhs) rSt₀.dhs = (sSt₀.rk, sSt₀.cks))
    (hs : SendStepOut (cls := cls) S g pts sSt (2 + H)) :
    let curLen := 55 + 14 * H
    let rOut := recvStOf rSt sSt (cls (2 + H)) curLen
    let rOut₀ := recvStOf rSt₀ sSt₀ 0 curLen
    StateWitness S g pts ⟨peer, rOut⟩ ⟨peer, rOut₀⟩ (stepRecvMeta mR mS (2 + H) (1 + H)) ∧
    createChain (sendStOf sSt₀ 0 curLen).rk (dhPk rOut₀.dhs) (sendStOf sSt₀ 0 curLen).dhs =
      (rOut₀.rk, rOut₀.cks) := by
  have hchk := List.all_eq_true.mp all_hr_steps_ok H (List.mem_range.mpr hH)
  unfold hrStepCheck at hchk
  rw [hcfg] at hchk
  dsimp only at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hpt_ts⟩, hdhs_ts⟩,
    hnpk_lt⟩, hnsk_op⟩, hnpk_op⟩, hcc_ok⟩, hchains_ts⟩ := hchk
  set curLen := 55 + 14 * H
  set m := 1 + H
  set nsk := recvSkId m
  have hdhs_s : sSt.dhs = sSt₀.dhs := congrArg (·.dhs) swS.hdr
  have hdr_out : (recvStOf rSt sSt (cls (2 + H)) curLen).toDRState =
      (recvStOf rSt₀ sSt₀ 0 curLen).toDRState := by
    unfold recvStOf; rw [hdhs_s]; exact decSt0_toDRState swR.hdr
  have hpqm_sm : SafeMemo dagSize dagOp dagBytes S g pts (pqMsgOf sSt (cls (2 + H)) curLen) :=
    (hpt_ts ▸ hs.pqMsg).safeMemo
  have hspqr_out : SafeMemo dagSize dagOp dagBytes S g pts
      (recvStOf rSt sSt (cls (2 + H)) curLen).spqr :=
    memoOK_spqrRecvState_pack swR.spqr_sm hpqm_sm
  have hpin_dhs : g.σ (curLen + 7) 32 = dagBytes nsk := hdhs_ts ▸ hp.recv_dhs m hm_lt
  have hnsk_lt : nsk < dagSize := by omega
  have t_nsk : TermAt dagSize dagOp dagBytes S g pts (rnd (curLen + 7) 32) nsk :=
    termAt_rand_b hpin_dhs (Bool.and_eq_true_iff.mpr ⟨decide_eq_true hnsk_lt, hnsk_op⟩)
  have t_npk : TermAt dagSize dagOp dagBytes S g pts (dhPk (rnd (curLen + 7) 32)) (nsk + 1) :=
    termAt_dhPk_b (Bool.and_eq_true_iff.mpr ⟨decide_eq_true hnpk_lt, hnpk_op⟩) t_nsk
  have t_skS : TermAt dagSize dagOp dagBytes S g pts (rnd mS.dhs_ts 32) mS.sk_id :=
    swS.hdhs_eq ▸ swS.t_dhs
  have t_pkS : TermAt dagSize dagOp dagBytes S g pts (dhPk (rnd mS.dhs_ts 32)) mS.pk_id :=
    swS.hdhs_eq ▸ swS.t_pk
  obtain ⟨_, _, t_rk2, t_cks2⟩ :=
    termAt_createChain_dhPk hcc_ok swS.t_rk t_skS t_pkS t_nsk t_npk
  have hrk1_eq : (createChain rSt₀.rk (dhPk sSt₀.dhs) rSt₀.dhs).1 = sSt₀.rk :=
    congrArg Prod.fst hsync
  have hckr_eq : (createChain rSt₀.rk (dhPk sSt₀.dhs) rSt₀.dhs).2 = sSt₀.cks :=
    congrArg Prod.snd hsync
  have hsync_next : createChain (sendStOf sSt₀ 0 curLen).rk
      (dhPk (recvStOf rSt₀ sSt₀ 0 curLen).dhs) (sendStOf sSt₀ 0 curLen).dhs =
      ((recvStOf rSt₀ sSt₀ 0 curLen).rk, (recvStOf rSt₀ sSt₀ 0 curLen).cks) := by
    show createChain sSt₀.rk (dhPk (rnd (curLen + 7) 32)) sSt₀.dhs =
      (createChain (createChain rSt₀.rk (dhPk sSt₀.dhs) rSt₀.dhs).1
        (dhPk sSt₀.dhs) (rnd (curLen + 7) 32))
    rw [hrk1_eq, createChain_comm sSt₀.rk (rnd (curLen + 7) 32) sSt₀.dhs]
  refine ⟨?_, hsync_next⟩
  have hne_chains : ∀ y ∈ rSt₀.recv, y.ratchetKey ≠ dhPk sSt₀.dhs := by
    intro y hy
    obtain ⟨cm, hcm_mem, hcr⟩ := forall₂_mem_left swR.hchains hy
    rw [hcr.1, swS.hdhs_eq]
    exact dhPk_rnd_ne (Nat.ne_of_lt (hchains_ts cm hcm_mem))
  have hlen_chains : rSt₀.recv.length = mR.chains.length := swR.hchains.length_eq
  let rcInit : RecvChain :=
    { ratchetKey := dhPk sSt₀.dhs,
      chainKey := (createChain rSt₀.rk (dhPk sSt₀.dhs) rSt₀.dhs).2,
      index := 0, rIdx := rSt₀.rIdx + 2 }
  let rcUpd : RecvChain :=
    { ratchetKey := dhPk sSt₀.dhs,
      chainKey := (kdfCk (createChain rSt₀.rk (dhPk sSt₀.dhs) rSt₀.dhs).2).1,
      index := 1, rIdx := rSt₀.rIdx + 2 }
  have hrecv_list : (recvStOf rSt₀ sSt₀ 0 curLen).recv =
      (rSt₀.recv ++ [rcUpd]).drop ((rSt₀.recv.length + 1) - maxReceiverChains) := by
    unfold recvStOf decSt0 ratchetState
    dsimp only
    exact setRecvChain_drop_append (c := rcInit) (c' := rcUpd) hne_chains rfl
  have hck_new : TermAt dagSize dagOp dagBytes S g pts
      (kdfCk (createChain rSt₀.rk (dhPk sSt₀.dhs) rSt₀.dhs).2).1
      (getSendRow (2 + H)).nck_id := by
    rw [hckr_eq]
    have hcks_s : (sendStOf sSt (cls (2 + H)) curLen).cks = (kdfCk sSt₀.cks).1 := by
      have h := congrArg (·.cks) (encSt_toDRState swS.hdr (c₁ := rnd (curLen + 1) (cls (2 + H)))
        (c₂ := rnd (curLen + 1) 0))
      exact h
    exact hcks_s ▸ (hpt_ts ▸ hs.cks_next)
  have hcmNew : ChainRel S g pts rcUpd
      { ts := mS.dhs_ts, pk_id := mS.pk_id, ck_id := (getSendRow (2 + H)).nck_id,
        index := 1, rIdx := mR.rIdx + 2 } :=
    ⟨congrArg dhPk swS.hdhs_eq, rfl, congrArg (· + 2) swR.hrIdx, swS.t_pk, hck_new⟩
  refine ⟨swR.hpart, swR.hpart0, hdr_out, swR.hinit, swR.hpeer, rfl, ?_, ?_, ?_,
    hspqr_out, swR.t_myIk, swR.t_peerIk, ?_, t_nsk, t_npk, ?_, swR.t_sid, ?_⟩
  · show (if rSt₀.ns = 0 then 0 else rSt₀.ns - 1) = (if mR.ns = 0 then 0 else mR.ns - 1)
    rw [swR.hns]
  · show rSt₀.rIdx + 2 = mR.rIdx + 2; rw [swR.hrIdx]
  · show rnd (curLen + 7) 32 = rnd (recvDhsTs m) 32; rw [hdhs_ts]
  · show TermAt dagSize dagOp dagBytes S g pts
      (createChain (createChain rSt₀.rk (dhPk sSt₀.dhs) rSt₀.dhs).1
        (dhPk sSt₀.dhs) (rnd (curLen + 7) 32)).1 (nsk + 4)
    rw [hrk1_eq, swS.hdhs_eq]; exact t_rk2
  · show TermAt dagSize dagOp dagBytes S g pts
      (createChain (createChain rSt₀.rk (dhPk sSt₀.dhs) rSt₀.dhs).1
        (dhPk sSt₀.dhs) (rnd (curLen + 7) 32)).2 (nsk + 6)
    rw [hrk1_eq, swS.hdhs_eq]; exact t_cks2
  · rw [hrecv_list, hlen_chains]
    exact forall₂_drop _ (forall₂_append_one swR.hchains hcmNew)

def StateTripleList (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List Bytes)
    (l l₀ : List (DY.PersistentLocalState.LocalState TRState)) (ms : List StateMeta) : Prop :=
  l.length = ms.length ∧ l₀.length = ms.length ∧
  ∀ i, i < ms.length →
    StateWitness S g pts
      (l.getD i ⟨"alice", stA0⟩) (l₀.getD i ⟨"alice", stA0⟩) (ms.getD i meta0)

theorem stateTripleList_append {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {l₁ l₂ l₀₁ l₀₂ : List (DY.PersistentLocalState.LocalState TRState)}
    {ms₁ ms₂ : List StateMeta}
    (h₁ : StateTripleList S g pts l₁ l₀₁ ms₁)
    (h₂ : StateTripleList S g pts l₂ l₀₂ ms₂) :
    StateTripleList S g pts (l₁ ++ l₂) (l₀₁ ++ l₀₂) (ms₁ ++ ms₂) := by
  obtain ⟨hl1, hl01, hw1⟩ := h₁
  obtain ⟨hl2, hl02, hw2⟩ := h₂
  refine ⟨by rw [List.length_append, List.length_append, hl1, hl2],
          by rw [List.length_append, List.length_append, hl01, hl02], fun i hi => ?_⟩
  rw [List.length_append] at hi
  by_cases hlt : i < ms₁.length
  · simp only [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (hl1 ▸ hlt), List.getElem?_append_left (hl01 ▸ hlt),
      List.getElem?_append_left hlt]
    exact hw1 i hlt
  · have hge : ms₁.length ≤ i := by omega
    have hi2 : i - ms₁.length < ms₂.length := by omega
    simp only [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (hl1 ▸ hge), List.getElem?_append_right (hl01 ▸ hge),
      List.getElem?_append_right hge, hl1, hl01]
    exact hw2 (i - ms₁.length) hi2

theorem mem_pts_of_lt {cls : Nat → Nat} {S : OpaqueSymbolSemantics} {g : Ghost}
    {vis : List VisEntry} {nSends nRecvs j : Nat}
    (hp : PrefixPinned cls S g vis nSends nRecvs) (hj : j < nSends) :
    randTerm (sendPtTs j) 32 ∈ plaintextTerms vis := by
  rw [hp.vis_pts]
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

theorem walk_calls_0_to_2 {cls : Nat → Nat} {S : OpaqueSymbolSemantics} {g : Ghost}
    {vis : List VisEntry} {nSends nRecvs : Nat}
    (hp : PrefixPinned cls S g vis nSends nRecvs)
    (hcls : ValidCoinLens cls)
    (h2 : 2 ≤ nSends) :
    let pts := plaintextTerms vis
    StateWitness S g pts ⟨"alice", stA0⟩ ⟨"alice", stA0⟩ meta0 ∧
    StateWitness S g pts ⟨"alice", stA1c cls⟩ ⟨"alice", stA1c cls0⟩ meta1 ∧
    StateWitness S g pts ⟨"alice", stA2c cls⟩ ⟨"alice", stA2c cls0⟩ meta2 ∧
    SendStepOut (cls := cls) S g pts stA0 0 ∧
    SendStepOut (cls := cls) S g pts (stA1c cls) 1 ∧
    TermAt dagSize dagOp dagBytes S g pts seedB0 104 ∧
    List.Forall₂ (TermAt dagSize dagOp dagBytes S g pts)
      ((allSalts13 cls).take 3) (honestSaltIds.take 3) := by
  set pts := plaintextTerms vis
  have hs := handshake_termAt (pts := pts) hp.base
  have hspqr0 : SafeMemo dagSize dagOp dagBytes S g pts stA0.spqr :=
    safeMemo_spqrInit hs.pqr.safeMemo (safeMemo_lit_short (by decide))
  have sw0 : StateWitness S g pts ⟨"alice", stA0⟩ ⟨"alice", stA0⟩ meta0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hspqr0,
     hs.ik0s, hs.ik1s, hs.stA0_rk, hs.t_dhsA, hs.pk4, hs.stA0_cks, hs.stA0_sid,
     List.Forall₂.cons ⟨rfl, rfl, rfl, hs.pk2, hs.ck_init⟩ List.Forall₂.nil⟩
  have out0 : SendStepOut (cls := cls) S g pts stA0 0 :=
    send_step_at hp hcls (by omega) (by decide) (mem_pts_of_lt hp (by omega))
      rfl sw0.spqr_sm sw0.t_pk sw0.t_myIk sw0.t_peerIk sw0.t_cks rfl rfl
  have sw1 : StateWitness S g pts ⟨"alice", stA1c cls⟩ ⟨"alice", stA1c cls0⟩ meta1 :=
    stateWitness_send sw0 out0 rfl
  have out1 : SendStepOut (cls := cls) S g pts (stA1c cls) 1 :=
    send_step_at hp hcls (by omega) (by decide) (mem_pts_of_lt hp (by omega))
      rfl sw1.spqr_sm (by rw [congrArg (·.dhs) sw1.hdr]; exact sw1.t_pk)
      (by rw [congrArg (·.myIk) sw1.hdr]; exact sw1.t_myIk)
      (by rw [congrArg (·.peerIk) sw1.hdr]; exact sw1.t_peerIk)
      (by rw [congrArg (·.cks) sw1.hdr]; exact sw1.t_cks)
      (congrArg (·.ns) sw1.hdr) (congrArg (·.pn) sw1.hdr)
  have sw2 : StateWitness S g pts ⟨"alice", stA2c cls⟩ ⟨"alice", stA2c cls0⟩ meta2 :=
    stateWitness_send sw1 out1 rfl
  have t_seedB0 : TermAt dagSize dagOp dagBytes S g pts seedB0 104 := seedB0_eq ▸ out0.seed
  have t_zero : TermAt dagSize dagOp dagBytes S g pts DY.Spqr.zeroKey 8 :=
    termAt_lit_b (id := 8) (by decide +kernel)
  have hsalts : List.Forall₂ (TermAt dagSize dagOp dagBytes S g pts)
      ((allSalts13 cls).take 3) (honestSaltIds.take 3) :=
    List.Forall₂.cons t_zero (List.Forall₂.cons out0.pqKey (List.Forall₂.cons out1.pqKey List.Forall₂.nil))
  exact ⟨sw0, sw1, sw2, out0, out1, t_seedB0, hsalts⟩

theorem stateWitness_st3 {cls : Nat → Nat} {S : OpaqueSymbolSemantics} {g : Ghost}
    {vis : List VisEntry} {nSends nRecvs : Nat}
    (hp : PrefixPinned cls S g vis nSends nRecvs) (h1 : 1 ≤ nRecvs)
    (sw2 : StateWitness S g (plaintextTerms vis) ⟨"alice", stA2c cls⟩ ⟨"alice", stA2c cls0⟩ meta2)
    (out1 : SendStepOut (cls := cls) S g (plaintextTerms vis) (stA1c cls) 1) :
    let pts := plaintextTerms vis
    StateWitness S g pts ⟨"bob", stB1c cls⟩ ⟨"bob", stB1c cls0⟩ meta3 ∧
    createChain (stA2c cls0).rk (dhPk (stB1c cls0).dhs) (stA2c cls0).dhs =
      ((stB1c cls0).rk, (stB1c cls0).cks) := by
  set pts := plaintextTerms vis
  have hs := handshake_termAt (pts := pts) hp.base
  have t_nsk : TermAt dagSize dagOp dagBytes S g pts dhsB1 156 :=
    termAt_rand_b (hp.recv_dhs 0 h1) (by decide +kernel)
  have t_npk : TermAt dagSize dagOp dagBytes S g pts (dhPk dhsB1) 157 :=
    termAt_dhPk_b (by decide +kernel) t_nsk
  have hcc1 : createChain keys1.rk (dhPk dhsA) spkB = (stA0.rk, stA0.cks) :=
    createChain_comm keys1.rk dhsA spkB
  obtain ⟨_, _, t_rkB, t_cksB⟩ :=
    termAt_createChain_dhPk (rk_id := 93) (s1 := 67) (pk1 := 69) (ts1 := 24)
      (s2 := 156) (pk2 := 157) (ts2 := 45)
      (dh_id := 158) (prk_id := 159) (rk2_id := 160) (c2_id := 161) (cks_id := 162)
      (by decide +kernel) hs.stA0_rk hs.t_dhsA hs.pk4 t_nsk t_npk
  have hrk_eq : (stB1c cls0).rk = (createChain stA0.rk (dhPk dhsA) dhsB1).1 := by
    show (createChain (createChain keys1.rk (dhPk dhsA) spkB).1 (dhPk dhsA) dhsB1).1 = _
    rw [hcc1]
  have hcks_eq : (stB1c cls0).cks = (createChain stA0.rk (dhPk dhsA) dhsB1).2 := by
    show (createChain (createChain keys1.rk (dhPk dhsA) spkB).1 (dhPk dhsA) dhsB1).2 = _
    rw [hcc1]
  have hsid_eq : (stB1c cls0).sid = stA0.sid := by
    show DY.Concat.concat (DY.X25519.normalizeX25519Key (dhPk dhsA)) keys1.rk = _
    rw [norm_dhPk dhsA]; rfl
  have hcB''_ck : cB''.chainKey = (stA2c cls0).cks := by
    show (kdfCk (kdfCk (createChain keys1.rk (dhPk dhsA) spkB).2).1).1 = _; rw [hcc1]; rfl
  have hspqr_b1 : SafeMemo dagSize dagOp dagBytes S g pts (stB1c cls).spqr :=
    memoOK_spqrRecvState_pack
      (safeMemo_spqrInit hs.pqr.safeMemo (safeMemo_lit_short (by decide))) out1.pqMsg.safeMemo
  have hsync0 : createChain (stA2c cls0).rk (dhPk (stB1c cls0).dhs) (stA2c cls0).dhs =
      ((stB1c cls0).rk, (stB1c cls0).cks) := by
    rw [hrk_eq, hcks_eq]; exact createChain_comm stA0.rk dhsB1 dhsA
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hspqr_b1,
    hs.ik1s, hs.ik0s, hrk_eq ▸ t_rkB, t_nsk, t_npk, hcks_eq ▸ t_cksB, hsid_eq ▸ hs.stA0_sid,
    List.Forall₂.cons ⟨rfl, rfl, rfl, hs.pk4, hcB''_ck ▸ sw2.t_cks⟩ List.Forall₂.nil⟩, hsync0⟩

theorem walk_hr_send {cls : Nat → Nat} {S : OpaqueSymbolSemantics} {g : Ghost}
    {vis : List VisEntry} {nSends nRecvs H : Nat}
    {me : Participant} {sSt sSt₀ : TRState} {mS mR : StateMeta}
    (hp : PrefixPinned cls S g vis nSends nRecvs) (hcls : ValidCoinLens cls)
    (hH : H < 10) (hj_lt : 2 + H < nSends)
    (hcfg_s : ∃ peer rSt, hrConfig cls H = (me, peer, sSt, rSt))
    (hcfg_m : hrConfigMeta H = (mS, mR))
    (swS : StateWitness S g (plaintextTerms vis) ⟨me, sSt⟩ ⟨me, sSt₀⟩ mS) :
    SendStepOut (cls := cls) S g (plaintextTerms vis) sSt (2 + H) ∧
    StateWitness S g (plaintextTerms vis)
      ⟨me, sendStOf sSt (cls (2 + H)) (55 + 14 * H)⟩
      ⟨me, sendStOf sSt₀ 0 (55 + 14 * H)⟩ (stepSendMeta mS (2 + H)) := by
  have hchk := List.all_eq_true.mp all_hr_steps_ok H (List.mem_range.mpr hH)
  unfold hrStepCheck at hchk; rw [hcfg_m] at hchk; dsimp only at hchk
  simp only [Bool.and_eq_true, beq_iff_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpk, hmy⟩, hpeer⟩, hcks⟩, hctr⟩, hprev⟩, _⟩, hpt_ts⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hchk
  obtain ⟨peer, rSt, hrc⟩ := hcfg_s
  have hclean : cleanSendMsg cls (2 + H) = sendMsgOf sSt (cls (2 + H)) (sendPtTs (2 + H)) := by
    unfold cleanSendMsg
    have h0 : ¬ (2 + H = 0) := by omega
    have h1 : ¬ (2 + H = 1) := by omega
    have hsub : 2 + H - 2 = H := by omega
    simp only [h0, h1, ↓reduceIte, hsub, hrc, hpt_ts]
  have out := send_step_at hp hcls hj_lt (by omega) (mem_pts_of_lt hp hj_lt) hclean swS.spqr_sm
    (by rw [congrArg (·.dhs) swS.hdr, hpk]; exact swS.t_pk)
    (by rw [congrArg (·.myIk) swS.hdr, hmy]; exact swS.t_myIk)
    (by rw [congrArg (·.peerIk) swS.hdr, hpeer]; exact swS.t_peerIk)
    (by rw [congrArg (·.cks) swS.hdr, hcks]; exact swS.t_cks)
    (by rw [congrArg (·.ns) swS.hdr, swS.hns, hctr])
    (by rw [congrArg (·.pn) swS.hdr, swS.hpn, hprev])
  exact ⟨out, stateWitness_send swS out hpt_ts⟩

def initStates4 (cls : Nat → Nat) : List (DY.PersistentLocalState.LocalState TRState) :=
  [⟨"alice", stA0⟩, ⟨"alice", stA1c cls⟩, ⟨"alice", stA2c cls⟩, ⟨"bob", stB1c cls⟩]

def prefixSaltsOf (cls : Nat → Nat) (H : Nat) : List Bytes :=
  [DY.Spqr.zeroKey, pqKey0 cls, pqKey1 cls] ++
    (List.range H).map fun h =>
      let (_, _, sSt_h, _) := hrConfig cls h
      pqKeyOf sSt_h (cls (2 + h)) (55 + 14 * h)

/-- Propagates `StateTripleList`, `honestSalts` `TermAt` witnesses, `SendStepOut` for prior sends,
and synchronized sender/receiver `StateWitness`es across `H` ping-pong half-rounds. -/
theorem walk_hr_prefix {cls : Nat → Nat} {S : OpaqueSymbolSemantics} {g : Ghost}
    {vis : List VisEntry} {nSends nRecvs : Nat}
    (hp : PrefixPinned cls S g vis nSends nRecvs) (hcls : ValidCoinLens cls) :
    ∀ H ≤ 10, 2 + H ≤ nSends → 1 + H ≤ nRecvs →
      let pts := plaintextTerms vis
      let (me, peer, sSt, rSt) := hrConfig cls H
      let (_, _, sSt₀, rSt₀) := hrConfig cls0 H
      let (mS, mR) := hrConfigMeta H
      StateTripleList S g pts
        (initStates4 cls ++ (List.range H).flatMap (hrStates cls))
        (initStates4 cls0 ++ (List.range H).flatMap (hrStates cls0))
        ([meta0, meta1, meta2, meta3] ++ (List.range H).flatMap hrMetas) ∧
      List.Forall₂ (TermAt dagSize dagOp dagBytes S g pts)
        (prefixSaltsOf cls H) (honestSaltIds.take (3 + H)) ∧
      (∀ j < 2 + H, ∃ st,
        cleanSendMsg cls j = sendMsgOf st (cls j) (sendPtTs j) ∧
        pqKeyOf st (cls j) (sendPtTs j) ∈ prefixSaltsOf cls H ∧
        SendStepOut (cls := cls) S g pts st j) ∧
      TermAt dagSize dagOp dagBytes S g pts seedB0 104 ∧
      StateWitness S g pts ⟨me, sSt⟩ ⟨me, sSt₀⟩ mS ∧
      StateWitness S g pts ⟨peer, rSt⟩ ⟨peer, rSt₀⟩ mR ∧
      createChain rSt₀.rk (dhPk sSt₀.dhs) rSt₀.dhs = (sSt₀.rk, sSt₀.cks)
  | 0, _, hS, hR => by
    obtain ⟨sw0, sw1, sw2, out0, out1, t_seed, hsalts3⟩ := walk_calls_0_to_2 hp hcls hS
    obtain ⟨sw3, hsync0⟩ := stateWitness_st3 hp hR sw2 out1
    refine ⟨?_, hsalts3, ?_, t_seed, sw3, sw2, hsync0⟩
    · simp only [List.range_zero, List.flatMap_nil, List.append_nil]
      refine ⟨rfl, rfl, fun i hi => ?_⟩
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by dsimp at hi; omega) with rfl | rfl | rfl | rfl
      · exact sw0
      · exact sw1
      · exact sw2
      · exact sw3
    · intro j hj
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · exact ⟨stA0, rfl, by simp [prefixSaltsOf, pqKey0, sendPtTs], out0⟩
      · exact ⟨stA1c cls, rfl, by simp [prefixSaltsOf, pqKey1, sendPtTs], out1⟩
  | H + 1, hle, hS, hR => by
    have ih := walk_hr_prefix hp hcls H (by omega) (by omega) (by omega)
    rcases hrc : hrConfig cls H with ⟨me, peer, sSt, rSt⟩
    rcases hrc0 : hrConfig cls0 H with ⟨me0, peer0, sSt₀, rSt₀⟩
    rcases hm : hrConfigMeta H with ⟨mS, mR⟩
    rw [hrc, hrc0, hm] at ih; dsimp only at ih
    obtain ⟨hsts, hsalts, hsends, t_seed, swS, swR, hsync⟩ := ih
    have ⟨hm_eq, hp_eq, _, _⟩ := hrConfig_toDRState cls H
    rw [hrc, hrc0] at hm_eq hp_eq; dsimp only at hm_eq hp_eq; subst hm_eq hp_eq
    obtain ⟨outS, swSendOut⟩ := walk_hr_send hp hcls (by omega) (by omega) ⟨peer, rSt, hrc⟩ hm swS
    have swS_norm : StateWitness S g (plaintextTerms vis)
        ⟨if mS.isBob then "bob" else "alice", sSt⟩
        ⟨if mS.isBob then "bob" else "alice", sSt₀⟩ mS := swS.hpart ▸ swS
    obtain ⟨swRecvOut, hsync_next⟩ :=
      stateWitness_recv hp (by omega) (by omega) hm swR swS_norm hsync outS
    have hchk := List.all_eq_true.mp all_hr_steps_ok H (List.mem_range.mpr (by omega))
    unfold hrStepCheck at hchk; rw [hm] at hchk; dsimp only at hchk
    simp only [Bool.and_eq_true, beq_iff_eq] at hchk
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, hsalt_id⟩, hpt_ts⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hchk
    have hps_succ : prefixSaltsOf cls (H + 1) =
        prefixSaltsOf cls H ++ [pqKeyOf sSt (cls (2 + H)) (55 + 14 * H)] := by
      unfold prefixSaltsOf
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, ← List.append_assoc]
      simp only [hrc]
    simp only [hrConfig, hrConfigMeta, hrc, hrc0, hm]
    refine ⟨?_, ?_, ?_, t_seed, swRecvOut, swSendOut, hsync_next⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_append, List.flatMap_append,
          ← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
      refine stateTripleList_append hsts ?_
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hrStates, hrMetas, hrc, hrc0, hm]
      refine ⟨rfl, rfl, fun i hi => ?_⟩
      rcases (show i = 0 ∨ i = 1 by dsimp at hi; omega) with rfl | rfl
      · exact swSendOut
      · exact swRecvOut
    · rw [hps_succ]
      have htake_succ : honestSaltIds.take (3 + (H + 1)) =
          honestSaltIds.take (3 + H) ++ [honestSaltIds.getD (3 + H) 0] := by
        rcases (show H = 0 ∨ H = 1 ∨ H = 2 ∨ H = 3 ∨ H = 4 ∨ H = 5 ∨ H = 6 ∨ H = 7 ∨ H = 8 ∨ H = 9 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      rw [htake_succ]
      exact forall₂_append_one hsalts (hsalt_id ▸ (hpt_ts ▸ outS.pqKey))
    · intro j hj
      by_cases hj_eq : j = 2 + H
      · subst hj_eq
        refine ⟨sSt, ?_, ?_, outS⟩
        · unfold cleanSendMsg
          have h0 : ¬ (2 + H = 0) := by omega
          have h1 : ¬ (2 + H = 1) := by omega
          have hsub : 2 + H - 2 = H := by omega
          simp only [h0, h1, ↓reduceIte, hsub, hrc, hpt_ts]
        · rw [hps_succ, hpt_ts]
          exact List.mem_append_right _ List.mem_cons_self
      · obtain ⟨st_j, hc_j, hm_j, out_j⟩ := hsends j (by omega)
        exact ⟨st_j, hc_j, hps_succ ▸ List.mem_append_left _ hm_j, out_j⟩

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk1
