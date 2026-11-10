/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins

/-!
# Certified DAG Walk: Single-Step Send and Coin-Length Independence

Proves `send_step_at`, which pins `pqKey` and `pqMsg` and establishes `TermAt` witnesses for every
derived key, wire message, and MAC of send step `j < 12`, and `allStates24_toDRState`, which shows
that `.participant` and `.toDRState` across all 24 clean states are independent of `cls`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalkSend

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

open DY (Bytes)
open DY.DiffieHellman (dhPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet
  (TRState litByte messageVersion hmac kdfCk trMsgKeys computeMac parseTrSignalMsg)
open DY.Libsignal.Composed.Refinement
  (OpaqueSymbolSemantics Ghost VisEntry randTerm litOf gamma' gamma)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compTag4)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (rnd encSt encMsg encSig parse_encMsg)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0 (evictedI0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.ShaMacLaws
  (gamma_hmacE gamma_computeMacE gamma_trMsgKeys_congr_prk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs (ValidCoinLens)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs
  (DagOp dagOpBytesOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagSize dagOp dagBytes)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagBuckets (dag_nodes_ok)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoCombinators
  (SafeMemo TermAt safeMemo_randTerm_zero)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTermAt
  (termAt_concat termAt_symEncPt termAt_trWire termAt_of_opaque safeMemo_spqrSend
   termAt_computeMac termAt_trMsgKeys)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrials
  (isKdfOp isConcatOp isTrunc8Op isLitOp wmkInfo_termAt)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace0 (decSt0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace
  (pqKeyOf pqMsgOf sendStOf sendMsgOf recvStOf hrConfig hrStates allStates24 cleanSendMsg)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins0
  (gamma_litOf encMsg_pins_pqKey_and_pqMsg)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPinsEv0
  (aliceBobAddrBytes sendPtTs sendPtBytes sendPtBytes_len_lt8 sendC32Id sendC64Id sendWmacId)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins (PrefixPinned)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk0
  (dag_bytes_ok isRandOp isSymEncPtOp isTrWireOp termAt_lit_b termAt_litOf_b
   termAt_rand_b termAt_kdf_b)

theorem spqrSend_shapes (S : OpaqueSymbolSemantics) (g : Ghost) (spqr coins : Bytes) :
    (gamma' evictedI0 S g (DY.Spqr.spqrSend spqr coins).2.1).shape =
      litOf (gamma evictedI0 S g (DY.Spqr.spqrSend spqr coins).2.1) ∧
    (gamma' evictedI0 S g (DY.Spqr.spqrSend spqr coins).2.2).shape =
      litOf (gamma evictedI0 S g (DY.Spqr.spqrSend spqr coins).2.2) := by
  unfold DY.Spqr.spqrSend; dsimp only
  split
  · constructor
    · unfold gamma gamma'
      dsimp only [DY.Spqr.spqrChainKey]
      rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrChainKey S)
        (DY.Libsignal.Composed.Refinement.concretizeAll evictedI0 S g)]
      rfl
    · unfold gamma gamma'
      rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrSendMsg S)
        (DY.Libsignal.Composed.Refinement.concretizeAll evictedI0 S g)]
      rfl
  · constructor
    · unfold gamma gamma'
      rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrSendKey S)
        (DY.Libsignal.Composed.Refinement.concretizeAll evictedI0 S g)]
      rfl
    · unfold gamma gamma'
      rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrSendMsg S)
        (DY.Libsignal.Composed.Refinement.concretizeAll evictedI0 S g)]
      rfl

structure SendRow where
  pk_id : Nat
  myIk_id : Nat
  peerIk_id : Nat
  ctr : UInt32
  prev : UInt32
  old_cks_id : Nat
  seed_id : Nat
  nck_id : Nat
  salt_id : Nat
  pq_id : Nat
  prk_id : Nat
  ckey_id : Nat
  mkey_id : Nat
  iv_id : Nat
  ct_id : Nat
  wire_id : Nat
  mi_r_id : Nat
  mi_id : Nat
  fmac_id : Nat
  mac_id : Nat

def sendRows : List SendRow := [
  ⟨69, 30, 31, 0, 0, 95, 104, 105, 100, 101, 106, 107, 109, 111, 112, 113, 114, 115, 116, 117⟩,
  ⟨69, 30, 31, 1, 0, 105, 124, 125, 120, 121, 126, 127, 129, 131, 132, 133, 134, 135, 136, 137⟩,
  ⟨157, 31, 30, 0, 0, 162, 169, 170, 165, 166, 171, 172, 174, 176, 177, 178, 179, 180, 181, 182⟩,
  ⟨250, 30, 31, 0, 1, 255, 262, 263, 258, 259, 264, 265, 267, 269, 270, 271, 272, 273, 274, 275⟩,
  ⟨406, 31, 30, 0, 0, 411, 418, 419, 414, 415, 420, 421, 423, 425, 426, 427, 428, 429, 430, 431⟩,
  ⟨641, 30, 31, 0, 0, 646, 653, 654, 649, 650, 655, 656, 658, 660, 661, 662, 663, 664, 665, 666⟩,
  ⟨971, 31, 30, 0, 0, 976, 983, 984, 979, 980, 985, 986, 988, 990, 991, 992, 993, 994, 995, 996⟩,
  ⟨1412, 30, 31, 0, 0, 1417, 1424, 1425, 1420, 1421, 1426, 1427, 1429, 1431, 1432, 1433, 1434, 1435, 1436, 1437⟩,
  ⟨1980, 31, 30, 0, 0, 1985, 1992, 1993, 1988, 1989, 1994, 1995, 1997, 1999, 2000, 2001, 2002, 2003, 2004, 2005⟩,
  ⟨2691, 30, 31, 0, 0, 2696, 2703, 2704, 2699, 2700, 2705, 2706, 2708, 2710, 2711, 2712, 2713, 2714, 2715, 2716⟩,
  ⟨3561, 31, 30, 0, 0, 3566, 3573, 3574, 3569, 3570, 3575, 3576, 3578, 3580, 3581, 3582, 3583, 3584, 3585, 3586⟩,
  ⟨4606, 30, 31, 0, 0, 4611, 4618, 4619, 4614, 4615, 4620, 4621, 4623, 4625, 4626, 4627, 4628, 4629, 4630, 4631⟩
]

def getSendRow (j : Nat) : SendRow :=
  sendRows[j]?.getD ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def sendRowOk (j : Nat) (r : SendRow) : Bool :=
  let wmac_id := sendWmacId j
  let ptTs := sendPtTs j
  let ptBs := sendPtBytes j
  let addr := if j < 2 then aliceBobAddrBytes else []
  let c2_id := r.mkey_id - 1
  let c3_id := r.iv_id - 1
  decide (j < 12) &&
  decide (r.pk_id < dagSize) && decide (r.myIk_id < dagSize) && decide (r.peerIk_id < dagSize) &&
  decide (r.seed_id < dagSize) && decide (r.nck_id < dagSize) &&
  decide (r.salt_id < dagSize) && decide (r.pq_id < dagSize) &&
  decide (r.prk_id < dagSize) && decide (r.ckey_id < dagSize) && decide (c2_id < dagSize) &&
  decide (r.mkey_id < dagSize) && decide (c3_id < dagSize) && decide (r.iv_id < dagSize) &&
  decide (r.ct_id < dagSize) && decide (r.wire_id < dagSize) &&
  decide (r.mi_r_id < dagSize) && decide (r.mi_id < dagSize) &&
  decide (r.fmac_id < dagSize) && decide (r.mac_id < dagSize) && decide (wmac_id < dagSize) &&
  isKdfOp (dagOp r.seed_id) r.old_cks_id 2 &&
  isKdfOp (dagOp r.nck_id) r.old_cks_id 3 &&
  isLitOp (dagOp r.salt_id) (dagBytes r.salt_id) &&
  decide ((dagBytes r.salt_id).length = 32) &&
  isLitOp (dagOp r.pq_id) (dagBytes r.pq_id) &&
  isKdfOp (dagOp r.prk_id) r.salt_id r.seed_id &&
  isKdfOp (dagOp r.ckey_id) r.prk_id 13 &&
  isConcatOp (dagOp c2_id) r.ckey_id 14 &&
  isKdfOp (dagOp r.mkey_id) r.prk_id c2_id &&
  isConcatOp (dagOp c3_id) r.mkey_id 15 &&
  isKdfOp (dagOp r.iv_id) r.prk_id c3_id &&
  isSymEncPtOp (dagOp r.ct_id) r.ckey_id r.iv_id ptTs ptBs &&
  isTrWireOp (dagOp r.wire_id) messageVersion r.pk_id r.ctr r.prev r.ct_id r.pq_id addr &&
  isConcatOp (dagOp r.mi_r_id) r.peerIk_id r.wire_id &&
  isConcatOp (dagOp r.mi_id) r.myIk_id r.mi_r_id &&
  isKdfOp (dagOp r.fmac_id) r.mkey_id r.mi_id &&
  isTrunc8Op (dagOp r.mac_id) r.fmac_id &&
  isConcatOp (dagOp wmac_id) r.wire_id r.mac_id &&
  decide ((dagBytes r.mac_id).length = 8) &&
  decide ((dagBytes r.mac_id).take 4 ≠ compTag4) &&
  decide ((dagBytes r.wire_id).length < 2048)

theorem all_send_rows_ok : (List.range 12).all (fun j => sendRowOk j (getSendRow j)) = true := by
  decide +kernel

/-- `SafeMemo` and `TermAt` witnesses produced by clean `.send` call `j` from state `st`. -/
structure SendStepOut {cls : Nat → Nat} (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List Bytes)
    (st : TRState) (j : Nat) : Prop where
  spqr_sm : SafeMemo dagSize dagOp dagBytes S g pts (sendStOf st (cls j) (sendPtTs j)).spqr
  pqKey : TermAt dagSize dagOp dagBytes S g pts (pqKeyOf st (cls j) (sendPtTs j)) (getSendRow j).salt_id
  pqMsg : TermAt dagSize dagOp dagBytes S g pts (pqMsgOf st (cls j) (sendPtTs j)) (getSendRow j).pq_id
  cks_next : TermAt dagSize dagOp dagBytes S g pts (sendStOf st (cls j) (sendPtTs j)).cks (getSendRow j).nck_id
  seed : TermAt dagSize dagOp dagBytes S g pts (kdfCk st.cks).2 (getSendRow j).seed_id
  ct : TermAt dagSize dagOp dagBytes S g pts
    (encSig st (rnd (sendPtTs j + 1) (cls j)) (pqKeyOf st (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32)).ciphertext
    (getSendRow j).ct_id
  wire : TermAt dagSize dagOp dagBytes S g pts
    (encSig st (rnd (sendPtTs j + 1) (cls j)) (pqKeyOf st (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32)).wire
    (getSendRow j).wire_id
  mac : TermAt dagSize dagOp dagBytes S g pts
    (encSig st (rnd (sendPtTs j + 1) (cls j)) (pqKeyOf st (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32)).mac
    (getSendRow j).mac_id
  wmac : TermAt dagSize dagOp dagBytes S g pts (cleanSendMsg cls j) (sendWmacId j)

/-- Certified single-step `.send` transition at call `j < 12`: pins `pqKey` and `pqMsg` from the
wire and MAC bytes and derives `SendStepOut`. -/
theorem send_step_at {cls : Nat → Nat} {S : OpaqueSymbolSemantics} {g : Ghost}
    {vis : List VisEntry} {pts : List Bytes} {nSends nRecvs j : Nat} {st : TRState}
    (hp : PrefixPinned cls S g vis nSends nRecvs)
    (hcls : ValidCoinLens cls)
    (hj : j < nSends) (hj12 : j < 12)
    (hpt_mem : randTerm (sendPtTs j) 32 ∈ pts)
    (hclean : cleanSendMsg cls j = sendMsgOf st (cls j) (sendPtTs j))
    (hspqr : SafeMemo dagSize dagOp dagBytes S g pts st.spqr)
    (tpk : TermAt dagSize dagOp dagBytes S g pts (dhPk st.dhs) (getSendRow j).pk_id)
    (tmyIk : TermAt dagSize dagOp dagBytes S g pts st.myIk (getSendRow j).myIk_id)
    (tpeerIk : TermAt dagSize dagOp dagBytes S g pts st.peerIk (getSendRow j).peerIk_id)
    (tcks : TermAt dagSize dagOp dagBytes S g pts st.cks (getSendRow j).old_cks_id)
    (hns : st.ns = (getSendRow j).ctr)
    (hpn : st.pn = (getSendRow j).prev) :
    SendStepOut (cls := cls) S g pts st j := by
  have hrow := List.all_eq_true.mp all_send_rows_ok j (List.mem_range.mpr hj12)
  set r := getSendRow j
  unfold sendRowOk at hrow
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrow
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hpk_lt⟩, hmy_lt⟩, hpeer_lt⟩,
    hseed_lt⟩, hnck_lt⟩, hsalt_lt⟩, hpq_lt⟩, hprk_lt⟩, hckey_lt⟩, hc2_lt⟩,
    hmkey_lt⟩, hc3_lt⟩, hiv_lt⟩, hct_lt⟩, hwire_lt⟩, hmir_lt⟩, hmi_lt⟩,
    hfmac_lt⟩, hmac_lt⟩, hwmac_lt⟩,
    hseed_op⟩, hnck_op⟩, hsalt_op⟩, hsalt_len⟩, hpq_op⟩, hprk_op⟩, hckey_op⟩, hc2_op⟩,
    hmkey_op⟩, hc3_op⟩, hiv_op⟩, hct_op⟩, hwire_op⟩, hmir_op⟩, hmi_op⟩, hfmac_op⟩,
    hmac_op⟩, hwmac_op⟩, hmac_len⟩, huntag⟩, hwire_len_lt⟩ := hrow
  have hcoins_sm : SafeMemo dagSize dagOp dagBytes S g pts (rnd (sendPtTs j + 1) (cls j)) := by
    rcases hcls j hj12 with h0 | h32 | h64
    · rw [h0]; exact safeMemo_randTerm_zero (sendPtTs j + 1)
    · rw [h32]
      have hcok : (decide (sendC32Id j < dagSize) && isRandOp (dagOp (sendC32Id j)) (sendPtTs j + 1) 32) = true := by
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
            j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
      exact (termAt_rand_b (pts := pts) (hp.send_c32 j hj h32) hcok).safeMemo
    · rw [h64]
      have hcok : (decide (sendC64Id j < dagSize) && isRandOp (dagOp (sendC64Id j)) (sendPtTs j + 1) 64) = true := by
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
            j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
      exact (termAt_rand_b (pts := pts) (hp.send_c64 j hj h64) hcok).safeMemo
  obtain ⟨hspqr_next, hpqKey_sm, hpqMsg_sm⟩ := safeMemo_spqrSend hspqr hcoins_sm
  have tb01 : TermAt dagSize dagOp dagBytes S g pts (litByte 1) 2 := termAt_lit_b (by decide +kernel)
  have tb02 : TermAt dagSize dagOp dagBytes S g pts (litByte 2) 3 := termAt_lit_b (by decide +kernel)
  have tseed : TermAt dagSize dagOp dagBytes S g pts (kdfCk st.cks).2 r.seed_id := by
    change TermAt dagSize dagOp dagBytes S g pts (hmac st.cks (litByte 1)) r.seed_id
    exact termAt_kdf_b (Bool.and_eq_true_iff.mpr ⟨decide_eq_true hseed_lt, hseed_op⟩) tcks tb01
  have tnck : TermAt dagSize dagOp dagBytes S g pts (kdfCk st.cks).1 r.nck_id := by
    change TermAt dagSize dagOp dagBytes S g pts (hmac st.cks (litByte 2)) r.nck_id
    exact termAt_kdf_b (Bool.and_eq_true_iff.mpr ⟨decide_eq_true hnck_lt, hnck_op⟩) tcks tb02
  obtain ⟨hi1, hi2, hi3⟩ := wmkInfo_termAt (S := S) (g := g) (pts := pts)
  have tsalt_lit := termAt_litOf_b (S := S) (g := g) (pts := pts) hsalt_lt hsalt_op
  have hk_op : ∀ {x a b : Nat}, isKdfOp (dagOp x) a b = true → dagOp x = .kdf a b := by
    intro x a b h; cases hd : dagOp x <;> simp [isKdfOp, hd] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  have hc_op : ∀ {x a b : Nat}, isConcatOp (dagOp x) a b = true → dagOp x = .concat a b := by
    intro x a b h; cases hd : dagOp x <;> simp [isConcatOp, hd] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  have ht_op : ∀ {x a : Nat}, isTrunc8Op (dagOp x) a = true → dagOp x = .trunc8 a := by
    intro x a h; cases hd : dagOp x <;> simp [isTrunc8Op, hd] at h; subst h; rfl
  have hse_op : ∀ {x c i t : Nat} {p : HwBytes},
      isSymEncPtOp (dagOp x) c i t p = true → dagOp x = .symEncPt c i t p := by
    intro x c i t p h; cases hd : dagOp x <;> simp [isSymEncPtOp, hd] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h; rfl
  have htw_op : ∀ {x rk ct pq : Nat} {v : UInt8} {c p : UInt32} {ad : HwBytes},
      isTrWireOp (dagOp x) v rk c p ct pq ad = true → dagOp x = .trWire v rk c p ct pq ad := by
    intro x rk ct pq v c p ad h; cases hd : dagOp x <;> simp [isTrWireOp, hd] at h
    obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h; rfl
  obtain ⟨tck0, tmk0, tiv0⟩ := termAt_trMsgKeys dag_nodes_ok hi1 hi2 hi3
    ⟨hprk_lt, hk_op hprk_op⟩ ⟨hckey_lt, hk_op hckey_op⟩ ⟨hc2_lt, hc_op hc2_op⟩
    ⟨hmkey_lt, hk_op hmkey_op⟩ ⟨hc3_lt, hc_op hc3_op⟩ ⟨hiv_lt, hk_op hiv_op⟩ tsalt_lit tseed
  have hprk_lit : gamma evictedI0 S g (hmac (litOf (dagBytes r.salt_id)) (litOf (dagBytes r.seed_id))) =
      gamma evictedI0 S g (hmac (litOf (dagBytes r.salt_id)) (kdfCk st.cks).2) := by
    simp only [gamma_hmacE, gamma_litOf, tseed.gamma_eq]
  obtain ⟨hck_c, hmk_c, hiv_c⟩ := gamma_trMsgKeys_congr_prk hprk_lit
  have twire_lit_dummy : gamma evictedI0 S g
      (computeMac (trMsgKeys (litOf (dagBytes r.salt_id)) (litOf (dagBytes r.seed_id))).macKey
        (litOf (dagBytes r.myIk_id)) (litOf (dagBytes r.peerIk_id)) (litOf (dagBytes r.wire_id))) =
      dagBytes r.mac_id := by
    simp only [gamma_computeMacE, hmk_c, tmk0.gamma_eq, gamma_litOf]
    have hb_mir := dag_bytes_ok hmir_lt; rw [hc_op hmir_op] at hb_mir
    simp only [dagOpBytesOk, beq_iff_eq] at hb_mir
    have hb_mi := dag_bytes_ok hmi_lt; rw [hc_op hmi_op] at hb_mi
    simp only [dagOpBytesOk, beq_iff_eq] at hb_mi
    have hb_fm := dag_bytes_ok hfmac_lt; rw [hk_op hfmac_op] at hb_fm
    simp only [dagOpBytesOk, beq_iff_eq] at hb_fm
    have hb_m := dag_bytes_ok hmac_lt; rw [ht_op hmac_op] at hb_m
    simp only [dagOpBytesOk, beq_iff_eq] at hb_m
    rw [← hb_mir, ← hb_mi, ← hb_fm, ← hb_m]
  have hb_ct := dag_bytes_ok hct_lt; rw [hse_op hct_op] at hb_ct
  simp only [dagOpBytesOk, beq_iff_eq] at hb_ct
  have hb_w := dag_bytes_ok hwire_lt; rw [htw_op hwire_op] at hb_w
  simp only [dagOpBytesOk, beq_iff_eq] at hb_w
  have hb_wm := dag_bytes_ok hwmac_lt; rw [hc_op hwmac_op] at hb_wm
  simp only [dagOpBytesOk, beq_iff_eq] at hb_wm
  have hmsg_bytes : gamma evictedI0 S g
      (encMsg st (rnd (sendPtTs j + 1) (cls j)) (pqKeyOf st (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32)) =
      dagBytes r.wire_id ++ dagBytes r.mac_id := by
    have h1 := hp.send_msg j hj
    rw [hclean] at h1
    exact h1.trans hb_wm
  have hparse : parseTrSignalMsg (cleanSendMsg cls j) =
      some (encSig st (rnd (sendPtTs j + 1) (cls j)) (pqKeyOf st (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32)) := by
    rw [hclean]; exact parse_encMsg _ _ _ _
  have haddr := hp.send_addr j hj _ hparse
  obtain ⟨hpqKey_bs, hpqMsg_bs⟩ := encMsg_pins_pqKey_and_pqMsg rfl hmsg_bytes hmac_len hsalt_len
    huntag tseed.gamma_eq tpk.gamma_eq tmyIk.gamma_eq tpeerIk.gamma_eq (hp.send_pt j hj) haddr
    twire_lit_dummy.symm (hck_c.trans tck0.gamma_eq) (hiv_c.trans tiv0.gamma_eq)
    hb_ct.symm (by rw [hns, hpn]; exact hb_w.symm) hwire_len_lt
  obtain ⟨hpqKey_sh, hpqMsg_sh⟩ := spqrSend_shapes S g st.spqr (rnd (sendPtTs j + 1) (cls j))
  have hs_lit_eq : dagOp r.salt_id = .lit (dagBytes r.salt_id) := by
    cases hd : dagOp r.salt_id <;> simp [isLitOp, hd] at hsalt_op; exact congrArg DagOp.lit hsalt_op
  have hp_lit_eq : dagOp r.pq_id = .lit (dagBytes r.pq_id) := by
    cases hd : dagOp r.pq_id <;> simp [isLitOp, hd] at hpq_op; exact congrArg DagOp.lit hpq_op
  have tpqKey : TermAt dagSize dagOp dagBytes S g pts (pqKeyOf st (cls j) (sendPtTs j)) r.salt_id :=
    termAt_of_opaque dag_nodes_ok hsalt_lt hs_lit_eq hpqKey_bs (hpqKey_sh.trans (congrArg litOf hpqKey_bs)) hpqKey_sm
  have tpqMsg : TermAt dagSize dagOp dagBytes S g pts (pqMsgOf st (cls j) (sendPtTs j)) r.pq_id :=
    termAt_of_opaque dag_nodes_ok hpq_lt hp_lit_eq hpqMsg_bs (hpqMsg_sh.trans (congrArg litOf hpqMsg_bs)) hpqMsg_sm
  obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys dag_nodes_ok hi1 hi2 hi3
    ⟨hprk_lt, hk_op hprk_op⟩ ⟨hckey_lt, hk_op hckey_op⟩ ⟨hc2_lt, hc_op hc2_op⟩
    ⟨hmkey_lt, hk_op hmkey_op⟩ ⟨hc3_lt, hc_op hc3_op⟩ ⟨hiv_lt, hk_op hiv_op⟩ tpqKey tseed
  have tct := termAt_symEncPt dag_nodes_ok hct_lt (hse_op hct_op) tck tiv hpt_mem
    (hp.send_pt j hj) (sendPtBytes_len_lt8 hj12)
  have twire : TermAt dagSize dagOp dagBytes S g pts
      (encSig st (rnd (sendPtTs j + 1) (cls j)) (pqKeyOf st (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32)).wire
      r.wire_id := by
    dsimp only [encSig]
    exact termAt_trWire dag_nodes_ok hwire_lt (by rw [hns, hpn]; exact htw_op hwire_op) tpk tct tpqMsg haddr
  have tmac : TermAt dagSize dagOp dagBytes S g pts
      (encSig st (rnd (sendPtTs j + 1) (cls j)) (pqKeyOf st (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32)).mac
      r.mac_id :=
    termAt_computeMac dag_nodes_ok ⟨hmir_lt, hc_op hmir_op⟩ ⟨hmi_lt, hc_op hmi_op⟩
      ⟨hfmac_lt, hk_op hfmac_op⟩ ⟨hmac_lt, ht_op hmac_op⟩ tmk tmyIk tpeerIk twire
  have twmac : TermAt dagSize dagOp dagBytes S g pts (cleanSendMsg cls j) (sendWmacId j) := by
    rw [hclean]; unfold sendMsgOf encMsg
    exact termAt_concat dag_nodes_ok hwmac_lt (hc_op hwmac_op) twire tmac
  exact ⟨hspqr_next, tpqKey, tpqMsg, tnck, tseed, tct, twire, tmac, twmac⟩

abbrev cls0 : Nat → Nat := fun _ => 0

theorem encSt_toDRState {st₁ st₂ : TRState} {c₁ c₂ : Bytes}
    (h : st₁.toDRState = st₂.toDRState) :
    (encSt st₁ c₁).toDRState = (encSt st₂ c₂).toDRState := by
  cases st₁; cases st₂; dsimp only at h; subst h; rfl

theorem decSt0_toDRState {st₁ st₂ : TRState} {p dhs pq₁ pq₂ : Bytes}
    (h : st₁.toDRState = st₂.toDRState) :
    (decSt0 st₁ p dhs pq₁).toDRState = (decSt0 st₂ p dhs pq₂).toDRState := by
  cases st₁; cases st₂; dsimp only at h; subst h; rfl

theorem hrConfig_toDRState (cls : Nat → Nat) :
    ∀ h : Nat,
      (hrConfig cls h).1 = (hrConfig cls0 h).1 ∧
      (hrConfig cls h).2.1 = (hrConfig cls0 h).2.1 ∧
      (hrConfig cls h).2.2.1.toDRState = (hrConfig cls0 h).2.2.1.toDRState ∧
      (hrConfig cls h).2.2.2.toDRState = (hrConfig cls0 h).2.2.2.toDRState
  | 0 => ⟨rfl, rfl, rfl, rfl⟩
  | h + 1 => by
    have ⟨hm, hp, hs, hr⟩ := hrConfig_toDRState cls h
    rcases h1 : hrConfig cls h with ⟨me1, peer1, s1, r1⟩
    rcases h0 : hrConfig cls0 h with ⟨me0, peer0, s0, r0s⟩
    rw [h1, h0] at hm hp hs hr
    dsimp only at hm hp hs hr
    have hdhs : s1.dhs = s0.dhs := congrArg (·.dhs) hs
    simp only [hrConfig, h1, h0, hm, hp]
    refine ⟨trivial, trivial, ?_, encSt_toDRState hs⟩
    unfold recvStOf; rw [hdhs]
    exact decSt0_toDRState hr

private theorem forall₂_append {α β : Type} {R : α → β → Prop} {l₁ l₂ : List α} {m₁ m₂ : List β}
    (h₁ : List.Forall₂ R l₁ m₁) (h₂ : List.Forall₂ R l₂ m₂) :
    List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons hr _ ih => exact List.Forall₂.cons hr ih

/-- Participant names and `.toDRState` projections across `allStates24 cls` agree with the
zero-coin schedule `cls0`. -/
theorem allStates24_toDRState (cls : Nat → Nat) :
    List.Forall₂
      (fun ls ls₀ => ls.participant = ls₀.participant ∧ ls.state.toDRState = ls₀.state.toDRState)
      (allStates24 cls) (allStates24 cls0) := by
  unfold allStates24
  refine forall₂_append ?_ ?_
  · exact List.Forall₂.cons ⟨rfl, rfl⟩
      (List.Forall₂.cons ⟨rfl, rfl⟩
        (List.Forall₂.cons ⟨rfl, rfl⟩
          (List.Forall₂.cons ⟨rfl, rfl⟩ List.Forall₂.nil)))
  · have hstep : ∀ h : Nat, List.Forall₂
        (fun ls ls₀ => ls.participant = ls₀.participant ∧ ls.state.toDRState = ls₀.state.toDRState)
        (hrStates cls h) (hrStates cls0 h) := fun h => by
      have ⟨hm, hp, hs, hr⟩ := hrConfig_toDRState cls h
      rcases h1 : hrConfig cls h with ⟨me1, peer1, s1, r1⟩
      rcases h0 : hrConfig cls0 h with ⟨me0, peer0, s0, r0s⟩
      rw [h1, h0] at hm hp hs hr
      dsimp only at hm hp hs hr
      have hdhs : s1.dhs = s0.dhs := congrArg (·.dhs) hs
      simp only [hrStates, h1, h0]
      refine List.Forall₂.cons ⟨hm, encSt_toDRState hs⟩
        (List.Forall₂.cons ⟨hp, ?_⟩ List.Forall₂.nil)
      unfold recvStOf; rw [hdhs]
      exact decSt0_toDRState hr
    have hr10 : List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := rfl
    rw [hr10]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact forall₂_append (hstep 0)
      (forall₂_append (hstep 1)
      (forall₂_append (hstep 2)
      (forall₂_append (hstep 3)
      (forall₂_append (hstep 4)
      (forall₂_append (hstep 5)
      (forall₂_append (hstep 6)
      (forall₂_append (hstep 7)
      (forall₂_append (hstep 8) (hstep 9)))))))))

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalkSend
