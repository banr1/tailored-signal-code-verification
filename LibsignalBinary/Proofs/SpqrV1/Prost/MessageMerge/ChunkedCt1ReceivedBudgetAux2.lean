/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1Received
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# SPQR V1: Budget-Threaded Field-1 & Field-2 Step Lemmas for `Chunked.Ct1Received::merge` (Block `303`)

Proves budget-threaded `tag = 1` (`uc : Unchunked.EkSentCt1Received`) and `tag = 2`
(`sendingEk : PolynomialEncoder`) initialization and call-step lemmas for
`V1State.Chunked.Ct1Received::merge` (Block `303`) with `withLsCodeRoLoaded lsmpl` callees.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedBudgetAux2

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk IsDropSuffix pointsToBytes_prefix_join
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join)
open CryptoVerification.LibsignalSpqrV1 (PolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth (WppPost optAuthenticatorPBCapAt setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.Poly (protoPolynomialEncoderAt)
open CryptoVerification.SpqrV1.ProtoRepr
  (optEkSentCt1ReceivedPBAt optPolynomialEncoderPBAt polynomialEncoderPBAt
   vecVecU8At vecVecU8At_eq_exists_pin vecVecU8Buf vecVecU8PinnedAt_eq_header_buf)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (cap_add_one_beq_zero_false cap_add_one_bne_zero_true
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (UnchunkedEkSentCt1ReceivedMergeGhost)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedCt1ReceivedMergeGhost ChunkedLoopRegs PolyEncoderMergeGhost SepWPpLscro
   bv64_add_zero bv64_sub_zero chunkedBelow chunkedBelow_eq_poly chunkedBelow_eq_unchunked
   chunkedCt1ReceivedMerge_fnOff chunkedCt1ReceivedPBAt chunkedCt1ReceivedPBCapAt
   chunkedSavedRegs codecWireTypeToProto
   default_ekSentCt1Received_entails_cap default_polyEncoder_entails_pb
   memRegion_48_split_128 memRegion_ekSentCt1Received_none_split memRegion_polyEncoder_none_split
   optPolyEncoderPolysLen optPolyEncoderPtsLen
   optPolyEncoder_getD_default_polys_len optPolyEncoder_getD_default_pts_len
   optUnchunkedEkSentCt1ReceivedPBCapAt
   optUnchunkedEkSentCt1ReceivedPBCapAt_entails_optEkSentCt1ReceivedPBAt
   optUnchunkedEkSentCt1ReceivedPBCapAt_mono polyEncoderToProto
   protoPolynomialEncoderAt_eq_pb proto_mergeMessage_len_le
   unchunkedEkSentCt1ReceivedPBCapAt vecU8Buf vecVecU8Buf_entails_cap_lt)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_303 blkPl_303)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedBudgetAux
  (ct1ReceivedErrFrame ct1ReceivedLoopPre ct1Received_push_err_exit_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (ChunkedCt1ReceivedMergeEnv FitsEnv.spqrMergeLoop_mono FitsEnv.spqrMergeLoop_split
   SpqrMergeLoopEnv UnchunkedEkSentCt1ReceivedMergeEnv UnchunkedEkSentCt1ReceivedMergePostEnv
   chunkedCt1ReceivedMergeSpec ct1ReceivedPolyCapBound decodeErrorPushMergeBudgetSpec
   unchunkedEkSentCt1ReceivedMergeSpec unchunkedEkSentCt1ReceivedMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro pool_entails_spqrPoolAt_append
   sepWPpLscro_of_vm spqrPoolAt spqrPoolAt_of_vmPreserved vmPreserved_setMem_same)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (PolyEncoderMergeEnv PolyEncoderMergePostEnv
   polyEncoderCapBound polyEncoderMergeSpec polyEncoderMergeSpecOfEnv polyMergeLoopEnv_to_spqr)

private theorem sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedCt1ReceivedMerge_fnOff
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre calleeSavedVRegs_setMem_pre

/-! ## 1. Representation & `FitsEnv` Embedding Helpers -/

private theorem vecU8Buf_entails_cap_lt_aux (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  exact Entails.pure_left fun h => Entails.pure_right h.2.1 (Entails.pure_right h (Entails.refl _))

private theorem vecU8At_eq_header_sep_buf_aux (A : RustAlloc) (a cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs =
      vecHeader a cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8At vecU8Buf; sep_ac_rfl

private theorem vecU8At_entails_header_cap_lt_aux (A : RustAlloc) (a cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗ (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  rw [vecU8At_eq_header_sep_buf_aux, vecHeader]
  exact Entails.trans (sepConj_mono_right (vecU8Buf_entails_cap_lt_aux A cap ptr bs)) (by sep_entail)

private theorem header_buf_entails_vecU8At_aux (A : RustAlloc) (a cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs ⊢ vecU8At A a cap ptr bs := by
  rw [vecU8At_eq_header_sep_buf_aux, vecHeader]; sep_entail

private def ucCt1TailCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (u : V1State.Unchunked.EkSentCt1Received) : SepProp :=
  (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x18#64) cap ptr u.ct1) ∗
    optAuthenticatorPBCapAt A (a + 0x30#64) bsLen u.auth ∗
    ((a + 0x60#64) ↦₆₄ u.epoch)

private theorem unchunkedEkSentCt1ReceivedPBCapAt_entails_cmn (A : RustAlloc) (a : BitVec 64)
    (bsLen : Nat) (u : V1State.Unchunked.EkSentCt1Received) :
    unchunkedEkSentCt1ReceivedPBCapAt A a bsLen u ⊢
      ∃∗ cap_dk : BitVec 64, ∃∗ ptr_dk : BitVec 64,
        ⌜cap_dk.toNat < 2 ^ 63⌝ ∗ ⌜BytesMergeCapOk cap_dk bsLen⌝ ∗
        (a ↦₆₄ cap_dk) ∗ ((a + 8#64) ↦₆₄ ptr_dk) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 u.dk.length) ∗
        vecU8Buf A cap_dk ptr_dk u.dk ∗ ucCt1TailCapAt A a bsLen u := by
  unfold unchunkedEkSentCt1ReceivedPBCapAt ucCt1TailCapAt
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine Entails.sepExists_elim fun cap_dk => Entails.sepExists_elim fun ptr_dk => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro cap_dk)
  refine Entails.trans ?_ (Entails.sepExists_intro ptr_dk)
  refine Entails.pure_left fun hcap => ?_
  refine Entails.trans
    (sepConj_mono_left (vecU8At_entails_header_cap_lt_aux A a cap_dk ptr_dk u.dk)) ?_
  simp only [sepConj_assoc]
  exact Entails.pure_left fun hlt =>
    Entails.pure_right hlt (Entails.pure_right hcap (Entails.refl _))

private theorem cmn_entails_unchunkedEkSentCt1ReceivedPBCapAt (A : RustAlloc) (a : BitVec 64)
    (bsLen : Nat) (u : V1State.Unchunked.EkSentCt1Received)
    (cap_dk ptr_dk : BitVec 64) (hcap : BytesMergeCapOk cap_dk bsLen) :
    (a ↦₆₄ cap_dk) ∗ ((a + 8#64) ↦₆₄ ptr_dk) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 u.dk.length) ∗
      vecU8Buf A cap_dk ptr_dk u.dk ∗ ucCt1TailCapAt A a bsLen u ⊢
      unchunkedEkSentCt1ReceivedPBCapAt A a bsLen u := by
  unfold unchunkedEkSentCt1ReceivedPBCapAt ucCt1TailCapAt
  refine Entails.trans (Entails.of_eq (show _ =
    ((a ↦₆₄ cap_dk) ∗ ((a + 8#64) ↦₆₄ ptr_dk) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 u.dk.length) ∗
      vecU8Buf A cap_dk ptr_dk u.dk) ∗
      ((∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x18#64) cap ptr u.ct1) ∗
        optAuthenticatorPBCapAt A (a + 0x30#64) bsLen u.auth ∗
        ((a + 0x60#64) ↦₆₄ u.epoch)) by sep_ac_rfl)) ?_
  refine sepConj_mono_left ?_
  refine Entails.trans (header_buf_entails_vecU8At_aux A a cap_dk ptr_dk u.dk) ?_
  refine Entails.trans ?_ (Entails.sepExists_intro cap_dk)
  refine Entails.trans ?_ (Entails.sepExists_intro ptr_dk)
  exact Entails.pure_right hcap (Entails.refl _)

private theorem fitsEnv_unchunkedEkSentMerge_of_spqr {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {f F maxLen polyBound : Nat}
    {x_uc : UnchunkedEkSentCt1ReceivedMergeGhost} {evs : List AllocEvent}
    (hf : f + (4 * x_uc.bs.length + 8) ≤ F)
    (hlen : x_uc.bs.length ≤ maxLen)
    (hevs : SpqrMergeLoopEnv f maxLen polyBound evs)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv F maxLen polyBound)) :
    FitsEnv M lim (M.stepEvents evs st) (UnchunkedEkSentCt1ReceivedMergeEnv x_uc) := by
  have hrem := FitsEnv.spqrMergeLoop_split (f₂ := 4 * x_uc.bs.length + 8) hevs
    (hFit.mono fun _ h => h.mono_fuel hf)
  exact FitsEnv.spqrMergeLoop_mono (Nat.le_refl _) hlen (Nat.zero_le _) hrem

private theorem fitsEnv_polyEncoderMerge_of_spqr {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {f F maxLen polyBound : Nat}
    {x_poly : PolyEncoderMergeGhost} {evs : List AllocEvent}
    (hf : f + (2 * x_poly.bs.length + 2) ≤ F)
    (hlen : x_poly.bs.length ≤ maxLen)
    (hpoly : polyEncoderCapBound x_poly ≤ polyBound)
    (hevs : SpqrMergeLoopEnv f maxLen polyBound evs)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv F maxLen polyBound)) :
    FitsEnv M lim (M.stepEvents evs st) (PolyEncoderMergeEnv x_poly) := by
  have hrem := FitsEnv.spqrMergeLoop_split (f₂ := 2 * x_poly.bs.length + 2) hevs
    (hFit.mono fun _ h => h.mono_fuel hf)
  exact fun evs' hp => hrem evs' (polyMergeLoopEnv_to_spqr hlen hpoly hp)

/-! ## 2. Placed Field-1 (`uc`) and Field-2 (`sendingEk`) Step Lemmas (Block `303`) -/

section Placed

set_option quotPrecheck false in
local notation "blkBase" => (blkPl_303).base

theorem ct1Received_tag1_init_step_budget_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : ChunkedCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Received} {rest : List (BitVec 8)}
    {v0 v19 v21 v22 : BitVec 64}
    (hpc : s.pc = (blkPl_303).base + 312#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = v0) (hx19 : s.readReg64 (Reg.gpr 19#5) = v19)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = v21)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = v22) (hcs : ChunkedLoopRegs s0 s)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_303).base + 344#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = v0 → s'.readReg64 (Reg.gpr 19#5) = v19 →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = v21 →
      s'.readReg64 (Reg.gpr 22#5) = v22 → ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s'
        (unchunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr rest.length (m.uc.getD default) ∗
          optPolynomialEncoderPBAt A.repAlloc (x.msgPtr + 104#64) m.sendingEk ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0 ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ct1ReceivedPolyCapBound x) s')
        (WppPost (chunkedCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R)) :
    SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s
      (ct1ReceivedLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (ct1ReceivedPolyCapBound x))
      (WppPost (chunkedCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  rcases huc : m.uc with _ | u
  · rw [huc] at hcont
    apply sepWPpLscro_of_vm (mid := blkBase + 344#64)
    by_vm_steps
      (conv => arg 4; rw [ct1ReceivedLoopPre, chunkedCt1ReceivedPBCapAt, huc,
        optUnchunkedEkSentCt1ReceivedPBCapAt, memRegion_ekSentCt1Received_none_split x.msgPtr])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro w96; apply SepWP.exists_elim; intro w48
      apply SepWP.exists_elim; intro w40; apply SepWP.exists_elim; intro w32
      apply SepWP.exists_elim; intro w24; apply SepWP.exists_elim; intro w16
      apply SepWP.exists_elim; intro w8
      wp_steps
      apply SepWP.fold (default_ekSentCt1Received_entails_cap A.repAlloc x.msgPtr rest.length)
        (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := unchunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr rest.length
            (Option.getD none default) ∗
          optPolynomialEncoderPBAt A.repAlloc (x.msgPtr + 104#64) m.sendingEk ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0 ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ct1ReceivedPolyCapBound x) _)
        (by rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, htr])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx0])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx19])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx21])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx22])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25],
         ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx26],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩⟩
  · rw [huc] at hcont
    apply sepWPpLscro_of_vm (mid := blkBase + 344#64)
    by_vm_steps
      (conv => arg 4; rw [ct1ReceivedLoopPre, chunkedCt1ReceivedPBCapAt, huc,
        optUnchunkedEkSentCt1ReceivedPBCapAt])
      (conv => arg 4; simp only [sepConj_assoc, arm64_norm])
      apply SepWP.fold
        (unchunkedEkSentCt1ReceivedPBCapAt_entails_cmn A.repAlloc x.msgPtr rest.length u)
        (by sep_focus)
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro cap_dk
      apply SepWP.exists_elim; intro ptr_dk
      wp_focus_pure; intro hcap_lt
      wp_focus_pure; intro hcap_dk
      have hcmn1 := cap_add_one_beq_zero_false hcap_lt
      have hcmn2 := cap_add_one_bne_zero_true hcap_lt
      wp_steps
      apply SepWP.fold
        (cmn_entails_unchunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr rest.length u
          cap_dk ptr_dk hcap_dk)
        (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := unchunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr rest.length
            (Option.getD (some u) default) ∗
          optPolynomialEncoderPBAt A.repAlloc (x.msgPtr + 104#64) m.sendingEk ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0 ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ct1ReceivedPolyCapBound x) _)
        (by rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, htr])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx0])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx19])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx21])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx22])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25],
         ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx26],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩⟩

theorem ct1Received_tag1_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hUcCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hPushCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Received} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt1ReceivedMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_uc :
      (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = none →
      (mergeMessage V1State.Chunked.Ct1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (u' : V1State.Unchunked.EkSentCt1Received) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = some (u', rest') →
      s'.pc = (blkPl_303).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s'
        (ct1ReceivedLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with uc := some u' } x.bs rest' (ct1ReceivedPolyCapBound x))
        (WppPost (chunkedCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_303).base + 312#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s
      (ct1ReceivedLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (ct1ReceivedPolyCapBound x))
      (WppPost (chunkedCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  have hpush_exit := fun {s_err : State} {u' : V1State.Unchunked.EkSentCt1Received} =>
    @ct1Received_push_err_exit_cl_placed _ M A lim H hPushCall x st R s0 s_err
      { m with uc := some u' }
  refine ct1Received_tag1_init_step_budget_placed hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs ?_
  clear hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs s
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1
  obtain ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_uc : UnchunkedEkSentCt1ReceivedMergeGhost :=
    ⟨iwt, x.msgPtr, m.uc.getD default, x.bufRef, x.slot, restPtr, rest⟩
  apply sepWPpLscro_of_vm (mid := lsmpl.base 311)
  by_vm_steps
    (conv => arg 4; rw [spqrPoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      chunkedBelow_eq_unchunked s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_uc, M.stepEvents evs st))
      (ret_pc := blkBase + 356#64) hUcCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [unchunkedEkSentCt1ReceivedMergeSpec, unchunkedEkSentCt1ReceivedMergeSpecOfEnv, x_uc]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1, setWidth8_ofNat64_wt],
        by simp only [arm64_norm, wp_norm, hx20_1],
        by simp only [arm64_norm, wp_norm, hx19_1],
        hrest_lt,
        fitsEnv_unchunkedEkSentMerge_of_spqr (x_uc := x_uc) (by dsimp only [x_uc]; omega)
          hrest_le hevs hFit⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases huc_res : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption with
    | none =>
      have hnone := hnone_of_uc huc_res
      apply sepWPpLscro_of_vm (mid := blkBase + 480#64)
      by_vm_steps
        (conv => arg 4; simp only [unchunkedEkSentCt1ReceivedMergeSpec,
          unchunkedEkSentCt1ReceivedMergeSpecOfEnv, UnchunkedEkSentCt1ReceivedMergePostEnv,
          x_uc, huc_res, memRegion_48_split_128 s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0
        apply SepWP.exists_elim; intro evs_u
        apply SepWP.exists_elim; intro u'
        apply SepWP.exists_elim; intro n_err
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_u
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hn_err
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1, ← chunkedBelow_eq_unchunked s0.sp])
        have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (Nat.le_refl (6 * (x.bs.length - rest.length) + (4 * rest.length + 8)))
            hevs (hevs_u.mono (Nat.le_refl _) hrest_le (Nat.zero_le _)))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply sepWPpLscro_of_vm (mid := blkBase + 508#64)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm3 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm3]
        apply SepWPpLscro.weaken_pre
          (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
            decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
            memRegion (s0.sp - 120#64) 40 ∗ chunkedBelow s0.sp ∗
            ct1ReceivedErrFrame A lim st
              (6 * (x.bs.length - rest.length) + (4 * rest.length + 8))
              (ct1ReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { m with uc := some u' } x.bs)
          (by dsimp only [ct1ReceivedErrFrame, chunkedCt1ReceivedPBAt, optEkSentCt1ReceivedPBAt];
              sep_entail)
        exact hpush_exit hFit hnone (by omega) hn_err hsm0 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hspm])
          ⟨by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨u', rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le huc_res
      apply sepWPpLscro_of_vm (mid := blkBase + 192#64)
      by_vm_steps
        (conv => arg 4; simp only [unchunkedEkSentCt1ReceivedMergeSpec,
          unchunkedEkSentCt1ReceivedMergeSpecOfEnv, UnchunkedEkSentCt1ReceivedMergePostEnv,
          x_uc, huc_res,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_u
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_u
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1, ← chunkedBelow_eq_unchunked s0.sp])
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (by omega : 6 * (x.bs.length - rest.length) + 4 * (rest.length - rest'.length) ≤
              6 * (x.bs.length - rest'.length))
            hevs (hevs_u.mono (Nat.le_refl _) hrest_le (Nat.zero_le _)))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := ct1ReceivedLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { m with uc := some u' } x.bs rest' (ct1ReceivedPolyCapBound x))
          (by dsimp only [ct1ReceivedLoopPre, chunkedCt1ReceivedPBCapAt,
              optUnchunkedEkSentCt1ReceivedPBCapAt]; sep_entail)
        exact hcont u' rest' _ huc_res
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          ⟨by simp only [arm64_norm, wp_norm, hx23_m],
           by simp only [arm64_norm, wp_norm, hx24_m],
           by simp only [arm64_norm, wp_norm, hx25_m],
           ⟨by simp only [arm64_norm, wp_norm, hx26_m],
            by simp only [arm64_norm, wp_norm, hx27_m],
            by simp only [arm64_norm, wp_norm, hx28_m],
            by simp only [arm64_norm, wp_norm, hvregs_m]⟩⟩

theorem ct1Received_tag2_init_step_budget_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : ChunkedCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Received} {rest : List (BitVec 8)}
    {v0 v19 v21 v22 : BitVec 64}
    (hpc : s.pc = (blkPl_303).base + 260#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = v0) (hx19 : s.readReg64 (Reg.gpr 19#5) = v19)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = v21)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = v22) (hcs : ChunkedLoopRegs s0 s)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_303).base + 288#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = v0 → s'.readReg64 (Reg.gpr 19#5) = v19 →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = v21 →
      s'.readReg64 (Reg.gpr 22#5) = v22 → ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s'
        (protoPolynomialEncoderAt A.repAlloc (x.msgPtr + 104#64)
            (polyEncoderToProto (m.sendingEk.getD default)) ∗
          optUnchunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0 ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ct1ReceivedPolyCapBound x) s')
        (WppPost (chunkedCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R)) :
    SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s
      (ct1ReceivedLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (ct1ReceivedPolyCapBound x))
      (WppPost (chunkedCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  rcases hpe : m.sendingEk with _ | pe
  · rw [hpe] at hcont
    apply sepWPpLscro_of_vm (mid := blkBase + 288#64)
    by_vm_steps
      (conv => arg 4; rw [ct1ReceivedLoopPre, chunkedCt1ReceivedPBCapAt, hpe,
        optPolynomialEncoderPBAt, memRegion_polyEncoder_none_split (x.msgPtr + 104#64)])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro w48; apply SepWP.exists_elim; intro w40
      apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
      apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
      wp_steps
      apply SepWP.fold (default_polyEncoder_entails_pb A.repAlloc (x.msgPtr + 104#64))
        (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := protoPolynomialEncoderAt A.repAlloc (x.msgPtr + 104#64)
            (polyEncoderToProto (Option.getD none default)) ∗
          optUnchunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0 ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ct1ReceivedPolyCapBound x) _)
        (by rw [protoPolynomialEncoderAt_eq_pb, spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, htr])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx0])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx19])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx21])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx22])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25],
         ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx26],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩⟩
  · rw [hpe] at hcont
    apply sepWPpLscro_of_vm (mid := blkBase + 288#64)
    by_vm_steps
      (conv => arg 4; rw [ct1ReceivedLoopPre, chunkedCt1ReceivedPBCapAt, hpe,
        optPolynomialEncoderPBAt, polynomialEncoderPBAt,
        vecVecU8At_eq_exists_pin A.repAlloc (x.msgPtr + 104#64) pe.pts])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro pin
      (conv => arg 4; rw [vecVecU8PinnedAt_eq_header_buf]; simp only [sepConj_assoc])
      apply SepWP.fold (vecVecU8Buf_entails_cap_lt A.repAlloc pin.cap pin.ptr pe.pts) (by sep_focus)
      (conv => arg 4; simp only [sepConj_assoc, sepConj_pure_left_comm])
      apply SepWP.pure_elim; intro hcap_lt
      have hcmn1 := cap_add_one_beq_zero_false hcap_lt
      have hcmn2 := cap_add_one_bne_zero_true hcap_lt
      wp_steps
      have hfold_pts :
          ((x.msgPtr + 104#64) ↦₆₄ pin.cap) ∗ ((x.msgPtr + 104#64 + 8#64) ↦₆₄ pin.ptr) ∗
            ((x.msgPtr + 104#64 + 16#64) ↦₆₄ BitVec.ofNat 64 pe.pts.length) ∗
            vecVecU8Buf A.repAlloc pin.cap pin.ptr pe.pts ⊢
          vecVecU8At A.repAlloc (x.msgPtr + 104#64) pe.pts := by
        rw [vecVecU8At_eq_exists_pin]
        refine Entails.trans ?_ (Entails.sepExists_right pin (Entails.refl _))
        rw [vecVecU8PinnedAt_eq_header_buf]
        exact Entails.of_eq (by sep_ac_rfl)
      apply SepWP.fold hfold_pts (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := protoPolynomialEncoderAt A.repAlloc (x.msgPtr + 104#64)
            (polyEncoderToProto (Option.getD (some pe) default)) ∗
          optUnchunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0 ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ct1ReceivedPolyCapBound x) _)
        (by dsimp only [Option.getD]; rw [protoPolynomialEncoderAt_eq_pb, spqrPoolAt_of_vmPreserved hvm1];
            dsimp only [polynomialEncoderPBAt]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, htr])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx0])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx19])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx21])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx22])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25],
         ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx26],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩⟩

theorem ct1Received_tag2_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPolyCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hPushCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Received} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt1ReceivedMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hpts_lt : optPolyEncoderPtsLen m.sendingEk + rest.length < 2 ^ 56)
    (hpolys_lt : optPolyEncoderPolysLen m.sendingEk + rest.length < 2 ^ 56)
    (hcap_bound : Nat.max (optPolyEncoderPtsLen m.sendingEk) (optPolyEncoderPolysLen m.sendingEk) +
      rest.length ≤ ct1ReceivedPolyCapBound x)
    (hnone_of_pe :
      (mergeMessage PolynomialEncoder.mergeField
        (codecWireTypeToProto iwt) (m.sendingEk.getD default) rest 98).toOption = none →
      (mergeMessage V1State.Chunked.Ct1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (pe' : PolynomialEncoder) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage PolynomialEncoder.mergeField
        (codecWireTypeToProto iwt) (m.sendingEk.getD default) rest 98).toOption = some (pe', rest') →
      s'.pc = (blkPl_303).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s'
        (ct1ReceivedLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with sendingEk := some pe' } x.bs rest' (ct1ReceivedPolyCapBound x))
        (WppPost (chunkedCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_303).base + 260#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s
      (ct1ReceivedLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (ct1ReceivedPolyCapBound x))
      (WppPost (chunkedCt1ReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  have hpush_exit := fun {s_err : State} {pe' : PolynomialEncoder} =>
    @ct1Received_push_err_exit_cl_placed _ M A lim H hPushCall x st R s0 s_err
      { m with sendingEk := some pe' }
  refine ct1Received_tag2_init_step_budget_placed hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs ?_
  clear hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs s
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1
  obtain ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_pe : PolyEncoderMergeGhost :=
    ⟨iwt, x.msgPtr + 104#64, m.sendingEk.getD default, x.bufRef, x.slot, restPtr, rest⟩
  have hpe_cap : polyEncoderCapBound x_pe ≤ ct1ReceivedPolyCapBound x := by
    dsimp only [polyEncoderCapBound, x_pe]
    rw [optPolyEncoder_getD_default_pts_len, optPolyEncoder_getD_default_polys_len]
    exact hcap_bound
  apply sepWPpLscro_of_vm (mid := lsmpl.base 297)
  by_vm_steps
    (conv => arg 4; rw [spqrPoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      chunkedBelow_eq_poly s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_pe, M.stepEvents evs st))
      (ret_pc := blkBase + 300#64) hPolyCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [polyEncoderMergeSpec, polyEncoderMergeSpecOfEnv, x_pe]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1, setWidth8_ofNat64_wt],
        by simp only [arm64_norm, wp_norm, hx20_1],
        by simp only [arm64_norm, wp_norm, hx19_1],
        by rw [optPolyEncoder_getD_default_pts_len]; exact hpts_lt,
        by rw [optPolyEncoder_getD_default_polys_len]; exact hpolys_lt,
        fitsEnv_polyEncoderMerge_of_spqr (x_poly := x_pe) (by dsimp only [x_pe]; omega)
          hrest_le hpe_cap hevs hFit⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases hpe_res : (mergeMessage PolynomialEncoder.mergeField
        (codecWireTypeToProto iwt) (m.sendingEk.getD default) rest 98).toOption with
    | none =>
      have hnone := hnone_of_pe hpe_res
      apply sepWPpLscro_of_vm (mid := blkBase + 444#64)
      by_vm_steps
        (conv => arg 4; simp only [polyEncoderMergeSpec, polyEncoderMergeSpecOfEnv,
          PolyEncoderMergePostEnv, x_pe, hpe_res,
          memRegion_48_split_128 s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0
        apply SepWP.exists_elim; intro evs_p
        apply SepWP.exists_elim; intro pe'
        apply SepWP.exists_elim; intro n_err
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_p
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hn_err
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1, protoPolynomialEncoderAt_eq_pb,
          ← chunkedBelow_eq_poly s0.sp])
        have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold
          (optUnchunkedEkSentCt1ReceivedPBCapAt_entails_optEkSentCt1ReceivedPBAt
            A.repAlloc x.msgPtr rest.length m.uc)
          (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (Nat.le_refl (6 * (x.bs.length - rest.length) + (2 * rest.length + 2)))
            hevs (polyMergeLoopEnv_to_spqr hrest_le hpe_cap hevs_p))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply sepWPpLscro_of_vm (mid := blkBase + 508#64)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm3 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm3]
        apply SepWPpLscro.weaken_pre
          (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
            decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
            memRegion (s0.sp - 120#64) 40 ∗ chunkedBelow s0.sp ∗
            ct1ReceivedErrFrame A lim st
              (6 * (x.bs.length - rest.length) + (2 * rest.length + 2))
              (ct1ReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { m with sendingEk := some pe' } x.bs)
          (by dsimp only [ct1ReceivedErrFrame, chunkedCt1ReceivedPBAt, optPolynomialEncoderPBAt];
              sep_entail)
        exact hpush_exit hFit hnone (by omega) (by omega : n_err ≤ 2) hsm0 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hspm])
          ⟨by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨pe', rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hpe_res
      apply sepWPpLscro_of_vm (mid := blkBase + 192#64)
      by_vm_steps
        (conv => arg 4; simp only [polyEncoderMergeSpec, polyEncoderMergeSpecOfEnv,
          PolyEncoderMergePostEnv, x_pe, hpe_res,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_p
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_p
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1, protoPolynomialEncoderAt_eq_pb,
          ← chunkedBelow_eq_poly s0.sp])
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold
          (optUnchunkedEkSentCt1ReceivedPBCapAt_mono A.repAlloc x.msgPtr m.uc hrest'_le)
          (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (by omega : 6 * (x.bs.length - rest.length) + 2 * (rest.length - rest'.length) ≤
              6 * (x.bs.length - rest'.length))
            hevs (polyMergeLoopEnv_to_spqr hrest_le hpe_cap hevs_p))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := ct1ReceivedLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { m with sendingEk := some pe' } x.bs rest' (ct1ReceivedPolyCapBound x))
          (by dsimp only [ct1ReceivedLoopPre, chunkedCt1ReceivedPBCapAt, optPolynomialEncoderPBAt];
              sep_entail)
        exact hcont pe' rest' _ hpe_res
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          ⟨by simp only [arm64_norm, wp_norm, hx23_m],
           by simp only [arm64_norm, wp_norm, hx24_m],
           by simp only [arm64_norm, wp_norm, hx25_m],
           ⟨by simp only [arm64_norm, wp_norm, hx26_m],
            by simp only [arm64_norm, wp_norm, hx27_m],
            by simp only [arm64_norm, wp_norm, hx28_m],
            by simp only [arm64_norm, wp_norm, hvregs_m]⟩⟩

end Placed

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedBudgetAux2
