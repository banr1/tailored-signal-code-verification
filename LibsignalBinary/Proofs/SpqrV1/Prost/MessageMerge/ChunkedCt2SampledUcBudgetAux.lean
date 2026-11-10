/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledUc
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Shared Budget Combinators and Inner-Exit Lemmas for `Chunked*Budget`

Provides:
1. `SepWPpLscro` + `VmPreserved` stepping and panic-free budget call combinators
   (`sepWPpLscro_of_vm`, `sepWPpLscro_of_ret_vm`, `WppPanicFalse`, `call_budget`,
   `call_budget_lscro`).
2. `SpqrMergeIterEnv` / `SpqrMergeLoopEnv` embedding lemmas for `DecodeErrorFromEnv`,
   `DecodeErrorPushEnv`, and `AuthMergeLoopEnv`, together with `FitsEnv` splitting helpers.
3. Budget-threaded loop preconditions, error frames, and placed exit lemmas for
   `Chunked.Ct2Sampled::merge` (Block `301`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledUcBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr
  (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk IsDropSuffix
   pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialEncoder ProtoAuthenticator V1State)
open CryptoVerification.SpqrV1.ProtoRepr
  (authenticatorPBAt ct2SentPBAt optAuthenticatorPBAt optCt2SentPBAt optPolynomialEncoderPBAt
   unchunked2At)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (cap_add_one_beq_zero_false cap_add_one_bne_zero_true
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Auth
  (WppPost authenticatorPBCapAt default_cells_entails_authenticatorPBCapAt
   memRegion_40_cells optAuthenticatorPBCapAt setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedCt2SampledMergeGhost ChunkedInl10CalleeSaved SepWPpLscro
   authenticatorPBCapAt_entails_cmn_ct2 bv64_add_zero bv64_sub_zero
   chunkedCt2SampledMerge_fnOff chunkedCt2SampledPBAt chunkedCt2SampledPBAt_entails_exists
   chunkedCt2SampledPBCapAt chunkedInlBelowStack chunkedInlBelow_authMerge
   chunkedInlBelow_authMerge_entails chunkedInlBelow_decodeErrorHook
   chunkedInlBelow_decodeErrorHook_entails chunkedInlSavedRegs10 chunkedInlStack
   cmn_entails_authenticatorPBCapAt_ct2 cmp_len_limit_of_eq cmp_len_limit_of_lt
   codecWireTypeToProto decodeErrorWith_le3_ct2 iwt_cbnz_true_of_ne_varint
   memRegion8_memRegion40_entails_48_160 memRegion_48_cells1_160 memRegion_48_wtErr160
   optCt2SentPBCapAt pointsTo64_memRegion40_entails_48_160 proto_mergeMessage_suffix
   stackAt_chunkedInl10_epilogue unchunked2CapAt
   unchunked2CapAt_entails_chunkedCt2SampledPBAt wtErr160_entails_memRegion40)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_301 blkPl_301)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget
  (AuthMergeEnv AuthMergeLoopEnv AuthMergePostEnv authMergeSpec authMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (FitsEnv.spqrMergeLoop_head FitsEnv.spqrMergeLoop_split SpqrMergeIterEnv SpqrMergeLoopEnv
   decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedCt2SampledMergeEnv ChunkedCt2SampledMergePostEnv chunkedCt2SampledMergeSpec
   chunkedCt2SampledMergeSpecOfEnv ct2SampledPolyCapBound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse authMergeLoopEnv_to_spqr call_budget_lscro
   decodeErrorFromEnv_to_spqr decodeErrorPushEnv_to_spqr
   fitsEnv_authMerge_of_spqr fitsEnv_decodeErrorFrom_of_spqr fitsEnv_decodeErrorPush_of_spqr
   pool_entails_spqrPoolAt_append pool_entails_spqrPoolAt_snoc pool_spqr_mono
   sepWPpLscro_of_ret_vm sepWPpLscro_of_vm spqrPoolAt spqrPoolAt_of_vmPreserved
   vmPreserved_setMem_same)

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedCt2SampledMerge_fnOff

/-! ## Budget Preconditions, Error Frame, and Placed Exits for `Chunked.Ct2Sampled::merge` -/

/-- Budget-threaded outer loop-header separation-logic bundle at `+0x0a8` (`entry + 168#64`). -/
def chunkedCt2SampledLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Chunked.Ct2Sampled) (bs cur : List (BitVec 8)) (polyBound : Nat) : SepProp :=
  spqrPoolAt A lim st (6 * (bs.length - cur.length)) bs.length polyBound s ∗
    chunkedCt2SampledPBCapAt A.repAlloc msgPtr cur.length m ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur

/-- Budget-threaded inner `Unchunked.Ct2Sent` loop-header bundle at `+0x198` (`entry + 412#64`). -/
def chunkedCt2SampledUcLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64)
    (hdr : Option PolynomialEncoder) (uc : V1State.Unchunked.Ct2Sent)
    (bs cur : List (BitVec 8)) (polyBound : Nat) : SepProp :=
  spqrPoolAt A lim st (6 * (bs.length - cur.length)) bs.length polyBound s ∗
    optPolynomialEncoderPBAt A.repAlloc msgPtr hdr ∗
    unchunked2CapAt A.repAlloc (msgPtr + 0x38#64) cur.length uc.epoch uc.auth ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur

/-- Budget-threaded error-exit separation-logic bundle at fuel `f` (`f ≤ 6 * bs.length + 12`). -/
def chunkedCt2SampledErrFrame {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (f polyBound : Nat) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Chunked.Ct2Sampled) (bs : List (BitVec 8)) : SepProp :=
  spqrPoolAt A lim st f bs.length polyBound s ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗ chunkedCt2SampledPBAt A.repAlloc msgPtr m ∗
    (bufRef ↦₆₄ slot) ∗ memRegion slot 16 ∗ (ptr ↦ₛ bs)

private theorem ct2_err_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (x : ChunkedCt2SampledMergeGhost)
    (s0 s sf : State) (m : V1State.Chunked.Ct2Sampled) (err : BitVec 64)
    (n f : Nat) (evs : List AllocEvent)
    (hnone : (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
      V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hvm : VmPreserved s sf) (hf : f ≤ 6 * x.bs.length + 12) (hn : n ≤ 3) (herr : err ≠ 0#64)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = err)
    (hevs : SpqrMergeLoopEnv f x.bs.length (ct2SampledPolyCapBound x) evs) :
    stackAt s0.sp chunkedInlStack ∗
      (decodeErrorAtStackLen A.repAlloc err n ∗
        (chunkedCt2SampledPBAt A.repAlloc x.msgPtr m ∗
          ((x.bufRef ↦₆₄ x.slot) ∗
            (memRegion x.slot 16 ∗ ((x.ptr ↦ₛ x.bs) ∗ A.pool lim (M.stepEvents evs st) s))))) ⊢
    (chunkedCt2SampledMergeSpec A lim).post (x, st) s0 sf := by
  dsimp only [chunkedCt2SampledMergeSpec, chunkedCt2SampledMergeSpecOfEnv,
    ChunkedCt2SampledMergePostEnv]
  rw [hnone, htr, hx0]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp chunkedInlStack ∗
      (decodeErrorAtStackLen A.repAlloc err n ∗
        (chunkedCt2SampledPBAt A.repAlloc x.msgPtr m ∗
          ((x.bufRef ↦₆₄ x.slot) ∗
            (memRegion x.slot 16 ∗ ((x.ptr ↦ₛ x.bs) ∗ A.pool lim (M.stepEvents evs st) s))))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (stackAt s0.sp chunkedInlStack ∗
          (decodeErrorAtStackLen A.repAlloc err n ∗
            (chunkedCt2SampledPBAt A.repAlloc x.msgPtr m ∗
              (memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)))))))) ?_
  exact sepConj_mono_right (sepConj_mono (pool_spqr_mono A lim st hvm hf hevs)
    (sepConj_mono_right (Entails.pure_right herr
      (sepConj_mono (decodeErrorWith_le3_ct2 A.repAlloc err hn)
        (sepConj_mono_left (chunkedCt2SampledPBAt_entails_exists A.repAlloc x.msgPtr m))))))

section Placed

set_option quotPrecheck false in
local notation "entry" => (blkPl_301).base

theorem chunkedCt2Sampled_ret_err_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {m : V1State.Chunked.Ct2Sampled} {s : State} {err : BitVec 64} {n f : Nat}
    (hnone : (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
      V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f ≤ 6 * x.bs.length + 12)
    (hn : n ≤ 3) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_301).base + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = err)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err n ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        memRegion (s0.sp - 128#64) 48 ∗
        chunkedCt2SampledErrFrame A lim st f (ct2SampledPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  apply sepWPpLscro_of_ret_vm
  by_vm_steps
    (conv => arg 4; simp only [chunkedCt2SampledErrFrame, spqrPoolAt, chunkedInlSavedRegs10,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm, arm64_norm, hsp])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
    refine ⟨fun hm => Satisfies.of_entails hm (sepConj_mono_left ?_),
      by simp only [arm64_norm, wp_norm, hsp],
      by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx27, hx28, hvregs]⟩
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (ct2_err_exit_entails A lim st x s0 s _ m err n f evs hnone hvm hf hn herr
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm, hx0]) hevs)

theorem chunkedCt2Sampled_from_err_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {m : V1State.Chunked.Ct2Sampled} {s : State} {w : BitVec 64} {f : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hnone : (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
      V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f + 1 ≤ 6 * x.bs.length + 12)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_301).base + 120#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedCt2SampledErrFrame A lim st f (ct2SampledPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hret := @chunkedCt2Sampled_ret_err_exit_placed _ M A lim H x st R s0 m
  apply sepWPpLscro_of_vm (mid := lsmpl.base 261)
  by_vm_steps
    (conv => arg 4; rw [chunkedCt2SampledErrFrame, spqrPoolAt, chunkedInlBelow_decodeErrorHook s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (s0.sp - 128#64, w, M.stepEvents evs st))
      (ret_pc := entry + 128#64) hFromCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeErrorFromBudgetSpec]; simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp]; try rfl)
      (And.intro hw (fitsEnv_decodeErrorFrom_of_spqr hf hevs hFit))
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp, hx27, hx28, hvregs]
      at hpcm hspm hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 128#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeErrorFromBudgetSpec,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_f
      apply SepWP.pure_elim; rintro ⟨⟨hsm0, htrm⟩, hevs_f⟩
      apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
      apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
      apply SepWP.fold
        (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm) (Nat.le_refl (f + 1))
          hevs (decodeErrorFromEnv_to_spqr hevs_f))
        (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          chunkedCt2SampledErrFrame A lim st (f + 1) (ct2SampledPolyCapBound x)
            s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
        (by dsimp only [chunkedCt2SampledErrFrame]; sep_entail)
      exact hret hnone hf (by decide : 0 ≤ 3) hsm0 hsp_align
        (by simp only [arm64_norm, wp_norm, hpcm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm, htr])
        (by simp only [arm64_norm, wp_norm])
        ⟨by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedCt2Sampled_push_ret_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {m : V1State.Chunked.Ct2Sampled} {s : State} {err : BitVec 64} {n f : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hnone : (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
      V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f + 1 ≤ 6 * x.bs.length + 12)
    (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_301).base + 732#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err n ∗
        memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedCt2SampledErrFrame A lim st f (ct2SampledPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hret := @chunkedCt2Sampled_ret_err_exit_placed _ M A lim H x st R s0 m
  apply sepWPpLscro_of_vm (mid := lsmpl.base 257)
  (conv => arg 4; rw [chunkedCt2SampledErrFrame, spqrPoolAt, chunkedInlBelow_decodeErrorHook s0.sp])
  (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
  apply SepWP.exists_elim; intro evs
  apply SepWP.pure_elim; intro hevs
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm1 => ?_⟩
  refine call_budget_lscro (x := (s0.sp - 128#64, err, n, M.stepEvents evs st))
    (ret_pc := entry + 736#64) hPushCall
    (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
    (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
    (by simp only [arm64_norm, wp_norm])
    (by dsimp only [decodeErrorPushMergeBudgetSpec]; simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp, hx0]; try rfl)
    (And.intro (by omega) (fitsEnv_decodeErrorPush_of_spqr (by omega) hf hevs hFit))
    (by sep_focus) ?_
  intro sm hpcm hrunm hspm hcsm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp, hx27, hx28, hvregs]
    at hpcm hspm hx27_m hx28_m hvregs_m
  apply sepWPpLscro_of_vm (mid := entry + 128#64)
  by_vm_steps
    (conv => arg 4; simp only [decodeErrorPushMergeBudgetSpec,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
    apply SepWP.exists_elim; intro evs_p
    apply SepWP.pure_elim; rintro ⟨htrm, hevs_p⟩
    apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
    apply SepWP.fold
      (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm) (Nat.le_refl (f + 1))
        hevs (decodeErrorPushEnv_to_spqr (by omega) hevs_p))
      (by sep_focus)
    wp_steps
    apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
    rw [← spqrPoolAt_of_vmPreserved hvm2]
    apply SepWPpLscro.weaken_pre
      (P' := decodeErrorAtStackLen A.repAlloc err (n + 1) ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
        chunkedCt2SampledErrFrame A lim st (f + 1) (ct2SampledPolyCapBound x)
          s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [chunkedCt2SampledErrFrame]; sep_entail)
    exact hret hnone hf (by omega : n + 1 ≤ 3) herr hsp_align
      (by simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm, hrunm])
      (by simp only [arm64_norm, wp_norm, hspm])
      (by simp only [arm64_norm, wp_norm, htrm, htr])
      (by simp only [arm64_norm, wp_norm])
      ⟨by simp only [arm64_norm, wp_norm, hx27_m],
       by simp only [arm64_norm, wp_norm, hx28_m],
       by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedCt2Sampled_uc_push_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {m : V1State.Chunked.Ct2Sampled} {s : State} {err : BitVec 64} {n f : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hnone : (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
      V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f + 1 ≤ 6 * x.bs.length + 12)
    (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_301).base + 700#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err n ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        memRegion (s0.sp - 128#64) 48 ∗
        chunkedCt2SampledErrFrame A lim st f (ct2SampledPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hpush := @chunkedCt2Sampled_push_ret_exit_placed _ M A lim H hPushCall x st R s0 m
  apply sepWPpLscro_of_vm (mid := entry + 704#64)
  by_vm_steps
    (conv => arg 4; rw [chunkedCt2SampledErrFrame, memRegion_48_cells1_160 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, hx1])
    apply SepWP.exists_elim; intro v_stk0
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    rw [← spqrPoolAt_of_vmPreserved hvm1]
    apply sepWPpLscro_of_vm (mid := entry + 732#64)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm2 => ?_⟩
    rw [← spqrPoolAt_of_vmPreserved hvm2]
    apply SepWPpLscro.weaken_pre
      (P' := ((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err n ∗
        memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedCt2SampledErrFrame A lim st f (ct2SampledPolyCapBound x)
          s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [chunkedCt2SampledErrFrame]; sep_entail)
    exact hpush hFit hnone hf hn herr hsp_align
      (by simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [arm64_norm, wp_norm, hsp])
      (by simp only [arm64_norm, wp_norm, htr])
      (by simp only [arm64_norm, wp_norm, hsp])
      ⟨by simp only [arm64_norm, wp_norm, hx27],
       by simp only [arm64_norm, wp_norm, hx28],
       by simp only [arm64_norm, wp_norm, hvregs]⟩

theorem chunkedCt2Sampled_uc_from_push_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {m : V1State.Chunked.Ct2Sampled} {s : State} {w : BitVec 64} {f : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hnone : (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
      V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f + 2 ≤ 6 * x.bs.length + 12)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_301).base + 688#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedCt2SampledErrFrame A lim st f (ct2SampledPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hpush := @chunkedCt2Sampled_uc_push_exit_placed _ M A lim H hPushCall x st R s0 m
  apply sepWPpLscro_of_vm (mid := lsmpl.base 261)
  by_vm_steps
    (conv => arg 4; rw [chunkedCt2SampledErrFrame, spqrPoolAt, chunkedInlBelow_decodeErrorHook s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (s0.sp - 128#64, w, M.stepEvents evs st))
      (ret_pc := entry + 696#64) hFromCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeErrorFromBudgetSpec]; simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp]; try rfl)
      (And.intro hw (fitsEnv_decodeErrorFrom_of_spqr (by omega) hevs hFit))
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp, hx27, hx28, hvregs]
      at hpcm hspm hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 700#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeErrorFromBudgetSpec,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_f
      apply SepWP.pure_elim; rintro ⟨⟨hsm0, htrm⟩, hevs_f⟩
      apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
      apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
      apply SepWP.fold
        (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm) (Nat.le_refl (f + 1))
          hevs (decodeErrorFromEnv_to_spqr hevs_f))
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          chunkedCt2SampledErrFrame A lim st (f + 1) (ct2SampledPolyCapBound x)
            s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
        (by dsimp only [chunkedCt2SampledErrFrame]; sep_entail)
      exact hpush hFit hnone (by omega) (by decide : 0 ≤ 2) hsm0 hsp_align
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm, htr])
        (by simp only [arm64_norm, wp_norm])
        ⟨by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedCt2Sampled_uc_field_push_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {m : V1State.Chunked.Ct2Sampled} {s : State} {err : BitVec 64} {n f : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hnone : (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
      V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f + 2 ≤ 6 * x.bs.length + 12)
    (hn : n ≤ 1) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_301).base + 924#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err n ∗
        memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedCt2SampledErrFrame A lim st f (ct2SampledPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hpush := @chunkedCt2Sampled_uc_push_exit_placed _ M A lim H hPushCall x st R s0 m
  apply sepWPpLscro_of_vm (mid := lsmpl.base 257)
  (conv => arg 4; rw [chunkedCt2SampledErrFrame, spqrPoolAt, chunkedInlBelow_decodeErrorHook s0.sp])
  (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
  apply SepWP.exists_elim; intro evs
  apply SepWP.pure_elim; intro hevs
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm1 => ?_⟩
  refine call_budget_lscro (x := (s0.sp - 128#64, err, n, M.stepEvents evs st))
    (ret_pc := entry + 928#64) hPushCall
    (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
    (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
    (by simp only [arm64_norm, wp_norm])
    (by dsimp only [decodeErrorPushMergeBudgetSpec]; simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp, hx0]; try rfl)
    (And.intro (by omega) (fitsEnv_decodeErrorPush_of_spqr (by omega) (by omega) hevs hFit))
    (by sep_focus) ?_
  intro sm hpcm hrunm hspm hcsm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp, hx27, hx28, hvregs]
    at hpcm hspm hx27_m hx28_m hvregs_m
  apply sepWPpLscro_of_vm (mid := entry + 700#64)
  by_vm_steps
    (conv => arg 4; simp only [decodeErrorPushMergeBudgetSpec,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
    apply SepWP.exists_elim; intro evs_p
    apply SepWP.pure_elim; rintro ⟨htrm, hevs_p⟩
    apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
    apply SepWP.fold
      (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm) (Nat.le_refl (f + 1))
        hevs (decodeErrorPushEnv_to_spqr (by omega) hevs_p))
      (by sep_focus)
    wp_steps
    apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
    rw [← spqrPoolAt_of_vmPreserved hvm2]
    apply SepWPpLscro.weaken_pre
      (P' := decodeErrorAtStackLen A.repAlloc err (n + 1) ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
        chunkedCt2SampledErrFrame A lim st (f + 1) (ct2SampledPolyCapBound x)
          s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [chunkedCt2SampledErrFrame]; sep_entail)
    exact hpush hFit hnone (by omega) (by omega : n + 1 ≤ 2) herr hsp_align
      (by simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm, hrunm])
      (by simp only [arm64_norm, wp_norm, hspm])
      (by simp only [arm64_norm, wp_norm, htrm, htr])
      (by simp only [arm64_norm, wp_norm])
      ⟨by simp only [arm64_norm, wp_norm, hx27_m],
       by simp only [arm64_norm, wp_norm, hx28_m],
       by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedCt2Sampled_uc_tag1_wt_err_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialEncoder} {uc : V1State.Unchunked.Ct2Sent}
    {rest : List (BitVec 8)} {iwt : WireType}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hiwt : iwt ≠ .varint) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone : (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
      V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hpc : s.pc = (blkPl_301).base + 524#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (chunkedCt2SampledUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        hdr uc x.bs rest (ct2SampledPolyCapBound x))
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hcbnz_wt : (BitVec.ofNat 64 iwt.toNat == 0#64) = false := iwt_cbnz_true_of_ne_varint hiwt
  have hfpush := @chunkedCt2Sampled_uc_field_push_exit_placed _ M A lim H hPushCall x st R s0
    { sendingCt2 := hdr, uc := some uc }
  apply sepWPpLscro_of_vm (mid := lsmpl.base 261)
  by_vm_steps
    (conv => arg 4; rw [chunkedCt2SampledUcLoopPre, spqrPoolAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt,
      chunkedInlBelow_decodeErrorHook s0.sp, memRegion_48_wtErr160 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro b_wt1
    apply SepWP.exists_elim; intro b_wt0
    apply SepWP.exists_elim; intro v_wt0
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (unchunked2CapAt_entails_chunkedCt2SampledPBAt A.repAlloc x.msgPtr rest.length hdr uc) (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (s0.sp - 128#64, 0x8000000000000006#64, M.stepEvents evs st))
      (ret_pc := entry + 852#64) hFromCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeErrorFromBudgetSpec]; simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp]; try rfl)
      (And.intro (by decide) (fitsEnv_decodeErrorFrom_of_spqr (by omega) hevs hFit))
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp, hx27, hx28, hvregs]
      at hpcm hspm hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 884#64)
    (conv => arg 4; simp only [decodeErrorFromBudgetSpec, memRegion_48_cells1_160 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
    apply SepWP.exists_elim; intro evs_f
    apply SepWP.exists_elim; intro v_stk0
    apply SepWP.pure_elim; rintro ⟨⟨hsm0, htrm⟩, hevs_f⟩
    apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
    apply SepWP.fold
      (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
        (Nat.le_refl (6 * (x.bs.length - rest.length) + 1))
        hevs (decodeErrorFromEnv_to_spqr hevs_f))
      (by sep_focus)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm2 => ?_⟩
    rw [← spqrPoolAt_of_vmPreserved hvm2]
    apply sepWPpLscro_of_vm (mid := entry + 924#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm3 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm3]
      apply SepWPpLscro.weaken_pre
        (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
          decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
          memRegion (s0.sp - 120#64) 40 ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
          chunkedCt2SampledErrFrame A lim st (6 * (x.bs.length - rest.length) + 1)
            (ct2SampledPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { sendingCt2 := hdr, uc := some uc } x.bs)
        (by dsimp only [chunkedCt2SampledErrFrame]; sep_entail)
      exact hfpush hFit hnone (by omega) (by decide : 0 ≤ 1) hsm0 hsp_align
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm, htr])
        (by simp only [arm64_norm, wp_norm, hspm])
        ⟨by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedCt2Sampled_uc_auth_init_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialEncoder} {uc : V1State.Unchunked.Ct2Sent} {rest : List (BitVec 8)}
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_301).base + 504#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s.trace →
      s'.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) →
      s'.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) →
      s'.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) →
      s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) →
      s'.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s'
        (optPolynomialEncoderPBAt A.repAlloc x.msgPtr hdr ∗
          authenticatorPBCapAt A.repAlloc (x.msgPtr + 0x38#64) rest.length (uc.auth.getD default) ∗
          ((x.msgPtr + 0x68#64) ↦₆₄ uc.epoch) ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
          memRegion (s0.sp - 128#64) 48 ∗
          chunkedInlSavedRegs10 s0.sp s0 ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ct2SampledPolyCapBound x) s')
        (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_301).base + 480#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (chunkedCt2SampledUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        hdr uc x.bs rest (ct2SampledPolyCapBound x))
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  rcases hauth : uc.auth with _ | auth
  · rw [hauth] at hcont
    apply sepWPpLscro_of_vm (mid := entry + 504#64)
    by_vm_steps
      (conv => arg 4; rw [chunkedCt2SampledUcLoopPre, unchunked2CapAt, hauth, optAuthenticatorPBCapAt,
        memRegion_40_cells (x.msgPtr + 0x38#64)])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro w1
      apply SepWP.exists_elim; intro w2
      apply SepWP.exists_elim; intro w3
      apply SepWP.exists_elim; intro w4
      apply SepWP.exists_elim; intro w5
      wp_steps
      have hdef := default_cells_entails_authenticatorPBCapAt A.repAlloc (x.msgPtr + 0x38#64) rest.length
      simp only [arm64_norm] at hdef
      apply SepWP.fold hdef (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm]
      apply SepWPpLscro.weaken_pre
        (P' := optPolynomialEncoderPBAt A.repAlloc x.msgPtr hdr ∗
          authenticatorPBCapAt A.repAlloc (x.msgPtr + 0x38#64) rest.length (Option.getD none default) ∗
          ((x.msgPtr + 0x68#64) ↦₆₄ uc.epoch) ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
          memRegion (s0.sp - 128#64) 48 ∗
          chunkedInlSavedRegs10 s0.sp s0 ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ct2SampledPolyCapBound x) _)
        (Entails.of_eq (by dsimp only [Option.getD]; sep_ac_rfl))
      exact hcont _ (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrun])
        (by simp only [arm64_norm, wp_norm, hsp])
        (by try simp only [arm64_norm, wp_norm])
        (by try simp only [arm64_norm, wp_norm])
        (by try simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx20])
        (by try simp only [arm64_norm, wp_norm])
        (by try simp only [arm64_norm, wp_norm])
        (by try simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx24])
        (by try simp only [arm64_norm, wp_norm])
        (by try simp only [arm64_norm, wp_norm])
        ⟨by simp only [arm64_norm, wp_norm, hx27],
         by simp only [arm64_norm, wp_norm, hx28],
         by simp only [arm64_norm, wp_norm, hvregs]⟩
  · rw [hauth] at hcont
    apply sepWPpLscro_of_vm (mid := entry + 504#64)
    by_vm_steps
      (conv => arg 4; rw [chunkedCt2SampledUcLoopPre, unchunked2CapAt, hauth, optAuthenticatorPBCapAt])
      (conv => arg 4; simp only [sepConj_assoc, arm64_norm])
      have hcmn_in := authenticatorPBCapAt_entails_cmn_ct2 A.repAlloc (x.msgPtr + 0x38#64) rest.length auth
      simp only [arm64_norm] at hcmn_in
      apply SepWP.fold hcmn_in (by sep_focus)
      wp_simp_pre [sepExists_sepConj_left, sepConj_assoc, arm64_norm]
      apply SepWP.exists_elim; intro cap_ik
      apply SepWP.exists_elim; intro ptr_ik
      apply SepWP.pure_elim; rintro ⟨hcap_lt, hcap_ik⟩
      have hcmn1 := cap_add_one_beq_zero_false hcap_lt
      have hcmn2 := cap_add_one_bne_zero_true hcap_lt
      wp_steps
      have hcmn_out := cmn_entails_authenticatorPBCapAt_ct2 A.repAlloc (x.msgPtr + 0x38#64) rest.length auth cap_ik ptr_ik hcap_ik
      simp only [arm64_norm] at hcmn_out
      apply SepWP.fold hcmn_out (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm]
      apply SepWPpLscro.weaken_pre
        (P' := optPolynomialEncoderPBAt A.repAlloc x.msgPtr hdr ∗
          authenticatorPBCapAt A.repAlloc (x.msgPtr + 0x38#64) rest.length (Option.getD (some auth) default) ∗
          ((x.msgPtr + 0x68#64) ↦₆₄ uc.epoch) ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
          memRegion (s0.sp - 128#64) 48 ∗
          chunkedInlSavedRegs10 s0.sp s0 ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ct2SampledPolyCapBound x) _)
        (Entails.of_eq (by dsimp only [Option.getD]; sep_ac_rfl))
      exact hcont _ (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrun])
        (by simp only [arm64_norm, wp_norm, hsp])
        (by try simp only [arm64_norm, wp_norm])
        (by try simp only [arm64_norm, wp_norm])
        (by try simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx20])
        (by try simp only [arm64_norm, wp_norm])
        (by try simp only [arm64_norm, wp_norm])
        (by try simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx24])
        (by try simp only [arm64_norm, wp_norm])
        (by try simp only [arm64_norm, wp_norm])
        ⟨by simp only [arm64_norm, wp_norm, hx27],
         by simp only [arm64_norm, wp_norm, hx28],
         by simp only [arm64_norm, wp_norm, hvregs]⟩

theorem chunkedCt2Sampled_uc_tag2_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hAuthCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialEncoder} {uc : V1State.Unchunked.Ct2Sent}
    {rest : List (BitVec 8)} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_auth : (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
        ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = none →
      (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
        V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (auth' : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
        ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = some (auth', rest') →
      s'.pc = (blkPl_301).base + 412#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s'
        (chunkedCt2SampledUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          hdr { uc with auth := some auth' } x.bs rest' (ct2SampledPolyCapBound x))
        (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_301).base + 480#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (chunkedCt2SampledUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        hdr uc x.bs rest (ct2SampledPolyCapBound x))
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  have hfpush := fun {auth' : ProtoAuthenticator} =>
    @chunkedCt2Sampled_uc_field_push_exit_placed _ M A lim H hPushCall x st R s0
      { sendingCt2 := hdr, uc := some { epoch := uc.epoch, auth := some auth' } }
  refine chunkedCt2Sampled_uc_auth_init_placed ?_ hpc hrun hsp hx20 hx24 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
  rw [htr] at htr1; rw [hx0] at hx0_1; rw [hx19] at hx19_1; rw [hx21] at hx21_1
  rw [hx22] at hx22_1; rw [hx23] at hx23_1; rw [hx25] at hx25_1; rw [hx26] at hx26_1
  obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply sepWPpLscro_of_vm (mid := lsmpl.base 295)
  by_vm_steps
    (conv => arg 4; rw [spqrPoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      chunkedInlBelow_authMerge s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro
      (x := (⟨iwt, x.msgPtr + 0x38#64, uc.auth.getD default, x.bufRef, x.slot, restPtr, rest⟩,
             M.stepEvents evs st))
      (ret_pc := entry + 516#64) hAuthCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [authMergeSpec, authMergeSpecOfEnv];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1, hx0_1, hx20_1, hx19_1, setWidth8_ofNat64_wt]; try rfl)
      (And.intro hrest_lt (fitsEnv_authMerge_of_spqr (errRem := 4) (byteRem := rest.length) (by omega) hrest_le hevs hFit))
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases hauth_res : (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
        ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption with
    | none =>
      have hnone := hnone_of_auth hauth_res
      apply sepWPpLscro_of_vm (mid := entry + 896#64)
      by_vm_steps
        (conv => arg 4; simp only [authMergeSpec, authMergeSpecOfEnv, AuthMergePostEnv, hauth_res,
          memRegion_48_cells1_160 s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp1])
        apply SepWP.exists_elim; intro v_stk0
        apply SepWP.exists_elim; intro evs_auth
        apply SepWP.exists_elim; intro auth'
        apply SepWP.exists_elim; intro n_err
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_auth⟩, hsm0, hn_err⟩
        have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (f₃ := 6 * x.bs.length + 10) (by omega)
            hevs (authMergeLoopEnv_to_spqr hrest_le hevs_auth))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply sepWPpLscro_of_vm (mid := entry + 924#64)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm3 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm3]
        apply SepWPpLscro.weaken_pre
          (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
            decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
            memRegion (s0.sp - 120#64) 40 ∗
            stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
            chunkedCt2SampledErrFrame A lim st (6 * x.bs.length + 10) (ct2SampledPolyCapBound x)
              s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { sendingCt2 := hdr, uc := some { epoch := uc.epoch, auth := some auth' } } x.bs)
          (by dsimp only [chunkedCt2SampledErrFrame, chunkedCt2SampledPBAt,
                optCt2SentPBAt, ct2SentPBAt, unchunked2At, optAuthenticatorPBAt];
              simp only [arm64_norm]; sep_entail)
        exact hfpush hFit hnone (by omega) hn_err hsm0 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hspm])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨auth', rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hauth_res).1
      apply sepWPpLscro_of_vm (mid := entry + 412#64)
      by_vm_steps
        (conv => arg 4; simp only [authMergeSpec, authMergeSpecOfEnv, AuthMergePostEnv, hauth_res,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp1])
        apply SepWP.exists_elim; intro evs_auth
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_auth⟩, hsm0⟩
        apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (f₃ := 6 * (x.bs.length - rest'.length)) (by omega)
            hevs (authMergeLoopEnv_to_spqr (Nat.le_trans (Nat.sub_le _ _) hrest_le) hevs_auth))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := chunkedCt2SampledUcLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            hdr { uc with auth := some auth' } x.bs rest' (ct2SampledPolyCapBound x))
          (by dsimp only [chunkedCt2SampledUcLoopPre, unchunked2CapAt, optAuthenticatorPBCapAt];
              simp only [arm64_norm]; sep_entail)
        exact hcont auth' rest' _ hauth_res
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          (by simp only [arm64_norm, wp_norm, hx23_m])
          (by simp only [arm64_norm, wp_norm, hx24_m])
          (by simp only [arm64_norm, wp_norm, hx25_m])
          (by simp only [arm64_norm, wp_norm, hx26_m])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedCt2Sampled_uc_loop_le_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialEncoder} {uc : V1State.Unchunked.Ct2Sent}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hle_lim : cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hlim_lt : innerLimit < 2 ^ 63)
    (hnone_of_lt : cur.length < innerLimit →
      (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
        V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (s' : State),
      cur.length = innerLimit →
      s'.pc = (blkPl_301).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s'
        (chunkedCt2SampledLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { sendingCt2 := hdr, uc := some uc } x.bs cur (ct2SampledPolyCapBound x))
        (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_301).base + 412#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (chunkedCt2SampledUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        hdr uc x.bs cur (ct2SampledPolyCapBound x))
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = innerLimit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    apply sepWPpLscro_of_vm (mid := entry + 168#64)
    by_vm_steps
      (conv => arg 4; rw [chunkedCt2SampledUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
        sliceCursorAt])
      wp_steps
      apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm]
      apply SepWPpLscro.weaken_pre
        (P' := chunkedCt2SampledLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
          { sendingCt2 := hdr, uc := some uc } x.bs cur (ct2SampledPolyCapBound x))
        (by dsimp only [chunkedCt2SampledLoopPre, chunkedCt2SampledPBCapAt,
              optCt2SentPBCapAt, unchunked2CapAt, sliceCursorAfter]; sep_entail)
      exact hcont _ heq_lim
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrun])
        (by simp only [arm64_norm, wp_norm, hsp])
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm, hx19])
        (by simp only [arm64_norm, wp_norm, hx20])
        (by simp only [arm64_norm, wp_norm, hx21])
        (by simp only [arm64_norm, wp_norm, hx22])
        (by simp only [arm64_norm, wp_norm, hx23])
        (by simp only [arm64_norm, wp_norm, hx24])
        (by simp only [arm64_norm, wp_norm, hx25])
        ⟨by simp only [arm64_norm, wp_norm, hx27],
         by simp only [arm64_norm, wp_norm, hx28],
         by simp only [arm64_norm, wp_norm, hvregs]⟩
  · have hlt_lim : cur.length < innerLimit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone := hnone_of_lt hlt_lim
    have hfrom_push := @chunkedCt2Sampled_uc_from_push_exit_placed _ M A lim H
      hFromCall hPushCall x st R s0 { sendingCt2 := hdr, uc := some uc }
    apply sepWPpLscro_of_vm (mid := entry + 688#64)
    by_vm_steps
      (conv => arg 4; rw [chunkedCt2SampledUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
        sliceCursorAt, memRegion_48_cells1_160 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v_stk0
      wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
      apply SepWP.fold (unchunked2CapAt_entails_chunkedCt2SampledPBAt A.repAlloc x.msgPtr cur.length hdr uc) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm]
      apply SepWPpLscro.weaken_pre
        (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000008#64) ∗
          memRegion (s0.sp - 120#64) 40 ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
          chunkedCt2SampledErrFrame A lim st (6 * (x.bs.length - cur.length))
            (ct2SampledPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { sendingCt2 := hdr, uc := some uc } x.bs)
        (by dsimp only [chunkedCt2SampledErrFrame]; sep_entail)
      exact hfrom_push hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrun])
        (by simp only [arm64_norm, wp_norm, hsp])
        (by simp only [arm64_norm, wp_norm, htr])
        ⟨by simp only [arm64_norm, wp_norm, hx27],
         by simp only [arm64_norm, wp_norm, hx28],
         by simp only [arm64_norm, wp_norm, hvregs]⟩

end Placed

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledUcBudgetAux
