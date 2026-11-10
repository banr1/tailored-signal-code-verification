/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEk
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek` (Budget-Threaded, Block `338`)

Budget-threaded `[LibsignalPlacement]` contracts on `lsProg_338 (Rust.withPanics ext)` (`99`
instructions) under `UnchunkedCt1SentRecvEkEnv` (`FreeOnlyEvs`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEkPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalPlacement blkPC_338 blkPl_338 lsProg_338 lsmpl lsρ
  subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.LibsignalSpqrV1 (
  Bytes Error MlKem StatesResult mlkemValidatePkSpec spqrAuthApi
)
open CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt (
  Ct1Sent Ct1SentEkReceived
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecU8)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Auth (authenticatorAt)
open CryptoVerification.SpqrV1.Drop (
  FiveVecGhost fiveVec128HeadersAt fiveVec128HeadersAt_entails_memRegion_128
  unchunkedCt1SentAt vecCapPtrDealloc vecU8_entails_capPtr_dealloc_bound
)
open CryptoVerification.SpqrV1.States.Leaves (
  ErrBranchPreserved UnchunkedCt1SentRecvEkGhost bics_255_eq_zero_iff bv_sub_sub
  cells_16_unfold errBranchFrame fold_fiveVec128HeadersAt_err
  fold_unchunkedCt1SentEkReceivedAt fold_unchunkedRecvEkSavedCells memRegion_128_unfold_err
  slice_and_tail_entails_vecCapPtrDealloc stackAt_sub208_extHook_split
  stackAt_unchunkedRecvEk_restore stackAt_unchunkedRecvEk_split
  stackAt_unchunkedRecvEk_tail_split unchunkedCt1SentRecvEkResAt
  unchunkedRecvEkSavedCells unchunkedRecvEkStack unchunked_recv_ek_elim
  vecU8Body vecU8Tail vecU8_entails_capPtr_dealloc_bound_24
  vecU8_entails_capPtr_dealloc_bound_72 vecU8_entails_capPtr_dealloc_bound_96
  vecU8_entails_slice_and_tail vecU8_unfold_body vecU8_unfold_body_24
  vecU8_unfold_body_48 vecU8_unfold_body_72 vecU8_unfold_body_96
  words16_entails_memRegion_128 words16_sub192_entails_memRegion_128
  words3_entails_memRegion_24 wordsAt_16
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget (
  UnchunkedCt1SentRecvEkEnv UnchunkedCt1SentRecvEkPlacedOkX
  unchunkedCt1SentRecvEkSpec unchunkedCt1SentRecvEkSpecOfEnv
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg
  RustCliAllocBudget.pool_writeVReg128 RustCliAllocBudget.pool_writeVReg64
  RustCliAllocBudget.pool_writeVReg32

private def deallocSym : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
private def validatePkSym : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"

/-! ## 1. Private Sequencing & Call Helpers -/

private def deallocFreeOnlySpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

private theorem subroutine_ok_deallocFreeOnly [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

private theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

private theorem align_pre_vm {prog : Program} {target : BitVec 64} {s0 s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (h : P = P_mid)
    (hwp : SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P_mid) ∧ Q sm) := by
  subst h; exact hwp

private theorem align_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (heq : P = P_mid s)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) := by
  subst heq; exact h

private theorem seq_clean_evs {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm))
    (h2 : ∀ (evs : List AllocEvent) (sm : State),
      FreeOnlyEvs evs → sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_evs evs sm) post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨evs, hevs, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 evs sm hevs hpc hrun hQ)

private theorem sepWP_evs_nil {prog : Program} {target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs [] sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨[], FreeOnlyEvs.nil, hp, hq⟩

private theorem sepWP_evs_dealloc {prog : Program} {target : BitVec 64}
    {s : State} (sz al : Nat)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm =>
      (Pm ⊢ P_evs (rustDeallocEvents sz al) sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ =>
    ⟨rustDeallocEvents sz al, FreeOnlyEvs.singleton al sz, hp, hq⟩

private theorem vecCapPtrDealloc_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (cap ptr : BitVec 64) :
    vecCapPtrDealloc A.repAlloc cap ptr =
      if (cap == 0#64) = true then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := rfl

private theorem sepWP_close_recv_ek {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {Env : UnchunkedCt1SentRecvEkGhost F → List AllocEvent → Prop}
    {prog : Program} {x : UnchunkedCt1SentRecvEkGhost F} {st0 : M.σ}
    {s0 : State} {P R : SepProp}
    (hEnv : ∀ evs, FreeOnlyEvs evs → Env x evs)
    (h : SepWP prog (s0.readReg64 Reg.lr) s0 P (fun sf P_f =>
      ∃ evs, FreeOnlyEvs evs ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ ⌜sf.trace = s0.trace⌝ ∗
          unchunkedCt1SentRecvEkResAt A.repAlloc x.outA x.res ∗
          memRegion x.stA 128 ∗
          memRegion x.ekA 24 ∗
          A.pool lim (M.stepEvents evs st0) sf ∗
          stackAt s0.sp unchunkedRecvEkStack))) :
    SepWP prog (s0.readReg64 Reg.lr) s0 P (fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
          unchunkedCt1SentRecvEkResAt A.repAlloc x.outA x.res ∗
          memRegion x.stA 128 ∗
          memRegion x.ekA 24 ∗
          A.pool lim (M.stepEvents evs st0) sf ∗
          stackAt s0.sp unchunkedRecvEkStack) ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  refine SepWP.mono h fun sf P_f _ _ ⟨evs, hevs, hsp_f, hcs_f, hent⟩ => ⟨fun hm => ?_, hsp_f, hcs_f⟩
  refine Satisfies.mono (sepConj_mono_left (Entails.trans hent (Entails.sepExists_right evs ?_))) hm
  refine Entails.pure_left fun htr => ?_
  exact Entails.pure_right ⟨htr, hEnv evs hevs⟩ (Entails.refl _)

private theorem call_validatePk_vm {K : MlKem} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withVmPreserved (mlkemValidatePkSpec K)))
    (hdrPtr ekPtr : BitVec 64) (hdr ek : Bytes)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = hdrPtr)
    (hx1 : (s.readReg64 Reg.x1).toNat = hdr.length)
    (hx2 : s.readReg64 Reg.x2 = ekPtr)
    (hx3 : (s.readReg64 Reg.x3).toNat = ek.length)
    (hsplit : P = ((hdrPtr ↦ₛ hdr) ∗ (ekPtr ↦ₛ ek) ∗ stackAt sp_call extHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → VmPreserved s sf → sf.trace = s0.trace →
      ((sf.readReg64 .x0).setWidth 8 = 0xff#8 ↔ K.validPkBytes hdr ek = true) →
      SepWP prog target_pc sf
        (((hdrPtr ↦ₛ hdr) ∗ (ekPtr ↦ₛ ek) ∗ stackAt sp_call extHookStack) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  refine SepWP.call_subroutine_frame hcall (x := ⟨hdrPtr, hdr, ekPtr, ek⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    rw [hsplit] at hm
    dsimp only [withVmPreserved, mlkemValidatePkSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [withVmPreserved, mlkemValidatePkSpec]
    rw [hsp]
    simp only [sepConj_assoc]
    refine SepWP.pure_elim fun hvm => ?_
    refine SepWP.pure_elim fun ⟨hvalid, htr⟩ => ?_
    have hassoc :
        (hdrPtr ↦ₛ hdr) ∗ ((ekPtr ↦ₛ ek) ∗ (stackAt sp_call extHookStack ∗ Frame)) =
        ((hdrPtr ↦ₛ hdr) ∗ (ekPtr ↦ₛ ek) ∗ stackAt sp_call extHookStack) ∗ Frame := by sep_ac_rfl
    rw [hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf hvm (htr.trans htrace) hvalid

/-! ## 2. Shared Epilogues (`+344#64` and `+316#64`) -/

private theorem unchunked_recv_ek_epilogue_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (outA stA ekA : BitVec 64)
    (res : Except Error (Ct1SentEkReceived (spqrAuthApi F)))
    (w8 : BitVec 64) (st0 : M.σ) (evs_acc : List AllocEvent) (hevs_acc : FreeOnlyEvs evs_acc)
    {s0 s : State} {P : SepProp}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_338).base + 344#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      unchunkedCt1SentRecvEkResAt A.repAlloc outA res ∗
      memRegion stA 128 ∗
      memRegion ekA 24 ∗
      A.pool lim (M.stepEvents evs_acc st0) s ∗
      stackAt (s0.sp - 208#64) extHookStack ∗
      memRegion (s0.sp - 208#64) 8 ∗
      ((s0.sp - 200#64) ↦₆₄ w8) ∗
      memRegion (s0.sp - 192#64) 128 ∗
      unchunkedRecvEkSavedCells s0)) :
    SepWP ((blkPC_338).rebase (blkPl_338).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        ∃ evs, FreeOnlyEvs evs ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          (P_f ⊢ ⌜sf.trace = s0.trace⌝ ∗
            unchunkedCt1SentRecvEkResAt A.repAlloc outA res ∗
            memRegion stA 128 ∗
            memRegion ekA 24 ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackAt s0.sp unchunkedRecvEkStack)) := by
  subst hP
  refine SepWP.mono (post := fun sf P_f =>
      VmPreserved s sf ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ ⌜sf.trace = s0.trace⌝ ∗
          unchunkedCt1SentRecvEkResAt A.repAlloc outA res ∗
          memRegion stA 128 ∗
          memRegion ekA 24 ∗
          A.pool lim (M.stepEvents evs_acc st0) s ∗
          stackAt s0.sp unchunkedRecvEkStack))
    ?_ (fun sf P_f _ _ ⟨hvm, hsp_f, hcs_f, hent⟩ =>
      ⟨evs_acc, hevs_acc, hsp_f, hcs_f, by rwa [A.pool_of_vmPreserved hvm]⟩)
  by_vm_steps (
    wp_conv_pre => unfold unchunkedRecvEkSavedCells
    wp_steps
    refine SepWP.fold (fold_unchunkedRecvEkSavedCells s0) (by sep_focus) ?_
    refine SepWP.fold (stackAt_unchunkedRecvEk_restore s0 w8) (by sep_focus) ?_
    wp_done)

private theorem unchunked_recv_ek_tail_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_fo : subroutine_ok ((blkPC_338).rebase (blkPl_338).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (deallocFreeOnlySpec M A lim))
    (outA stA ekA cap ptr : BitVec 64)
    (res : Except Error (Ct1SentEkReceived (spqrAuthApi F)))
    (w8 : BitVec 64) (st0 : M.σ) (evs_acc : List AllocEvent) (hevs_acc : FreeOnlyEvs evs_acc)
    {s0 s : State} {P : SepProp}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlr0 : LsRetAddr624 (s0.readReg64 Reg.lr))
    (hpc : s.pc = (blkPl_338).base + 316#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : s.readReg64 .x1 = cap)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      unchunkedCt1SentRecvEkResAt A.repAlloc outA res ∗
      memRegion stA 128 ∗
      memRegion ekA 24 ∗
      A.live ptr cap.toNat 1 ∗
      memRegion ptr cap.toNat ∗
      A.pool lim (M.stepEvents evs_acc st0) s ∗
      stackAt (s0.sp - 208#64) extHookStack ∗
      memRegion (s0.sp - 208#64) 8 ∗
      ((s0.sp - 200#64) ↦₆₄ w8) ∗
      memRegion (s0.sp - 192#64) 128 ∗
      unchunkedRecvEkSavedCells s0)) :
    SepWP ((blkPC_338).rebase (blkPl_338).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        ∃ evs, FreeOnlyEvs evs ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          (P_f ⊢ ⌜sf.trace = s0.trace⌝ ∗
            unchunkedCt1SentRecvEkResAt A.repAlloc outA res ∗
            memRegion stA 128 ∗
            memRegion ekA 24 ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackAt s0.sp unchunkedRecvEkStack)) := by
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  subst hP
  refine seq_vm_clean (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
    (P_mid := unchunkedCt1SentRecvEkResAt A.repAlloc outA res ∗
      memRegion stA 128 ∗ memRegion ekA 24 ∗
      A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗
      A.pool lim (M.stepEvents evs_acc st0) s ∗
      stackAt s0.sp unchunkedRecvEkStack)
    (Q := fun sm => sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧
      sm.readReg64 .lr = s0.readReg64 .lr ∧ sm.trace = s0.trace ∧
      sm.readReg64 .x0 = ptr ∧ sm.readReg64 .x1 = cap ∧ sm.readReg64 .x2 = 1#64)
    ?_ ?_
  · by_vm_steps (
      wp_conv_pre => unfold unchunkedRecvEkSavedCells
      wp_steps
      refine SepWP.fold (fold_unchunkedRecvEkSavedCells s0) (by sep_focus) ?_
      refine SepWP.fold (stackAt_unchunkedRecvEk_restore s0 w8) (by sep_focus) ?_
      refine align_pre_vm (by sep_ac_rfl) ?_
      wp_done)
  · intro sm hpcm hrunm hvmm ⟨hsp_m, hcs_m, hlr_m, htr_m, hx0_m, hx1_m, hx2_m⟩
    rw [← A.pool_of_vmPreserved hvmm]
    have hsm_align : (sm.sp &&& 15#64 == 0#64) = true := by rw [hsp_m]; exact hsp0_align
    refine SepWP.mono (post := fun sf P_f =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          (P_f ⊢ ⌜sf.trace = s0.trace⌝ ∗
            unchunkedCt1SentRecvEkResAt A.repAlloc outA res ∗
            memRegion stA 128 ∗
            memRegion ekA 24 ∗
            A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) (M.stepEvents evs_acc st0)) sf ∗
            stackAt s0.sp unchunkedRecvEkStack))
      ?_ (fun sf P_f _ _ ⟨hsp_f, hcs_f, hent⟩ =>
        ⟨evs_acc ++ rustDeallocEvents cap.toNat 1,
         hevs_acc.append (FreeOnlyEvs.singleton 1 cap.toNat), hsp_f, hcs_f,
         by rwa [M.stepEvents_append]⟩)
    rcases hcs_m with ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩
    have _hlr_sm : LsRetAddr624 (sm.readReg64 .lr) := hlr_m ▸ hlr0
    wp_conv_pre => rw [stackAt_unchunkedRecvEk_tail_split s0.sp, ← hsp_m]
    wp_apply
    rw [hsp_m]
    rcases ‹AllocCallPreserved _ _› with ⟨_, _, _, _, _, _, _⟩
    refine SepWP.fold (Entails.of_eq (stackAt_unchunkedRecvEk_tail_split s0.sp).symm) (by sep_focus) ?_
    wp_done

/-! ## 3. OK Branch (`+220#64`) -/

private theorem unchunked_recv_ek_ok_branch_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_fo : subroutine_ok ((blkPC_338).rebase (blkPl_338).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (deallocFreeOnlySpec M A lim))
    (outA stA ekA hdrCap hdrPtr ekCap ekPtr : BitVec 64)
    (st : Ct1Sent (spqrAuthApi F)) (ek : Bytes)
    (res : Except Error (Ct1SentEkReceived (spqrAuthApi F)))
    (hres : res = .ok { epoch := st.epoch, auth := st.auth, es := st.es, ek := ek, ct1 := st.ct1 })
    (hhdr_le : st.hdr.length ≤ hdrCap.toNat) (hhdr_lt : hdrCap.toNat < 2 ^ 63)
    (hek_le : ek.length ≤ ekCap.toNat) (hek_lt : ekCap.toNat < 2 ^ 63) (hek_ne : ekPtr ≠ 0#64)
    (st0 : M.σ)
    {s0 s : State} {P : SepProp}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlr0 : LsRetAddr624 (s0.readReg64 Reg.lr))
    (hpc : s.pc = (blkPl_338).base + 220#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 208#64)
    (hx19 : s.readReg64 .x19 = stA) (hx20 : s.readReg64 .x20 = hdrPtr)
    (hx21 : s.readReg64 .x21 = outA) (hx22 : s.readReg64 .x22 = st.epoch)
    (hx23 : s.readReg64 .x23 = ekA)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25) (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      memRegion outA 128 ∗ authenticatorAt A.repAlloc stA st.auth ∗
      ((stA + 48#64) ↦₆₄ hdrCap) ∗ ((stA + 56#64) ↦₆₄ hdrPtr) ∗
      ((stA + 64#64) ↦₆₄ BitVec.ofNat 64 st.hdr.length) ∗
      (hdrPtr ↦ₛ st.hdr) ∗ vecU8Tail A.repAlloc hdrCap hdrPtr st.hdr ∗
      vecU8 A.repAlloc (stA + 72#64) st.es ∗ vecU8 A.repAlloc (stA + 96#64) st.ct1 ∗
      ((stA + 120#64) ↦₆₄ st.epoch) ∗
      (ekA ↦₆₄ ekCap) ∗ ((ekA + 8#64) ↦₆₄ ekPtr) ∗
      ((ekA + 16#64) ↦₆₄ BitVec.ofNat 64 ek.length) ∗
      (ekPtr ↦ₛ ek) ∗ vecU8Tail A.repAlloc ekCap ekPtr ek ∗ A.pool lim st0 s ∗
      stackAt (s0.sp - 208#64) extHookStack ∗ memRegion (s0.sp - 208#64) 8 ∗
      ((s0.sp - 200#64) ↦₆₄ st.epoch) ∗ memRegion (s0.sp - 192#64) 128 ∗
      unchunkedRecvEkSavedCells s0)) :
    SepWP ((blkPC_338).rebase (blkPl_338).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        ∃ evs, FreeOnlyEvs evs ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          (P_f ⊢ ⌜sf.trace = s0.trace⌝ ∗ unchunkedCt1SentRecvEkResAt A.repAlloc outA res ∗
            memRegion stA 128 ∗ memRegion ekA 24 ∗
            A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp unchunkedRecvEkStack)) := by
  have hdealloc_raw := hdealloc_fo
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_raw
  subst hP
  have hauth_eq : authenticatorAt A.repAlloc stA st.auth =
      (vecU8 A.repAlloc stA st.auth.rootKey ∗ vecU8 A.repAlloc (stA + 24#64) st.auth.macKey) := rfl
  wp_conv_pre => rw [hauth_eq]
  refine SepWP.fold (vecU8_unfold_body A.repAlloc stA st.auth.rootKey) (by sep_focus) ?_
  wp_pull_exists; rename_i rkCap rkPtr
  refine SepWP.fold (vecU8_unfold_body_24 A.repAlloc stA st.auth.macKey) (by sep_focus) ?_
  wp_pull_exists; rename_i mkCap mkPtr
  refine SepWP.fold (vecU8_unfold_body_72 A.repAlloc stA st.es) (by sep_focus) ?_
  wp_pull_exists; rename_i esCap esPtr
  refine SepWP.fold (vecU8_unfold_body_96 A.repAlloc stA st.ct1) (by sep_focus) ?_
  wp_pull_exists; rename_i ct1Cap ct1Ptr
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A.repAlloc hdrCap hdrPtr st.hdr hhdr_le hhdr_lt)
    (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold outA) (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.fold (cells_16_unfold (s0.sp - 192#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => simp only [wordsAt_16, arm64_norm]
  have hfold_out :
      (outA ↦₆₄ rkCap) ∗ ((outA + 8#64) ↦₆₄ rkPtr) ∗ ((outA + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
      vecU8Body A.repAlloc rkCap rkPtr st.auth.rootKey ∗
      ((outA + 24#64) ↦₆₄ mkCap) ∗ ((outA + 32#64) ↦₆₄ mkPtr) ∗ ((outA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
      vecU8Body A.repAlloc mkCap mkPtr st.auth.macKey ∗
      ((outA + 48#64) ↦₆₄ esCap) ∗ ((outA + 56#64) ↦₆₄ esPtr) ∗ ((outA + 64#64) ↦₆₄ BitVec.ofNat 64 st.es.length) ∗
      vecU8Body A.repAlloc esCap esPtr st.es ∗
      ((outA + 72#64) ↦₆₄ ekCap) ∗ ((outA + 80#64) ↦₆₄ ekPtr) ∗ ((outA + 88#64) ↦₆₄ BitVec.ofNat 64 ek.length) ∗
      (ekPtr ↦ₛ ek) ∗ vecU8Tail A.repAlloc ekCap ekPtr ek ∗
      ((outA + 96#64) ↦₆₄ ct1Cap) ∗ ((outA + 104#64) ↦₆₄ ct1Ptr) ∗ ((outA + 112#64) ↦₆₄ BitVec.ofNat 64 st.ct1.length) ∗
      vecU8Body A.repAlloc ct1Cap ct1Ptr st.ct1 ∗
      ((outA + 120#64) ↦₆₄ st.epoch) ⊢
      unchunkedCt1SentRecvEkResAt A.repAlloc outA res := by
    rw [hres]
    exact fold_unchunkedCt1SentEkReceivedAt A.repAlloc outA st ek
      rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr ct1Cap ct1Ptr hek_le hek_lt hek_ne
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  by_cases hhdr0 : (hdrCap == 0#64) = true <;>
    simp only [hhdr0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · refine SepWP.mono (post := fun sf P_f =>
        VmPreserved s sf ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          (P_f ⊢ ⌜sf.trace = s0.trace⌝ ∗ unchunkedCt1SentRecvEkResAt A.repAlloc outA res ∗
            memRegion stA 128 ∗ memRegion ekA 24 ∗
            A.pool lim st0 s ∗ stackAt s0.sp unchunkedRecvEkStack))
      ?_ (fun sf P_f _ _ ⟨hvm, hsp_f, hcs_f, hent⟩ =>
        ⟨[], FreeOnlyEvs.nil, hsp_f, hcs_f,
         by rwa [M.stepEvents_nil, A.pool_of_vmPreserved hvm]⟩)
    by_vm_steps (
      wp_steps
      refine SepWP.fold hfold_out (by sep_focus) ?_
      refine SepWP.fold (words16_entails_memRegion_128 stA
          rkCap rkPtr (BitVec.ofNat 64 st.auth.rootKey.length)
          mkCap mkPtr (BitVec.ofNat 64 st.auth.macKey.length)
          hdrCap hdrPtr (BitVec.ofNat 64 st.hdr.length)
          esCap esPtr (BitVec.ofNat 64 st.es.length)
          ct1Cap ct1Ptr (BitVec.ofNat 64 st.ct1.length) st.epoch)
        (by sep_focus) ?_
      refine SepWP.fold (words3_entails_memRegion_24 ekA ekCap ekPtr (BitVec.ofNat 64 ek.length))
        (by sep_focus) ?_
      refine SepWP.fold (words16_sub192_entails_memRegion_128 s0.sp
          rkCap rkPtr (BitVec.ofNat 64 st.auth.rootKey.length)
          mkCap mkPtr (BitVec.ofNat 64 st.auth.macKey.length)
          esCap esPtr (BitVec.ofNat 64 st.es.length)
          ekCap ekPtr (BitVec.ofNat 64 ek.length)
          ct1Cap ct1Ptr (BitVec.ofNat 64 st.ct1.length) _)
        (by sep_focus) ?_
      wp_conv_pre => unfold unchunkedRecvEkSavedCells
      wp_steps
      refine SepWP.fold (fold_unchunkedRecvEkSavedCells s0) (by sep_focus) ?_
      refine SepWP.fold (stackAt_unchunkedRecvEk_restore s0 st.epoch) (by sep_focus) ?_
      wp_done)
  · refine seq_vm_clean (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (P_mid := unchunkedCt1SentRecvEkResAt A.repAlloc outA res ∗
        memRegion stA 128 ∗ memRegion ekA 24 ∗
        A.live hdrPtr hdrCap.toNat 1 ∗ memRegion hdrPtr hdrCap.toNat ∗
        A.pool lim st0 s ∗ stackAt s0.sp unchunkedRecvEkStack)
      (Q := fun sm => sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧
        sm.readReg64 .lr = s0.readReg64 .lr ∧ sm.trace = s0.trace ∧
        sm.readReg64 .x0 = hdrPtr ∧ sm.readReg64 .x1 = hdrCap ∧ sm.readReg64 .x2 = 1#64)
      ?_ ?_
    · by_vm_steps (
        wp_steps
        refine SepWP.fold hfold_out (by sep_focus) ?_
        refine SepWP.fold (words16_entails_memRegion_128 stA
            rkCap rkPtr (BitVec.ofNat 64 st.auth.rootKey.length)
            mkCap mkPtr (BitVec.ofNat 64 st.auth.macKey.length)
            hdrCap hdrPtr (BitVec.ofNat 64 st.hdr.length)
            esCap esPtr (BitVec.ofNat 64 st.es.length)
            ct1Cap ct1Ptr (BitVec.ofNat 64 st.ct1.length) st.epoch)
          (by sep_focus) ?_
        refine SepWP.fold (words3_entails_memRegion_24 ekA ekCap ekPtr (BitVec.ofNat 64 ek.length))
          (by sep_focus) ?_
        refine SepWP.fold (words16_sub192_entails_memRegion_128 s0.sp
            rkCap rkPtr (BitVec.ofNat 64 st.auth.rootKey.length)
            mkCap mkPtr (BitVec.ofNat 64 st.auth.macKey.length)
            esCap esPtr (BitVec.ofNat 64 st.es.length)
            ekCap ekPtr (BitVec.ofNat 64 ek.length)
            ct1Cap ct1Ptr (BitVec.ofNat 64 st.ct1.length) _)
          (by sep_focus) ?_
        wp_conv_pre => unfold unchunkedRecvEkSavedCells
        wp_steps
        refine SepWP.fold (fold_unchunkedRecvEkSavedCells s0) (by sep_focus) ?_
        refine SepWP.fold (stackAt_unchunkedRecvEk_restore s0 st.epoch) (by sep_focus) ?_
        refine align_pre_vm (by sep_ac_rfl) ?_
        wp_done)
    · intro sm hpcm hrunm hvmm ⟨hsp_m, hcs_m, hlr_m, htr_m, hx0_m, hx1_m, hx2_m⟩
      rw [← A.pool_of_vmPreserved hvmm]
      have hsm_align : (sm.sp &&& 15#64 == 0#64) = true := by rw [hsp_m]; exact hsp0_align
      refine SepWP.mono (post := fun sf P_f =>
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
            (P_f ⊢ ⌜sf.trace = s0.trace⌝ ∗ unchunkedCt1SentRecvEkResAt A.repAlloc outA res ∗
              memRegion stA 128 ∗ memRegion ekA 24 ∗
              A.pool lim (M.stepEvents (rustDeallocEvents hdrCap.toNat 1) st0) sf ∗
              stackAt s0.sp unchunkedRecvEkStack))
        ?_ (fun sf P_f _ _ ⟨hsp_f, hcs_f, hent⟩ =>
          ⟨rustDeallocEvents hdrCap.toNat 1, FreeOnlyEvs.singleton 1 hdrCap.toNat, hsp_f, hcs_f, hent⟩)
      rcases hcs_m with ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩
      have _hlr_sm : LsRetAddr624 (sm.readReg64 .lr) := hlr_m ▸ hlr0
      wp_conv_pre => rw [stackAt_unchunkedRecvEk_tail_split s0.sp, ← hsp_m]
      wp_apply
      rw [hsp_m]
      rcases ‹AllocCallPreserved _ _› with ⟨_, _, _, _, _, _, _⟩
      refine SepWP.fold (Entails.of_eq (stackAt_unchunkedRecvEk_tail_split s0.sp).symm) (by sep_focus) ?_
      wp_done

/-! ## 4. Error Branch (`+88#64`) -/

private theorem unchunked_recv_ek_err_tail_164_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_fo : subroutine_ok ((blkPC_338).rebase (blkPl_338).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (deallocFreeOnlySpec M A lim))
    (outA stA ekA rkCap rkPtr mkCap mkPtr hdrCap hdrPtr esCap esPtr ct1Cap ct1Ptr : BitVec 64)
    (epoch : BitVec 64)
    (res : Except Error (Ct1SentEkReceived (spqrAuthApi F)))
    (st0 : M.σ) (evs_pre : List AllocEvent) (hevs_pre : FreeOnlyEvs evs_pre)
    {s0 s3 : State}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlr0 : LsRetAddr624 (s0.readReg64 Reg.lr))
    (hpc3 : s3.pc = (blkPl_338).base + 164#64)
    (hrun3 : s3.status = .Running)
    (herr3 : ErrBranchPreserved s0 s3 stA hdrPtr) :
    let g : FiveVecGhost :=
      ⟨⟨rkCap, rkPtr⟩, ⟨mkCap, mkPtr⟩, ⟨hdrCap, hdrPtr⟩, ⟨esCap, esPtr⟩, ⟨ct1Cap, ct1Ptr⟩⟩
    SepWP ((blkPC_338).rebase (blkPl_338).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s3
      ((fiveVec128HeadersAt stA g ∗
        vecCapPtrDealloc A.repAlloc hdrCap hdrPtr ∗ vecCapPtrDealloc A.repAlloc esCap esPtr ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr) ∗
        A.pool lim (M.stepEvents evs_pre st0) s3 ∗ stackAt (s0.sp - 208#64) allocHookStack ∗
        errBranchFrame A.repAlloc outA ekA res s0 epoch)
      (fun sf P_f =>
        ∃ evs, FreeOnlyEvs evs ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          (P_f ⊢ ⌜sf.trace = s0.trace⌝ ∗ unchunkedCt1SentRecvEkResAt A.repAlloc outA res ∗
            memRegion stA 128 ∗ memRegion ekA 24 ∗
            A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp unchunkedRecvEkStack)) := by
  intro g
  have hdealloc_raw := hdealloc_fo
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_raw
  have h_epilogue := @unchunked_recv_ek_epilogue_ret_placed _ M A lim F ext
  have h_tail := unchunked_recv_ek_tail_dealloc_placed (F := F) hdealloc_fo
  have hfsp_align : ((s0.sp - 208#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 208#64 hsp0_align (by decide)
  rcases herr3 with ⟨hsp3, hx19_3, hx20_3, hx25_3, hx26_3, hx27_3, hx28_3, htr3, hvregs_3⟩
  let st3 := M.stepEvents evs_pre st0
  refine seq_clean_evs (mid := (blkPl_338).base + 184#64)
    (P_evs := fun evs sm => (fiveVec128HeadersAt stA g ∗
      vecCapPtrDealloc A.repAlloc esCap esPtr ∗ vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr) ∗
      A.pool lim (M.stepEvents evs st3) sm ∗ stackAt (s0.sp - 208#64) allocHookStack ∗
      errBranchFrame A.repAlloc outA ekA res s0 epoch)
    (Q := fun sm => ErrBranchPreserved s0 sm stA hdrPtr) ?_ ?_
  · wp_conv_pre =>
      dsimp only [fiveVec128HeadersAt, g]
      rw [vecCapPtrDealloc_eq A hdrCap hdrPtr]
    by_cases hhdr0 : (hdrCap == 0#64) = true <;>
      simp only [hhdr0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps
      refine align_pre_st (by dsimp only [fiveVec128HeadersAt, g]; simp only [wp_norm, arm64_norm]; sep_ac_rfl) ?_
      wp_done
    · have hs3_al : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hfsp_align
      apply sepWP_evs_dealloc hdrCap.toNat 1
      wp_conv_pre => rw [← hsp3]
      wp_steps; wp_apply
      rcases ‹AllocCallPreserved _ _› with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by dsimp only [fiveVec128HeadersAt, g]; simp only [hsp3, wp_norm, arm64_norm]; sep_ac_rfl) ?_
      wp_done
  · intro evs4 s4 hevs4 hpc4 hrun4 ⟨hsp4, hx19_4, hx20_4, hx25_4, hx26_4, hx27_4, hx28_4, htr4, hvregs_4⟩
    let st4 := M.stepEvents evs4 st3
    refine seq_clean_evs (mid := (blkPl_338).base + 204#64)
      (P_evs := fun evs sm => (fiveVec128HeadersAt stA g ∗
        vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr) ∗
        A.pool lim (M.stepEvents evs st4) sm ∗ stackAt (s0.sp - 208#64) allocHookStack ∗
        errBranchFrame A.repAlloc outA ekA res s0 epoch)
      (Q := fun sm => ErrBranchPreserved s0 sm stA hdrPtr) ?_ ?_
    · wp_conv_pre =>
        dsimp only [fiveVec128HeadersAt, g]
        rw [vecCapPtrDealloc_eq A esCap esPtr]
      by_cases hes0 : (esCap == 0#64) = true <;>
        simp only [hes0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil
        simp only [M.stepEvents_nil]
        wp_steps
        refine align_pre_st (by dsimp only [fiveVec128HeadersAt, g]; simp only [wp_norm, arm64_norm]; sep_ac_rfl) ?_
        wp_done
      · have hs4_al : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hfsp_align
        apply sepWP_evs_dealloc esCap.toNat 1
        wp_conv_pre => rw [← hsp4]
        wp_steps; wp_apply
        rcases ‹AllocCallPreserved _ _› with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by dsimp only [fiveVec128HeadersAt, g]; simp only [hsp4, wp_norm, arm64_norm]; sep_ac_rfl) ?_
        wp_done
    · intro evs5 s5 hevs5 hpc5 hrun5 ⟨hsp5, hx19_5, hx20_5, hx25_5, hx26_5, hx27_5, hx28_5, htr5, hvregs_5⟩
      let st5 := M.stepEvents evs5 st4
      have hevs_all : FreeOnlyEvs (evs_pre ++ evs4 ++ evs5) :=
        (hevs_pre.append hevs4).append hevs5
      have hst_all :
          M.stepEvents evs5 (M.stepEvents evs4 (M.stepEvents evs_pre st0)) =
            M.stepEvents (evs_pre ++ evs4 ++ evs5) st0 := by
        simp only [M.stepEvents_append]
      wp_conv_pre => unfold errBranchFrame
      refine SepWP.fold (Entails.of_eq (stackAt_sub208_extHook_split s0.sp).symm)
        (by sep_focus) ?_
      wp_conv_pre =>
        dsimp only [fiveVec128HeadersAt, g]
        rw [vecCapPtrDealloc_eq A ct1Cap ct1Ptr]
      by_cases hct1_0 : (ct1Cap == 0#64) = true <;>
        simp only [hct1_0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_step; wp_step
        refine SepWP.fold (fiveVec128HeadersAt_entails_memRegion_128 stA g)
          (by dsimp only [fiveVec128HeadersAt, g]; sep_focus) ?_
        exact h_epilogue outA stA ekA res epoch st0
          (evs_pre ++ evs4 ++ evs5) hevs_all hsp0_align
          (by wp_norm_goal)
          (by wp_norm_lhs)
          (by simp only [State.sp, arm64_norm, hsp5])
          (by simp only [Reg.x25, arm64_norm, hx25_5]) (by simp only [Reg.x26, arm64_norm, hx26_5])
          (by simp only [Reg.x27, arm64_norm, hx27_5]) (by simp only [Reg.x28, arm64_norm, hx28_5])
          (by simp only [arm64_norm, htr5]) (by simp only [arm64_norm, hvregs_5])
          (by dsimp only [st3, st4, st5]; rw [hst_all]; simp only [arm64_norm, wp_norm]; sep_ac_rfl)
      · wp_step; wp_step; wp_step; wp_step
        refine SepWP.fold (fiveVec128HeadersAt_entails_memRegion_128 stA g)
          (by dsimp only [fiveVec128HeadersAt, g]; sep_focus) ?_
        exact h_tail outA stA ekA ct1Cap ct1Ptr res epoch st0
          (evs_pre ++ evs4 ++ evs5) hevs_all hsp0_align hlr0
          (by wp_norm_goal)
          (by wp_norm_lhs)
          (by simp only [State.sp, arm64_norm, hsp5])
          (by simp only [Reg.x0, arm64_norm]) (by simp only [Reg.x1, arm64_norm])
          (by simp only [Reg.x25, arm64_norm, hx25_5]) (by simp only [Reg.x26, arm64_norm, hx26_5])
          (by simp only [Reg.x27, arm64_norm, hx27_5]) (by simp only [Reg.x28, arm64_norm, hx28_5])
          (by simp only [arm64_norm, htr5]) (by simp only [arm64_norm, hvregs_5])
          (by dsimp only [st3, st4, st5]; rw [hst_all]; simp only [arm64_norm, wp_norm]; sep_ac_rfl)

private theorem unchunked_recv_ek_err_branch_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_fo : subroutine_ok ((blkPC_338).rebase (blkPl_338).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (deallocFreeOnlySpec M A lim))
    (outA stA ekA hdrCap hdrPtr ekCap ekPtr : BitVec 64)
    (st : Ct1Sent (spqrAuthApi F)) (ek : Bytes)
    (res : Except Error (Ct1SentEkReceived (spqrAuthApi F)))
    (hres : res = .error .erroneousDataReceived)
    (hhdr_le : st.hdr.length ≤ hdrCap.toNat) (hhdr_lt : hdrCap.toNat < 2 ^ 63)
    (hek_le : ek.length ≤ ekCap.toNat) (hek_lt : ekCap.toNat < 2 ^ 63)
    (st0 : M.σ)
    {s0 s : State} {P : SepProp}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlr0 : LsRetAddr624 (s0.readReg64 Reg.lr))
    (hpc : s.pc = (blkPl_338).base + 88#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 208#64)
    (hx19 : s.readReg64 .x19 = stA) (hx20 : s.readReg64 .x20 = hdrPtr)
    (hx21 : s.readReg64 .x21 = outA) (hx23 : s.readReg64 .x23 = ekA)
    (hx24 : s.readReg64 .x24 = ekPtr)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25) (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      memRegion outA 128 ∗ authenticatorAt A.repAlloc stA st.auth ∗
      ((stA + 48#64) ↦₆₄ hdrCap) ∗ ((stA + 56#64) ↦₆₄ hdrPtr) ∗
      ((stA + 64#64) ↦₆₄ BitVec.ofNat 64 st.hdr.length) ∗
      (hdrPtr ↦ₛ st.hdr) ∗ vecU8Tail A.repAlloc hdrCap hdrPtr st.hdr ∗
      vecU8 A.repAlloc (stA + 72#64) st.es ∗ vecU8 A.repAlloc (stA + 96#64) st.ct1 ∗
      ((stA + 120#64) ↦₆₄ st.epoch) ∗
      (ekA ↦₆₄ ekCap) ∗ ((ekA + 8#64) ↦₆₄ ekPtr) ∗
      ((ekA + 16#64) ↦₆₄ BitVec.ofNat 64 ek.length) ∗
      (ekPtr ↦ₛ ek) ∗ vecU8Tail A.repAlloc ekCap ekPtr ek ∗ A.pool lim st0 s ∗
      stackAt (s0.sp - 208#64) extHookStack ∗ memRegion (s0.sp - 208#64) 8 ∗
      ((s0.sp - 200#64) ↦₆₄ st.epoch) ∗ memRegion (s0.sp - 192#64) 128 ∗
      unchunkedRecvEkSavedCells s0)) :
    SepWP ((blkPC_338).rebase (blkPl_338).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        ∃ evs, FreeOnlyEvs evs ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          (P_f ⊢ ⌜sf.trace = s0.trace⌝ ∗ unchunkedCt1SentRecvEkResAt A.repAlloc outA res ∗
            memRegion stA 128 ∗ memRegion ekA 24 ∗
            A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp unchunkedRecvEkStack)) := by
  have hdealloc_raw := hdealloc_fo
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_raw
  have hfsp_align : ((s0.sp - 208#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 208#64 hsp0_align (by decide)
  subst hP
  have hauth_eq : authenticatorAt A.repAlloc stA st.auth =
      (vecU8 A.repAlloc stA st.auth.rootKey ∗ vecU8 A.repAlloc (stA + 24#64) st.auth.macKey) := rfl
  wp_conv_pre => rw [hauth_eq, stackAt_sub208_extHook_split s0.sp]
  refine SepWP.fold (memRegion_128_unfold_err outA) (by sep_focus) ?_
  wp_pull_exists; rename_i outW0 outB8
  refine SepWP.fold (vecU8_entails_capPtr_dealloc_bound A.repAlloc stA st.auth.rootKey) (by sep_focus) ?_
  wp_pull_exists; rename_i rkCap rkPtr
  wp_focus_pure; intro _hrk_lt
  refine SepWP.fold (vecU8_entails_capPtr_dealloc_bound_24 A.repAlloc stA st.auth.macKey) (by sep_focus) ?_
  wp_pull_exists; rename_i mkCap mkPtr
  wp_focus_pure; intro _hmk_lt
  refine SepWP.fold (vecU8_entails_capPtr_dealloc_bound_72 A.repAlloc stA st.es) (by sep_focus) ?_
  wp_pull_exists; rename_i esCap esPtr
  wp_focus_pure; intro _hes_lt
  refine SepWP.fold (vecU8_entails_capPtr_dealloc_bound_96 A.repAlloc stA st.ct1) (by sep_focus) ?_
  wp_pull_exists; rename_i ct1Cap ct1Ptr
  wp_focus_pure; intro _hct1_lt
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A.repAlloc hdrCap hdrPtr st.hdr hhdr_le hhdr_lt)
    (by sep_focus) ?_
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A.repAlloc ekCap ekPtr ek hek_le hek_lt)
    (by sep_focus) ?_
  refine SepWP.fold (fold_fiveVec128HeadersAt_err stA
      rkCap rkPtr mkCap mkPtr hdrCap hdrPtr (BitVec.ofNat 64 st.hdr.length)
      esCap esPtr ct1Cap ct1Ptr st.epoch)
    (by sep_focus) ?_
  let g : FiveVecGhost :=
    ⟨⟨rkCap, rkPtr⟩, ⟨mkCap, mkPtr⟩, ⟨hdrCap, hdrPtr⟩, ⟨esCap, esPtr⟩, ⟨ct1Cap, ct1Ptr⟩⟩
  have hfold_err :
      (outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 12#8) ∗ memRegion (outA + 9#64) 119 ∗
      (ekA ↦₆₄ ekCap) ∗ ((ekA + 8#64) ↦₆₄ ekPtr) ∗ ((ekA + 16#64) ↦₆₄ BitVec.ofNat 64 ek.length) ∗
      memRegion (s0.sp - 16592#64) 12288 ∗ memRegion (s0.sp - 208#64) 8 ∗
      ((s0.sp - 200#64) ↦₆₄ st.epoch) ∗ memRegion (s0.sp - 192#64) 128 ∗
      unchunkedRecvEkSavedCells s0 ⊢
      errBranchFrame A.repAlloc outA ekA res s0 st.epoch := by
    unfold errBranchFrame; rw [hres]; dsimp only [unchunkedCt1SentRecvEkResAt]
    have hek24 := words3_entails_memRegion_24 ekA ekCap ekPtr (BitVec.ofNat 64 ek.length)
    refine Entails.trans (Entails.of_eq (show _ =
      (((ekA ↦₆₄ ekCap) ∗ ((ekA + 8#64) ↦₆₄ ekPtr) ∗ ((ekA + 16#64) ↦₆₄ BitVec.ofNat 64 ek.length)) ∗
       ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 12#8) ∗ memRegion (outA + 9#64) 119 ∗
        memRegion (s0.sp - 16592#64) 12288 ∗ memRegion (s0.sp - 208#64) 8 ∗
        ((s0.sp - 200#64) ↦₆₄ st.epoch) ∗ memRegion (s0.sp - 192#64) 128 ∗
        unchunkedRecvEkSavedCells s0)) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left hek24) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  refine seq_clean_evs (mid := (blkPl_338).base + 124#64)
    (P_evs := fun evs sm => (fiveVec128HeadersAt stA g ∗
      vecCapPtrDealloc A.repAlloc rkCap rkPtr ∗ vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
      vecCapPtrDealloc A.repAlloc hdrCap hdrPtr ∗ vecCapPtrDealloc A.repAlloc esCap esPtr ∗
      vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr) ∗
      A.pool lim (M.stepEvents evs st0) sm ∗ stackAt (s0.sp - 208#64) allocHookStack ∗
      errBranchFrame A.repAlloc outA ekA res s0 st.epoch)
    (Q := fun sm => ErrBranchPreserved s0 sm stA hdrPtr) ?_ ?_
  · wp_conv_pre => rw [vecCapPtrDealloc_eq A ekCap ekPtr]
    by_cases hek0 : (ekCap == 0#64) = true <;>
      simp only [hek0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · refine seq_vm_clean (mid := (blkPl_338).base + 124#64)
        (P_mid := (fiveVec128HeadersAt stA g ∗
          vecCapPtrDealloc A.repAlloc rkCap rkPtr ∗ vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
          vecCapPtrDealloc A.repAlloc hdrCap hdrPtr ∗ vecCapPtrDealloc A.repAlloc esCap esPtr ∗
          vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr) ∗
          A.pool lim st0 s ∗ stackAt (s0.sp - 208#64) allocHookStack ∗
          errBranchFrame A.repAlloc outA ekA res s0 st.epoch)
        (Q := fun sm => ErrBranchPreserved s0 sm stA hdrPtr) ?_ ?_
      · by_vm_steps (
          wp_step; wp_step; wp_step; wp_step; wp_step
          refine SepWP.fold hfold_err (by dsimp only [noneCap]; sep_focus) ?_
          wp_steps
          refine align_pre_vm (by sep_ac_rfl) ?_
          wp_done)
      · intro sm hpcm hrunm hvmm ⟨_, _, _, _, _, _, _, _, _⟩
        rw [← A.pool_of_vmPreserved hvmm]
        apply sepWP_evs_nil
        simp only [M.stepEvents_nil]
        wp_done
    · refine seq_vm_clean (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
        (P_mid := (fiveVec128HeadersAt stA g ∗
          (A.live ekPtr ekCap.toNat 1 ∗ memRegion ekPtr ekCap.toNat) ∗
          vecCapPtrDealloc A.repAlloc rkCap rkPtr ∗ vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
          vecCapPtrDealloc A.repAlloc hdrCap hdrPtr ∗ vecCapPtrDealloc A.repAlloc esCap esPtr ∗
          vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr) ∗
          A.pool lim st0 s ∗ stackAt (s0.sp - 208#64) allocHookStack ∗
          errBranchFrame A.repAlloc outA ekA res s0 st.epoch)
        (Q := fun sc => ErrBranchPreserved s0 sc stA hdrPtr ∧
          sc.readReg64 .lr = (blkPl_338).base + 124#64 ∧
          sc.readReg64 .x0 = ekPtr ∧ sc.readReg64 .x1 = ekCap ∧ sc.readReg64 .x2 = 1#64)
        ?_ ?_
      · by_vm_steps (
          wp_step; wp_step; wp_step; wp_step; wp_step
          refine SepWP.fold hfold_err (by dsimp only [noneCap]; sep_focus) ?_
          wp_steps
          refine align_pre_vm (by sep_ac_rfl) ?_
          wp_done)
      · intro sc hpcc hrunc hvmc ⟨⟨hsp_c, hx19_c, hx20_c, hx25_c, hx26_c, hx27_c, hx28_c, htr_c, hvregs_c⟩, hlr_c, hx0_c, hx1_c, hx2_c⟩
        rw [← A.pool_of_vmPreserved hvmc]
        have hsc_al : (sc.sp &&& 15#64 == 0#64) = true := by rw [hsp_c]; exact hfsp_align
        have _hlr_sc : LsRetAddr624 (sc.readReg64 .lr) := by
          rw [hlr_c]; simp (config := { decide := true }) only [wp_norm, arm64_norm]
        apply sepWP_evs_dealloc ekCap.toNat 1
        wp_conv_pre => rw [← hsp_c]
        wp_apply
        rcases ‹AllocCallPreserved _ _› with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by simp only [hsp_c, wp_norm, arm64_norm]; sep_ac_rfl) ?_
        wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨hsp1, hx19_1, hx20_1, hx25_1, hx26_1, hx27_1, hx28_1, htr1, hvregs_1⟩
    let st1 := M.stepEvents evs1 st0
    refine seq_clean_evs (mid := (blkPl_338).base + 144#64)
      (P_evs := fun evs sm => (fiveVec128HeadersAt stA g ∗
        vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗ vecCapPtrDealloc A.repAlloc hdrCap hdrPtr ∗
        vecCapPtrDealloc A.repAlloc esCap esPtr ∗ vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr) ∗
        A.pool lim (M.stepEvents evs st1) sm ∗ stackAt (s0.sp - 208#64) allocHookStack ∗
        errBranchFrame A.repAlloc outA ekA res s0 st.epoch)
      (Q := fun sm => ErrBranchPreserved s0 sm stA hdrPtr) ?_ ?_
    · wp_conv_pre =>
        dsimp only [fiveVec128HeadersAt, g]
        rw [vecCapPtrDealloc_eq A rkCap rkPtr]
      by_cases hrk0 : (rkCap == 0#64) = true <;>
        simp only [hrk0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil
        simp only [M.stepEvents_nil]
        wp_steps
        refine align_pre_st (by dsimp only [fiveVec128HeadersAt, g]; simp only [wp_norm, arm64_norm]; sep_ac_rfl) ?_
        wp_done
      · have hs1_al : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hfsp_align
        apply sepWP_evs_dealloc rkCap.toNat 1
        wp_conv_pre => rw [← hsp1]
        wp_steps; wp_apply
        rcases ‹AllocCallPreserved _ _› with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by dsimp only [fiveVec128HeadersAt, g]; simp only [hsp1, wp_norm, arm64_norm]; sep_ac_rfl) ?_
        wp_done
    · intro evs2 s2 hevs2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, hx25_2, hx26_2, hx27_2, hx28_2, htr2, hvregs_2⟩
      let st2 := M.stepEvents evs2 st1
      refine seq_clean_evs (mid := (blkPl_338).base + 164#64)
        (P_evs := fun evs sm => (fiveVec128HeadersAt stA g ∗
          vecCapPtrDealloc A.repAlloc hdrCap hdrPtr ∗ vecCapPtrDealloc A.repAlloc esCap esPtr ∗
          vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr) ∗
          A.pool lim (M.stepEvents evs st2) sm ∗ stackAt (s0.sp - 208#64) allocHookStack ∗
          errBranchFrame A.repAlloc outA ekA res s0 st.epoch)
        (Q := fun sm => ErrBranchPreserved s0 sm stA hdrPtr) ?_ ?_
      · wp_conv_pre =>
          dsimp only [fiveVec128HeadersAt, g]
          rw [vecCapPtrDealloc_eq A mkCap mkPtr]
        by_cases hmk0 : (mkCap == 0#64) = true <;>
          simp only [hmk0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil
          simp only [M.stepEvents_nil]
          wp_steps
          refine align_pre_st (by dsimp only [fiveVec128HeadersAt, g]; simp only [wp_norm, arm64_norm]; sep_ac_rfl) ?_
          wp_done
        · have hs2_al : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hfsp_align
          apply sepWP_evs_dealloc mkCap.toNat 1
          wp_conv_pre => rw [← hsp2]
          wp_steps; wp_apply
          rcases ‹AllocCallPreserved _ _› with ⟨_, _, _, _, _, _, _⟩
          refine align_pre_st (by dsimp only [fiveVec128HeadersAt, g]; simp only [hsp2, wp_norm, arm64_norm]; sep_ac_rfl) ?_
          wp_done
      · intro evs3 s3 hevs3 hpc3 hrun3 herr3
        have hevs13 : FreeOnlyEvs (evs1 ++ evs2 ++ evs3) := (hevs1.append hevs2).append hevs3
        have hst13 : M.stepEvents evs3 st2 = M.stepEvents (evs1 ++ evs2 ++ evs3) st0 := by
          simp only [st1, st2, M.stepEvents_append]
        rw [hst13]
        exact unchunked_recv_ek_err_tail_164_placed hdealloc_fo
          outA stA ekA rkCap rkPtr mkCap mkPtr hdrCap hdrPtr esCap esPtr ct1Cap ct1Ptr
          st.epoch res st0 (evs1 ++ evs2 ++ evs3) hevs13 hsp0_align hlr0 hpc3 hrun3 herr3

/-! ## 5. Public Budget-Threaded Contracts (Block `338`, 99 instructions) -/

/-- Envelope-parametric `[LibsignalPlacement]` contract for
    `<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek` (Block `338`, 99 instructions). -/
theorem unchunked_ct1_sent_recv_ek_placed_ok_x_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {Env : UnchunkedCt1SentRecvEkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hEnv : ∀ x evs, FreeOnlyEvs evs → Env x evs)
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hval_pk : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (withVmPreserved (mlkemValidatePkSpec K))) :
    subroutine_ok (lsProg_338 (Rust.withPanics ext)) (blkPl_338).base
      (unchunkedCt1SentRecvEkSpecOfEnv M A lim F K Env) := by
  have hdealloc_call : subroutine_ok (lsProg_338 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem (sym := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") hdealloc
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_call
  have hval_call : subroutine_ok (lsProg_338 (Rust.withPanics ext))
      (lsρ "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes")
      (withVmPreserved (mlkemValidatePkSpec K)) :=
    spqr_hook_ok_of_mem
      (sym := "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes") hval_pk
  simp only [unchunkedCt1SentRecvEkSpecOfEnv, lsProg_338] at hdealloc_fo hval_call ⊢
  have h_ok := unchunked_recv_ek_ok_branch_placed (F := F) hdealloc_fo
  have h_err := unchunked_recv_ek_err_branch_placed (F := F) hdealloc_fo
  wp_init x_st s0
  rcases x_st with ⟨x, st0⟩
  dsimp only at *
  apply sepWP_close_recv_ek (hEnv x)
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = x.outA := by assumption
  have hx1 : s0.readReg64 (Reg.gpr 1#5) = x.stA := by assumption
  have hx2 : s0.readReg64 (Reg.gpr 2#5) = x.st.epoch := by assumption
  have hx3 : s0.readReg64 (Reg.gpr 3#5) = x.ekA := by assumption
  have hrecv : x.st.recv_ek K x.st.epoch x.ek = StatesResult.ofError x.res := by assumption
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by assumption
  have hlr0 : LsRetAddr624 (s0.readReg64 Reg.lr) := by assumption
  have hfsp_align : ((s0.sp - 208#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 208#64 hsp0_align (by decide)
  obtain ⟨hok_res, herr_res⟩ := unchunked_recv_ek_elim hrecv
  wp_conv_pre =>
    unfold unchunkedCt1SentAt
    rw [stackAt_unchunkedRecvEk_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.fold (vecU8_unfold_body_48 A.repAlloc x.stA x.st.hdr) (by sep_focus) ?_
  wp_pull_exists; rename_i hdrCap hdrPtr
  wp_focus_pure; rintro ⟨hhdr_le, hhdr_lt, _⟩
  refine SepWP.fold (vecU8_entails_slice_and_tail A.repAlloc x.ekA x.ek) (by sep_focus) ?_
  wp_pull_exists; rename_i ekCap ekPtr
  wp_focus_pure; rintro ⟨hek_le, hek_lt, hek_ne⟩
  refine seq_vm_clean
    (mid := lsρ "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes")
    (P_mid := ((hdrPtr ↦ₛ x.st.hdr) ∗ (ekPtr ↦ₛ x.ek) ∗ stackAt (s0.sp - 208#64) extHookStack) ∗
      (memRegion x.outA 128 ∗ authenticatorAt A.repAlloc x.stA x.st.auth ∗
       ((x.stA + 48#64) ↦₆₄ hdrCap) ∗ ((x.stA + 56#64) ↦₆₄ hdrPtr) ∗
       ((x.stA + 64#64) ↦₆₄ BitVec.ofNat 64 x.st.hdr.length) ∗
       vecU8Tail A.repAlloc hdrCap hdrPtr x.st.hdr ∗
       vecU8 A.repAlloc (x.stA + 72#64) x.st.es ∗ vecU8 A.repAlloc (x.stA + 96#64) x.st.ct1 ∗
       ((x.stA + 120#64) ↦₆₄ x.st.epoch) ∗
       (x.ekA ↦₆₄ ekCap) ∗ ((x.ekA + 8#64) ↦₆₄ ekPtr) ∗
       ((x.ekA + 16#64) ↦₆₄ BitVec.ofNat 64 x.ek.length) ∗
       vecU8Tail A.repAlloc ekCap ekPtr x.ek ∗ A.pool lim st0 s0 ∗
       memRegion (s0.sp - 208#64) 8 ∗ ((s0.sp - 200#64) ↦₆₄ x.st.epoch) ∗
       memRegion (s0.sp - 192#64) 128 ∗ unchunkedRecvEkSavedCells s0))
    (Q := fun sc => sc.sp = s0.sp - 208#64 ∧
      sc.readReg64 .lr = (blkPl_338).base + 76#64 ∧
      sc.trace = s0.trace ∧
      sc.readReg64 .x0 = hdrPtr ∧
      sc.readReg64 .x1 = BitVec.ofNat 64 x.st.hdr.length ∧
      sc.readReg64 .x2 = ekPtr ∧
      sc.readReg64 .x3 = BitVec.ofNat 64 x.ek.length ∧
      sc.readReg64 .x19 = x.stA ∧
      sc.readReg64 .x20 = hdrPtr ∧
      sc.readReg64 .x21 = x.outA ∧
      sc.readReg64 .x22 = x.st.epoch ∧
      sc.readReg64 .x23 = x.ekA ∧
      sc.readReg64 .x24 = ekPtr ∧
      sc.readReg64 .x25 = s0.readReg64 .x25 ∧
      sc.readReg64 .x26 = s0.readReg64 .x26 ∧
      sc.readReg64 .x27 = s0.readReg64 .x27 ∧
      sc.readReg64 .x28 = s0.readReg64 .x28 ∧
      calleeSavedVRegs sc = calleeSavedVRegs s0)
    ?_ ?_
  · by_vm_steps (
      wp_steps
      refine SepWP.fold (fold_unchunkedRecvEkSavedCells s0) (by sep_focus) ?_
      refine align_pre_vm (by sep_ac_rfl) ?_
      wp_done)
  · intro sc hpcc hrunc hvmc
      ⟨hsp_c, hlr_c, htr_c, hx0_c, hx1_c, hx2_c, hx3_c,
       hx19_c, hx20_c, hx21_c, hx22_c, hx23_c, hx24_c,
       hx25_c, hx26_c, hx27_c, hx28_c, hvregs_c⟩
    rw [← A.pool_of_vmPreserved hvmc]
    refine call_validatePk_vm hval_call hdrPtr ekPtr x.st.hdr x.ek
      (ret_pc := (blkPl_338).base + 76#64) (sp_call := s0.sp - 208#64)
      hpcc hrunc hsp_c hfsp_align hlr_c htr_c hx0_c
      (by rw [hx1_c, BitVec.toNat_ofNat]; omega)
      hx2_c
      (by rw [hx3_c, BitVec.toNat_ofNat]; omega)
      rfl
      (fun sf1 hpc1 hrun1 hsp1 hcs1 hvm1 htr1 hvalid => ?_)
    rw [← A.pool_of_vmPreserved hvm1]
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
    have hx19_f : sf1.readReg64 .x19 = x.stA := hx19_1.trans hx19_c
    have hx20_f : sf1.readReg64 .x20 = hdrPtr := hx20_1.trans hx20_c
    have hx21_f : sf1.readReg64 .x21 = x.outA := hx21_1.trans hx21_c
    have hx22_f : sf1.readReg64 .x22 = x.st.epoch := hx22_1.trans hx22_c
    have hx23_f : sf1.readReg64 .x23 = x.ekA := hx23_1.trans hx23_c
    have hx24_f : sf1.readReg64 .x24 = ekPtr := hx24_1.trans hx24_c
    have hx25_f : sf1.readReg64 .x25 = s0.readReg64 .x25 := hx25_1.trans hx25_c
    have hx26_f : sf1.readReg64 .x26 = s0.readReg64 .x26 := hx26_1.trans hx26_c
    have hx27_f : sf1.readReg64 .x27 = s0.readReg64 .x27 := hx27_1.trans hx27_c
    have hx28_f : sf1.readReg64 .x28 = s0.readReg64 .x28 := hx28_1.trans hx28_c
    have hvregs_f : calleeSavedVRegs sf1 = calleeSavedVRegs s0 := hvregs_1.trans hvregs_c
    by_cases hpk : K.validPkBytes x.st.hdr x.ek = true
    · have hbics : (BitVec.truncate 32 (255#64 &&& ~~~BitVec.zeroExtend 64 (BitVec.truncate 32 (sf1.readReg64 (Reg.gpr 0#5)))) == 0#32) = true :=
        (bics_255_eq_zero_iff (sf1.readReg64 (Reg.gpr 0#5))).mpr (hvalid.mpr hpk)
      wp_step; wp_step; wp_step
      refine h_ok x.outA x.stA x.ekA hdrCap hdrPtr ekCap ekPtr
        x.st x.ek x.res (hok_res hpk) hhdr_le hhdr_lt hek_le hek_lt hek_ne st0 hsp0_align hlr0
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · wp_norm_goal
      · wp_norm_lhs
      · simp only [State.sp, arm64_norm, hsp1]
      · simp only [Reg.x19, arm64_norm, hx19_f]
      · simp only [Reg.x20, arm64_norm, hx20_f]
      · simp only [Reg.x21, arm64_norm, hx21_f]
      · simp only [Reg.x22, arm64_norm, hx22_f]
      · simp only [Reg.x23, arm64_norm, hx23_f]
      · simp only [Reg.x25, arm64_norm, hx25_f]
      · simp only [Reg.x26, arm64_norm, hx26_f]
      · simp only [Reg.x27, arm64_norm, hx27_f]
      · simp only [Reg.x28, arm64_norm, hx28_f]
      · simp only [arm64_norm, htr1]
      · simp only [arm64_norm, hvregs_f]
      · simp only [arm64_norm, wp_norm]; sep_ac_rfl
    · have hpk_f : K.validPkBytes x.st.hdr x.ek = false := Bool.eq_false_iff.mpr hpk
      have hbics_not : ¬((BitVec.truncate 32 (255#64 &&& ~~~BitVec.zeroExtend 64 (BitVec.truncate 32 (sf1.readReg64 (Reg.gpr 0#5)))) == 0#32) = true) :=
        fun hb => hpk (hvalid.mp ((bics_255_eq_zero_iff (sf1.readReg64 (Reg.gpr 0#5))).mp hb))
      have hbics : (BitVec.truncate 32 (255#64 &&& ~~~BitVec.zeroExtend 64 (BitVec.truncate 32 (sf1.readReg64 (Reg.gpr 0#5)))) == 0#32) = false :=
        Bool.eq_false_iff.mpr hbics_not
      wp_step; wp_step; wp_step
      refine h_err x.outA x.stA x.ekA hdrCap hdrPtr ekCap ekPtr
        x.st x.ek x.res (herr_res hpk_f) hhdr_le hhdr_lt hek_le hek_lt st0 hsp0_align hlr0
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · wp_norm_goal
      · wp_norm_lhs
      · simp only [State.sp, arm64_norm, hsp1]
      · simp only [Reg.x19, arm64_norm, hx19_f]
      · simp only [Reg.x20, arm64_norm, hx20_f]
      · simp only [Reg.x21, arm64_norm, hx21_f]
      · simp only [Reg.x23, arm64_norm, hx23_f]
      · simp only [Reg.x24, arm64_norm, hx24_f]
      · simp only [Reg.x25, arm64_norm, hx25_f]
      · simp only [Reg.x26, arm64_norm, hx26_f]
      · simp only [Reg.x27, arm64_norm, hx27_f]
      · simp only [Reg.x28, arm64_norm, hx28_f]
      · simp only [arm64_norm, htr1]
      · simp only [arm64_norm, hvregs_f]
      · simp only [arm64_norm, wp_norm]; sep_ac_rfl

/-- `withLsCodeLoaded`-wrapped envelope-parametric `[LibsignalPlacement]` contract for
    `<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek` (Block `338`). -/
theorem unchunked_ct1_sent_recv_ek_placed_cl_ok_x_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {Env : UnchunkedCt1SentRecvEkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hEnv : ∀ x evs, FreeOnlyEvs evs → Env x evs)
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hval_pk : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (withVmPreserved (mlkemValidatePkSpec K))) :
    subroutine_ok (lsProg_338 (Rust.withPanics ext)) (blkPl_338).base
      (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpecOfEnv M A lim F K Env)) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (unchunked_ct1_sent_recv_ek_placed_ok_x_of_env hEnv hdealloc hval_pk)

/-- Closed `[LibsignalPlacement]` budget contract for
    `<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek` (Block `338`, 99 instructions)
    from `HookSat` hypotheses. -/
theorem unchunked_ct1_sent_recv_ek_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hval_pk : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (withVmPreserved (mlkemValidatePkSpec K))) :
    UnchunkedCt1SentRecvEkPlacedOkX M A lim F K ext :=
  unchunked_ct1_sent_recv_ek_placed_ok_x_of_env (fun _ _ h => h) hdealloc hval_pk

/-- `withLsCodeLoaded`-wrapped `[LibsignalPlacement]` budget contract for
    `<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek` (Block `338`), suitable for cross-block
    transfer via `ls_subroutine_ok_of_block`. -/
theorem unchunked_ct1_sent_recv_ek_placed_cl_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hval_pk : HookSat (Rust.withPanics ext)
      "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
      (withVmPreserved (mlkemValidatePkSpec K))) :
    subroutine_ok (lsProg_338 (Rust.withPanics ext)) (blkPl_338).base
      (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec M A lim F K)) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (unchunked_ct1_sent_recv_ek_placed_ok_x hdealloc hval_pk)

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEkPlacedBudget
