/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoderBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.States1a
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyDecoder
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Drop Glue for `spqr::v1::chunked::states::States [local#1]` (Block `140`, Part 1)

Defines `dropChunkedStatesLocal1PlacedSpec` and `dropChunkedStatesLocal1PlacedVariantSpec` under
`RustCliAllocBudget M` (`FreeOnlyEvs`) and proves the first six relocatable
`[LibsignalPlacement]` variant contracts (`keysUnsampled`, `noHeaderReceived`, `headerReceived`,
`ekSentCt1Received`, `ct1Acknowledged`, `ct1Sampled`) for Block `140`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement blkPC_140 blkPl_140 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (NUM_POLYS Pt States spqrAuthApi spqrPolyApi)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop (
  DropChunkedStatesGhost Saved32x19Preserved
  chunkedCt1AcknowledgedAt chunkedCt1SampledAt chunkedEkSentCt1ReceivedAt
  chunkedHeaderReceivedAt chunkedKeysUnsampledAt chunkedNoHeaderReceivedAt
  chunkedStatesAt chunkedStatesLocal1JumpTableBytes
  chunkedStatesLocal1JumpTablePlacedAt chunkedStatesLocal1JumpTablePlacedExpanded
  chunkedStatesLocal1JumpTableSym chunkedStatesSize
  dropGluePoly16Stack dropStack32 dropStackPoly64
  fourVec8HeadersAt fourVec8HeadersAt_entails_memRegion_104
  polyDecoder64_entails_vecs_tail polyDecoder64_post_join
  polyDecoder88_entails_vecs_tail polyDecoder88_post_join
  polyDecoderAt_entails_vecs_tail polyDecoder_post_join
  polyEncoderAt_expose_tag polyEncoderAt_unexpose_tag
  stackAt_dropStack32_split_sub32 stackAt_dropStackPoly64_split
  stackAt_dropStackPoly64_split_bottom stack_restore_64_dropStack32
  tag_and_two_regions_entails_928
  threeVec8HeadersAt threeVec8HeadersAt_entails_memRegion_80
  twoVec8HeadersAt twoVec8HeadersAt_entails_memRegion_56
  unchunkedCt1SentAt unchunkedCt1SentSize
  unchunkedCt2Sent8_entails_dealloc unchunkedEkSent8_entails_dealloc
  unchunkedEkSentCt1Received8_entails_dealloc
  unchunkedHeaderReceivedAt_eq_ekSentAt unchunkedKeysUnsampledAt_eq_ct2SentAt
  unchunkedNoHeaderReceivedAt_eq_ct2SentAt
  vecCapPtrDealloc vecPtListOf
)
open CryptoVerification.SpqrV1.Poly (
  polyArrayBytes polyDecoderAt polyDecoderSize polyEncoderAt polyEncoderSize
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoderBudget (dropGluePolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (dropGlueSortedSetPt16Spec)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (dropUnchunkedCt1SentSpec)

namespace LibsignalBinary.Proofs.SpqrV1.Drop.States1aBudget

open Arm64 ProofLib
open ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Budget-Threaded Specifications (Block `140`) -/

def dropChunkedStatesLocal1PlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (DropChunkedStatesGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      chunkedStatesAt A.repAlloc x.a x.st ∗
      chunkedStatesLocal1JumpTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp dropStackPoly64
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.a chunkedStatesSize ∗
      chunkedStatesLocal1JumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropStackPoly64

/-- Per-variant budget-threaded specification of
`core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#1]` (Block `140`). -/
def dropChunkedStatesLocal1PlacedVariantSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) {F : ShaCompress}
    (st_v : States spqrPolyApi (spqrAuthApi F)) : Spec (BitVec 64 × M.σ) where
  pre := fun (a, st) s =>
    ⌜s.readReg64 .x0 = a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      chunkedStatesAt A.repAlloc a st_v ∗
      chunkedStatesLocal1JumpTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp dropStackPoly64
  post := fun (a, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
      memRegion a chunkedStatesSize ∗
      chunkedStatesLocal1JumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropStackPoly64

/-! ## Sequencing and Prologue Helpers -/

abbrev savedFrame32 (s0 : State) (w3 : BitVec 64) : SepProp :=
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3)

def deallocFreeOnlySpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

theorem subroutine_ok_deallocFreeOnly [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

theorem align_pre_vm {prog : Program} {target : BitVec 64} {s0 s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (h : P = P_mid)
    (hwp : SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P_mid) ∧ Q sm) := by
  subst h; exact hwp

theorem align_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (heq : P = P_mid s)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) := by
  subst heq; exact h

theorem step_prologue_12_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (s0 : State) (v_fp v_lr v_x20 v_x19 : BitVec 64) (Rest : SepProp)
    (hpc : s0.pc = (blkPl_140).base) (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP ((blkPC_140).rebase (blkPl_140).base H) ((blkPl_140).base + 12#64) s0
      (((s0.sp - 32#64) ↦₆₄ v_fp) ∗ ((s0.sp - 24#64) ↦₆₄ v_lr) ∗
        ((s0.sp - 16#64) ↦₆₄ v_x20) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19) ∗ Rest)
      (fun sp1 Pp1 =>
        VmPreserved s0 sp1 ∧
        (Pp1 ⊢ savedFrame32 s0 v_x19 ∗ Rest) ∧
        Saved32x19Preserved s0 sp1 (s0.sp - 32#64) ∧
        AllocCallPreserved s0 sp1 ∧
        sp1.readReg64 .x0 = s0.readReg64 .x0) := by
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 hsp_align (by decide)
  by_vm_steps (
    wp_steps
    dsimp only [savedFrame32]
    refine align_pre_vm (by simp only [Reg.fp, Reg.lr, Reg.x19, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
    wp_done)

theorem enter_prologue_12_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {target : BitVec 64} {s0 : State} {st : M.σ} {a : BitVec 64}
    (v_fp v_lr v_x20 v_x19 : BitVec 64) {Body : SepProp} {post : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_140).base) (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 .x0 = a)
    (hk : ∀ sp1 : State,
      sp1.pc = (blkPl_140).base + 12#64 →
      sp1.status = .Running →
      Saved32x19Preserved s0 sp1 (s0.sp - 32#64) →
      AllocCallPreserved s0 sp1 →
      sp1.readReg64 .x0 = a →
      SepWP ((blkPC_140).rebase (blkPl_140).base H) target sp1
        (Body ∗ A.pool lim st sp1 ∗ savedFrame32 s0 v_x19) post) :
    SepWP ((blkPC_140).rebase (blkPl_140).base H) target s0
      (Body ∗ A.pool lim st s0 ∗
        (((s0.sp - 32#64) ↦₆₄ v_fp) ∗ ((s0.sp - 24#64) ↦₆₄ v_lr) ∗
          ((s0.sp - 16#64) ↦₆₄ v_x20) ∗ ((s0.sp - 8#64) ↦₆₄ v_x19))) post := by
  have h1 := step_prologue_12_placed (H := H) s0 v_fp v_lr v_x20 v_x19
    (Body ∗ A.pool lim st s0) hpc hrun hsp_align
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.seq h1 ?_)
  intro sp1 Pp1 hpc1 hrun1 ⟨hvm, hent, hpres, hacp, hx0_1⟩
  rw [hx0] at hx0_1
  have hent' : Pp1 ⊢ Body ∗ A.pool lim st sp1 ∗ savedFrame32 s0 v_x19 := by
    rw [A.pool_of_vmPreserved hvm]
    exact Entails.trans hent (Entails.of_eq (by sep_ac_rfl))
  exact SepWP.weaken_pre hent' (hk sp1 hpc1 hrun1 hpres hacp hx0_1)

theorem seq_evs_step {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {mid target : BitVec 64}
    {st : M.σ} {s : State} {P X1 X2 X3 : SepProp}
    {P_mid : M.σ → State → SepProp} {Q_mid Q_out : State → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs1, FreeOnlyEvs evs1 ∧ (Pm ⊢ P_mid (M.stepEvents evs1 st) sm) ∧ Q_mid sm))
    (h2 : ∀ (st1 : M.σ) (sm : State),
      sm.pc = mid → sm.status = .Running → Q_mid sm →
      SepWP prog target sm (P_mid st1 sm) (fun sf Pf =>
        ∃ evs2, FreeOnlyEvs evs2 ∧
          (Pf ⊢ X1 ∗ X2 ∗ A.pool lim (M.stepEvents evs2 st1) sf ∗ X3) ∧ Q_out sf)) :
    SepWP prog target s P (fun sf Pf =>
      ∃ evs, FreeOnlyEvs evs ∧
        (Pf ⊢ X1 ∗ X2 ∗ A.pool lim (M.stepEvents evs st) sf ∗ X3) ∧ Q_out sf) :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨evs1, hevs1, hent, hQ⟩ =>
    SepWP.mono (SepWP.weaken_pre hent (h2 (M.stepEvents evs1 st) sm hpc hrun hQ))
      fun sf _Pf _ _ ⟨evs2, hevs2, hPf, hQo⟩ =>
        ⟨evs1 ++ evs2, hevs1.append hevs2, by
          rwa [LibsignalBinary.Heap.AllocCostModel.stepEvents_append], hQo⟩

theorem sepWP_evs_nil {prog : Program} {target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs [] sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, hp, hq⟩

theorem sepWP_evs_dealloc {prog : Program} {target : BitVec 64}
    {s : State} (sz al : Nat)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm =>
      (Pm ⊢ P_evs (rustDeallocEvents sz al) sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ =>
    ⟨rustDeallocEvents sz al, LibsignalBinary.Heap.FreeOnlyEvs.singleton al sz, hp, hq⟩

theorem sepWP_evs_of {prog : Program} {target : BitVec 64}
    {s : State} (evs : List AllocEvent) (hevs : FreeOnlyEvs evs)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs evs sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs', FreeOnlyEvs evs' ∧ (Pm ⊢ P_evs evs' sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs, hevs, hp, hq⟩

theorem sepWP_open_evs {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {s0 : State} {P X1 X2 R : SepProp} {stk : Nat} {st : M.σ}
    (h : SepWP prog (s0.readReg64 .lr) s0 P (fun sf Pf =>
      ∃ evs, FreeOnlyEvs evs ∧
        (Pf ⊢ X1 ∗ X2 ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk) ∧
        (sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ CalleeSavedPreserved s0 sf))) :
    SepWP prog (s0.readReg64 .lr) s0 P (fun sf Pf =>
      (sf.mem ⊨ Pf ∗ R → sf.mem ⊨
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
          X1 ∗ X2 ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) :=
  SepWP.mono h fun sf _Pf _ _ ⟨evs, hevs, hp, hsp_f, htr_f, hacp_f, hcs_f⟩ =>
    ⟨fun hm => by
      rw [satisfies_sepExists]
      refine ⟨evs, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨⟨htr_f, hacp_f, hevs⟩,
        Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm⟩,
     hsp_f, hcs_f⟩

private theorem chunkedStatesLocal1JumpTablePlacedAt_eq [LibsignalPlacement] :
    chunkedStatesLocal1JumpTablePlacedAt = chunkedStatesLocal1JumpTablePlacedExpanded := by
  simp only [chunkedStatesLocal1JumpTablePlacedAt, chunkedStatesLocal1JumpTableBytes,
    chunkedStatesLocal1JumpTablePlacedExpanded, pointsToBytesRO_cons, pointsToBytesRO_nil,
    sepConj_emp, BitVec.add_assoc, wp_norm, arm64_norm]

theorem enter_chunked_states_prologue [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {s0 : State} {st : M.σ} {a : BitVec 64} {StatePre R : SepProp}
    (hpc : s0.pc = (blkPl_140).base) (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 .x0 = a)
    (hk : ∀ (sp1 : State) (v_x19 : BitVec 64),
      sp1.pc = (blkPl_140).base + 12#64 →
      sp1.status = .Running →
      Saved32x19Preserved s0 sp1 (s0.sp - 32#64) →
      AllocCallPreserved s0 sp1 →
      sp1.readReg64 .x0 = a →
      SepWP ((blkPC_140).rebase (blkPl_140).base H) (s0.readReg64 .lr) sp1
        (StatePre ∗ chunkedStatesLocal1JumpTablePlacedExpanded ∗
          A.pool lim st sp1 ∗ stackAt (s0.sp - 32#64) dropStack32 ∗ savedFrame32 s0 v_x19)
        (fun sf Pf =>
          ∃ evs, FreeOnlyEvs evs ∧
            (Pf ⊢ memRegion a 928 ∗ chunkedStatesLocal1JumpTablePlacedExpanded ∗
              A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropStackPoly64) ∧
            (sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ CalleeSavedPreserved s0 sf))) :
    SepWP ((blkPC_140).rebase (blkPl_140).base H) (s0.readReg64 .lr) s0
      (StatePre ∗ chunkedStatesLocal1JumpTablePlacedAt ∗ A.pool lim st s0 ∗ stackAt s0.sp dropStackPoly64)
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R → sf.mem ⊨
          (∃∗ evs : List AllocEvent,
            ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FreeOnlyEvs evs⌝ ∗
            memRegion a chunkedStatesSize ∗ chunkedStatesLocal1JumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropStackPoly64) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  rw [chunkedStatesLocal1JumpTablePlacedAt_eq]
  dsimp only [chunkedStatesSize]
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  apply sepWP_open_evs
  refine SepWP.weaken_pre ?_ (enter_prologue_12_placed v_fp v_lr v_x20 v_x19
    (Body := StatePre ∗ chunkedStatesLocal1JumpTablePlacedExpanded ∗ stackAt (s0.sp - 32#64) dropStack32)
    hpc hrun hsp_align hx0
    (fun sp1 hpc1 hrun1 hpres1 hacp1 hx0_1 =>
      SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hk sp1 v_x19 hpc1 hrun1 hpres1 hacp1 hx0_1)))
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## Relocatable `[LibsignalPlacement]` Variant Proofs (Block `140`) -/

section PlacedStates1aBudget
variable [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
  {lim : BudgetLimits} {F : ShaCompress} {H : String → Option (State → State)}

/-- Variant `keysUnsampled` (`tag = 2#64`, jump index `0` -> `+264` -> `+284` -> `ret`). -/
theorem drop_chunked_states_local1_keysUnsampled_placed
    (hdealloc : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (blkPl_140).base
      (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.keysUnsampled st_v)) := by
  simp only [dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc; simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine enter_chunked_states_prologue (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, chunkedKeysUnsampledAt]
  rw [unchunkedKeysUnsampledAt_eq_ct2SentAt]
  refine SepWP.focus_weaken
    (unchunkedCt2Sent8_entails_dealloc A.repAlloc a { epoch := st_v.uc.epoch, auth := st_v.uc.auth })
    (by sep_focus) ?_
  wp_pull_exists; rename_i g
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine seq_evs_step (mid := (blkPl_140).base + 284#64)
    (P_mid := fun st1 sm =>
      ((a ↦₆₄ 2#64) ∗
        (twoVec8HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
        memRegion (a + 64#64) 864) ∗
      chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool lim st1 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      savedFrame32 s0 v_x19)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · dsimp only [twoVec8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      savedFrame32, chunkedStatesLocal1JumpTablePlacedExpanded]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · apply sepWP_evs_dealloc g.v1.cap.toNat 1
      wp_steps; wp_apply; rw [hsp_0]
      have hacp' : AllocCallPreserved s0 sf := hacp_0.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st1 s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    have hjoin928 : (a ↦₆₄ 2#64) ∗ twoVec8HeadersAt a g ∗ memRegion (a + 64#64) 864 ⊢ memRegion a 928 := by
      refine Entails.trans (sepConj_mono_right (sepConj_mono_left (twoVec8HeadersAt_entails_memRegion_56 a g))) ?_
      exact tag_and_two_regions_entails_928 a 2#64 56 864 64#64 (BitVec.add_assoc a 8#64 56#64).symm rfl
    dsimp only [twoVec8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      savedFrame32, chunkedStatesLocal1JumpTablePlacedExpanded] at hjoin928 ⊢
    by_cases hc2 : (g.v2.cap == 0#64) = true <;>
      simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps
      refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x19) v_x19)
        (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
      wp_done
    · apply sepWP_evs_dealloc g.v2.cap.toNat 1
      wp_steps
      refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x19) v_x19)
        (by sep_focus) ?_
      have hsplit_top : stackAt s0.sp dropStackPoly64 =
          memRegion (s0.sp - 4160#64) 64 ∗ stackAt s0.sp allocHookStack :=
        stackAt_split_bottom s0.sp allocHookStack 64 (by decide)
      refine SepWP.focus_weaken (Entails.of_eq hsplit_top) (by sep_focus) ?_
      wp_apply
      have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      refine SepWP.focus_weaken (Entails.of_eq hsplit_top.symm) (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
      wp_done

/-- Variant `noHeaderReceived` (`tag = 7#64`, jump index `5` -> `+428` -> dealloc 2 Vecs -> tail-call Block `137`). -/
theorem drop_chunked_states_local1_noHeaderReceived_placed
    (hdealloc : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsmpl.base 137) (dropGlueSortedSetPt16Spec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (blkPl_140).base
      (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.noHeaderReceived st_v)) := by
  simp only [dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc; simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine enter_chunked_states_prologue (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, chunkedNoHeaderReceivedAt, spqrPolyApi]
  rw [unchunkedNoHeaderReceivedAt_eq_ct2SentAt]
  refine SepWP.focus_weaken
    (unchunkedCt2Sent8_entails_dealloc A.repAlloc a { epoch := st_v.uc.epoch, auth := st_v.uc.auth })
    (by sep_focus) ?_
  wp_pull_exists; rename_i g
  refine SepWP.focus_weaken (polyDecoder64_entails_vecs_tail A.repAlloc a st_v.receiving_hdr) (by sep_focus) ?_
  wp_pull_exists; rename_i vecs; wp_focus_pure; intro hvecs_len
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine seq_evs_step (mid := (blkPl_140).base + 448#64)
    (P_mid := fun st1 sm =>
      ((a ↦₆₄ 7#64) ∗
        (twoVec8HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
        vecPtListOf A.repAlloc (a + 64#64) vecs ∗ memRegion (a + 448#64) 16 ∗
        memRegion (a + 464#64) 464) ∗
      chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool lim st1 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      savedFrame32 s0 v_x19)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · dsimp only [twoVec8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      savedFrame32, chunkedStatesLocal1JumpTablePlacedExpanded]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · apply sepWP_evs_dealloc g.v1.cap.toNat 1
      wp_steps; wp_apply; rw [hsp_0]
      have hacp' : AllocCallPreserved s0 sf := hacp_0.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st1 s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    refine seq_evs_step (mid := (blkPl_140).base + 468#64)
      (P_mid := fun st2 sm =>
        ((a ↦₆₄ 7#64) ∗ memRegion (a + 8#64) 56 ∗
          vecPtListOf A.repAlloc (a + 64#64) vecs ∗ memRegion (a + 448#64) 16 ∗
          memRegion (a + 464#64) 464) ∗
        chunkedStatesLocal1JumpTablePlacedExpanded ∗
        A.pool lim st2 sm ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
        savedFrame32 s0 v_x19)
      (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · have hhdr56 := twoVec8HeadersAt_entails_memRegion_56 a g
      dsimp only [twoVec8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live] at hhdr56 ⊢
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps
        refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
        refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
      · apply sepWP_evs_dealloc g.v2.cap.toNat 1
        wp_steps; wp_apply; rw [hsp_1]
        have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
        refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · intro st2 s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_2
      dsimp only [savedFrame32, chunkedStatesLocal1JumpTablePlacedExpanded]
      wp_steps
      refine SepWP.focus_weaken
        (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x19) v_x19)
        (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
      wp_call hdec_raw (⟨a + 64#64, vecs⟩, st2)
      have hacp_f : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
      have hevs_w : FreeOnlyEvs w := by assumption
      rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
      dsimp only [polyArrayBytes]
      refine SepWP.focus_weaken (polyDecoder64_post_join a) (by sep_focus) ?_
      have hjoin456 : memRegion (a + 8#64) 56 ∗ memRegion (a + 64#64) polyDecoderSize ⊢
          memRegion (a + 8#64) 456 := by
        have h64 : (a + 8#64) + 56#64 = a + 64#64 := BitVec.add_assoc a 8#64 56#64
        rw [← h64, show (456 : Nat) = 56 + polyDecoderSize from rfl,
            ProofLib.memRegion_split (a + 8#64) 56 polyDecoderSize (by decide)]
        exact Entails.refl _
      refine SepWP.focus_weaken hjoin456 (by sep_focus) ?_
      have hjoin928 := tag_and_two_regions_entails_928 a 7#64 456 464 464#64
        (BitVec.add_assoc a 8#64 456#64).symm rfl
      refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
      apply sepWP_evs_of w hevs_w
      wp_done

/-- Variant `headerReceived` (`tag = 8#64`, jump index `6` -> `+484` -> dealloc 3 Vecs -> tail-call Block `137`). -/
theorem drop_chunked_states_local1_headerReceived_placed
    (hdealloc : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsmpl.base 137) (dropGlueSortedSetPt16Spec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (blkPl_140).base
      (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.headerReceived st_v)) := by
  simp only [dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc; simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine enter_chunked_states_prologue (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, chunkedHeaderReceivedAt, spqrPolyApi]
  rw [unchunkedHeaderReceivedAt_eq_ekSentAt]
  refine SepWP.focus_weaken
    (unchunkedEkSent8_entails_dealloc A.repAlloc a { epoch := st_v.uc.epoch, auth := st_v.uc.auth, dk := st_v.uc.hdr })
    (by sep_focus) ?_
  wp_pull_exists; rename_i g
  refine SepWP.focus_weaken (polyDecoder88_entails_vecs_tail A.repAlloc a st_v.receiving_ek) (by sep_focus) ?_
  wp_pull_exists; rename_i vecs; wp_focus_pure; intro hvecs_len
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine seq_evs_step (mid := (blkPl_140).base + 504#64)
    (P_mid := fun st1 sm =>
      ((a ↦₆₄ 8#64) ∗
        (threeVec8HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
         vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
        vecPtListOf A.repAlloc (a + 88#64) vecs ∗ memRegion (a + 472#64) 16 ∗
        memRegion (a + 488#64) 440) ∗
      chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool lim st1 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      savedFrame32 s0 v_x19)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · dsimp only [threeVec8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      savedFrame32, chunkedStatesLocal1JumpTablePlacedExpanded]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · apply sepWP_evs_dealloc g.v1.cap.toNat 1
      wp_steps; wp_apply; rw [hsp_0]
      have hacp' : AllocCallPreserved s0 sf := hacp_0.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st1 s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    refine seq_evs_step (mid := (blkPl_140).base + 524#64)
      (P_mid := fun st2 sm =>
        ((a ↦₆₄ 8#64) ∗
          (threeVec8HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
          vecPtListOf A.repAlloc (a + 88#64) vecs ∗ memRegion (a + 472#64) 16 ∗
          memRegion (a + 488#64) 440) ∗
        chunkedStatesLocal1JumpTablePlacedExpanded ∗
        A.pool lim st2 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        savedFrame32 s0 v_x19)
      (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · dsimp only [threeVec8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
      · apply sepWP_evs_dealloc g.v2.cap.toNat 1
        wp_steps; wp_apply; rw [hsp_1]
        have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · intro st2 s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_2
      refine seq_evs_step (mid := (blkPl_140).base + 544#64)
        (P_mid := fun st3 sm =>
          ((a ↦₆₄ 8#64) ∗ memRegion (a + 8#64) 80 ∗
            vecPtListOf A.repAlloc (a + 88#64) vecs ∗ memRegion (a + 472#64) 16 ∗
            memRegion (a + 488#64) 440) ∗
          chunkedStatesLocal1JumpTablePlacedExpanded ∗
          A.pool lim st3 sm ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
          savedFrame32 s0 v_x19)
        (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · have hhdr80 := threeVec8HeadersAt_entails_memRegion_80 a g
        dsimp only [threeVec8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live] at hhdr80 ⊢
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
          wp_steps
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
          refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
        · apply sepWP_evs_dealloc g.v3.cap.toNat 1
          wp_steps; wp_apply; rw [hsp_2]
          have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
          refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
      · intro st3 s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_3
        dsimp only [savedFrame32, chunkedStatesLocal1JumpTablePlacedExpanded]
        wp_steps
        refine SepWP.focus_weaken
          (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x19) v_x19)
          (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
        wp_call hdec_raw (⟨a + 88#64, vecs⟩, st3)
        have hacp_f : AllocCallPreserved s0 sf := hacp_3.trans (by assumption)
        have hevs_w : FreeOnlyEvs w := by assumption
        rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
        refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
        dsimp only [polyArrayBytes]
        refine SepWP.focus_weaken (polyDecoder88_post_join a) (by sep_focus) ?_
        have hjoin480 : memRegion (a + 8#64) 80 ∗ memRegion (a + 88#64) polyDecoderSize ⊢
            memRegion (a + 8#64) 480 := by
          have h88 : (a + 8#64) + 80#64 = a + 88#64 := BitVec.add_assoc a 8#64 80#64
          rw [← h88, show (480 : Nat) = 80 + polyDecoderSize from rfl,
              ProofLib.memRegion_split (a + 8#64) 80 polyDecoderSize (by decide)]
          exact Entails.refl _
        refine SepWP.focus_weaken hjoin480 (by sep_focus) ?_
        have hjoin928 := tag_and_two_regions_entails_928 a 8#64 480 440 488#64
          (BitVec.add_assoc a 8#64 480#64).symm rfl
        refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
        apply sepWP_evs_of w hevs_w
        wp_done

/-- Variant `ekSentCt1Received` (`tag = 6#64`, jump index `4` -> `+144` -> dealloc 4 Vecs -> tail-call Block `137`). -/
theorem drop_chunked_states_local1_ekSentCt1Received_placed
    (hdealloc : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsmpl.base 137) (dropGlueSortedSetPt16Spec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (blkPl_140).base
      (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.ekSentCt1Received st_v)) := by
  simp only [dropChunkedStatesLocal1PlacedVariantSpec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc; simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine enter_chunked_states_prologue (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, chunkedEkSentCt1ReceivedAt, spqrPolyApi]
  refine SepWP.focus_weaken (unchunkedEkSentCt1Received8_entails_dealloc A.repAlloc a st_v.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g
  have hdec112 : polyDecoderAt A.repAlloc (a + 112#64) st_v.receiving_ct2 ⊢
      ∃∗ vecs : List (List Pt),
        ⌜vecs.length = NUM_POLYS⌝ ∗
        vecPtListOf A.repAlloc (a + 112#64) vecs ∗
        memRegion (a + 496#64) 16 := by
    refine Entails.trans (polyDecoderAt_entails_vecs_tail A.repAlloc (a + 112#64) st_v.receiving_ct2) ?_
    apply Entails.sepExists_elim; intro vecs
    refine Entails.sepExists_right vecs ?_
    rw [BitVec.add_assoc a 112#64 384#64]
    exact Entails.refl _
  refine SepWP.focus_weaken hdec112 (by sep_focus) ?_
  wp_pull_exists; rename_i vecs; wp_focus_pure; intro hvecs_len
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine seq_evs_step (mid := (blkPl_140).base + 164#64)
    (P_mid := fun st1 sm =>
      ((a ↦₆₄ 6#64) ∗
        (fourVec8HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
         vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗ vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr) ∗
        vecPtListOf A.repAlloc (a + 112#64) vecs ∗ memRegion (a + 496#64) 16 ∗
        memRegion (a + 512#64) 416) ∗
      chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool lim st1 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      savedFrame32 s0 v_x19)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · dsimp only [fourVec8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      savedFrame32, chunkedStatesLocal1JumpTablePlacedExpanded]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · apply sepWP_evs_dealloc g.v1.cap.toNat 1
      wp_steps; wp_apply; rw [hsp_0]
      have hacp' : AllocCallPreserved s0 sf := hacp_0.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st1 s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    refine seq_evs_step (mid := (blkPl_140).base + 184#64)
      (P_mid := fun st2 sm =>
        ((a ↦₆₄ 6#64) ∗
          (fourVec8HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
           vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr) ∗
          vecPtListOf A.repAlloc (a + 112#64) vecs ∗ memRegion (a + 496#64) 16 ∗
          memRegion (a + 512#64) 416) ∗
        chunkedStatesLocal1JumpTablePlacedExpanded ∗
        A.pool lim st2 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        savedFrame32 s0 v_x19)
      (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · dsimp only [fourVec8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
      · apply sepWP_evs_dealloc g.v2.cap.toNat 1
        wp_steps; wp_apply; rw [hsp_1]
        have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · intro st2 s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_2
      refine seq_evs_step (mid := (blkPl_140).base + 204#64)
        (P_mid := fun st3 sm =>
          ((a ↦₆₄ 6#64) ∗
            (fourVec8HeadersAt a g ∗ vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr) ∗
            vecPtListOf A.repAlloc (a + 112#64) vecs ∗ memRegion (a + 496#64) 16 ∗
            memRegion (a + 512#64) 416) ∗
          chunkedStatesLocal1JumpTablePlacedExpanded ∗
          A.pool lim st3 sm ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
          savedFrame32 s0 v_x19)
        (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · dsimp only [fourVec8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
          wp_steps; refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
        · apply sepWP_evs_dealloc g.v3.cap.toNat 1
          wp_steps; wp_apply; rw [hsp_2]
          have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
      · intro st3 s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_3
        refine seq_evs_step (mid := (blkPl_140).base + 224#64)
          (P_mid := fun st4 sm =>
            ((a ↦₆₄ 6#64) ∗ memRegion (a + 8#64) 104 ∗
              vecPtListOf A.repAlloc (a + 112#64) vecs ∗ memRegion (a + 496#64) 16 ∗
              memRegion (a + 512#64) 416) ∗
            chunkedStatesLocal1JumpTablePlacedExpanded ∗
            A.pool lim st4 sm ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
            savedFrame32 s0 v_x19)
          (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
          ?_ ?_
        · have hhdr104 := fourVec8HeadersAt_entails_memRegion_104 a g
          dsimp only [fourVec8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live] at hhdr104 ⊢
          by_cases hc4 : (g.v4.cap == 0#64) = true <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
          · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
            wp_steps
            refine SepWP.focus_weaken hhdr104 (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
            refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
          · apply sepWP_evs_dealloc g.v4.cap.toNat 1
            wp_steps; wp_apply; rw [hsp_3]
            have hacp' : AllocCallPreserved s0 sf := hacp_3.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            refine SepWP.focus_weaken hhdr104 (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
            refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
        · intro st4 s4 hpc4 hrun4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hacp_4, hx19_4⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_4
          dsimp only [savedFrame32, chunkedStatesLocal1JumpTablePlacedExpanded]
          wp_steps
          refine SepWP.focus_weaken
            (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x19) v_x19)
            (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
          wp_call hdec_raw (⟨a + 112#64, vecs⟩, st4)
          have hacp_f : AllocCallPreserved s0 sf := hacp_4.trans (by assumption)
          have hevs_w : FreeOnlyEvs w := by assumption
          rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
          have hjoin112 : memRegion (a + 112#64) polyArrayBytes ∗ memRegion (a + 496#64) 16 ⊢
              memRegion (a + 112#64) polyDecoderSize := by
            have h496 : a + 496#64 = (a + 112#64) + 384#64 := (BitVec.add_assoc a 112#64 384#64).symm
            rw [h496]
            exact polyDecoder_post_join (a + 112#64)
          refine SepWP.focus_weaken hjoin112 (by sep_focus) ?_
          have hjoin504 : memRegion (a + 8#64) 104 ∗ memRegion (a + 112#64) polyDecoderSize ⊢
              memRegion (a + 8#64) 504 := by
            have h112 : (a + 8#64) + 104#64 = a + 112#64 := BitVec.add_assoc a 8#64 104#64
            rw [← h112, show (504 : Nat) = 104 + polyDecoderSize from rfl,
                ProofLib.memRegion_split (a + 8#64) 104 polyDecoderSize (by decide)]
            exact Entails.refl _
          refine SepWP.focus_weaken hjoin504 (by sep_focus) ?_
          have hjoin928 := tag_and_two_regions_entails_928 a 6#64 504 416 512#64
            (BitVec.add_assoc a 8#64 504#64).symm rfl
          refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
          apply sepWP_evs_of w hevs_w
          wp_done

/-- Variant `ct1Acknowledged` (`tag = 11#64`, jump index `9` -> `+240` -> `bl` Block `141` -> tail-call Block `137`). -/
theorem drop_chunked_states_local1_ct1Acknowledged_placed
    (hct1_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsmpl.base 141) (dropUnchunkedCt1SentSpec M A lim F))
    (hdec_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsmpl.base 137) (dropGlueSortedSetPt16Spec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (blkPl_140).base
      (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.ct1Acknowledged st_v)) := by
  simp only [dropChunkedStatesLocal1PlacedVariantSpec]
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine enter_chunked_states_prologue (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, chunkedCt1AcknowledgedAt, spqrPolyApi]
  refine SepWP.focus_weaken (polyDecoderAt_entails_vecs_tail A.repAlloc (a + 136#64) st_v.receiving_ek) (by sep_focus) ?_
  wp_pull_exists; rename_i vecs; wp_focus_pure; intro hvecs_len
  refine seq_evs_step (mid := (blkPl_140).base + 240#64)
    (P_mid := fun st1 sm =>
      ((a ↦₆₄ 11#64) ∗ unchunkedCt1SentAt A.repAlloc (a + 8#64) st_v.uc ∗
        vecPtListOf A.repAlloc (a + 136#64) vecs ∗ memRegion ((a + 136#64) + 384#64) 16 ∗
        memRegion (a + 536#64) 392) ∗
      chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool lim st1 sm ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
      savedFrame32 s0 v_x19)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    dsimp only [savedFrame32, chunkedStatesLocal1JumpTablePlacedExpanded]
    wp_steps
    refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st1 s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    dsimp only [savedFrame32, chunkedStatesLocal1JumpTablePlacedExpanded]
    wp_steps
    rw [← hsp_1]
    wp_call hct1_raw (⟨a + 8#64, st_v.uc⟩, st1)
    have hacp_2 : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
    have hevs1 : FreeOnlyEvs w := by assumption
    have hsp_sf : sf.sp = s1.sp := by assumption
    rw [hsp_1] at hsp_sf ⊢
    wp_steps
    have hsp_eq : stackAt sf.sp dropStack32 = stackAt (s0.sp - 32#64) dropStack32 := by rw [hsp_sf]
    refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
    refine SepWP.focus_weaken
      (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x19) v_x19)
      (by sep_focus) ?_
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
    wp_call hdec_raw (⟨a + 136#64, vecs⟩, M.stepEvents w st1)
    have hacp_f : AllocCallPreserved s0 sf_1 := hacp_2.trans (by assumption)
    have hevs2 : FreeOnlyEvs w_1 := by assumption
    rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
    rw [← LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
    dsimp only [polyArrayBytes, unchunkedCt1SentSize]
    refine SepWP.focus_weaken (polyDecoder_post_join (a + 136#64)) (by sep_focus) ?_
    have hjoin528 : memRegion (a + 8#64) 128 ∗ memRegion (a + 136#64) polyDecoderSize ⊢
        memRegion (a + 8#64) 528 := by
      have h136 : (a + 8#64) + 128#64 = a + 136#64 := BitVec.add_assoc a 8#64 128#64
      rw [← h136, show (528 : Nat) = 128 + polyDecoderSize from rfl,
          ProofLib.memRegion_split (a + 8#64) 128 polyDecoderSize (by decide)]
      exact Entails.refl _
    refine SepWP.focus_weaken hjoin528 (by sep_focus) ?_
    have hjoin928 := tag_and_two_regions_entails_928 a 11#64 528 392 536#64
      (BitVec.add_assoc a 8#64 528#64).symm rfl
    refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
    apply sepWP_evs_of (w ++ w_1) (hevs1.append hevs2)
    wp_done

/-- Variant `ct1Sampled` (`tag = 0#64` or `1#64` -> `+396` -> `bl` Block `141` -> `bl` Block `138` -> tail-call Block `137`). -/
theorem drop_chunked_states_local1_ct1Sampled_placed
    (hct1_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsmpl.base 141) (dropUnchunkedCt1SentSpec M A lim F))
    (henc_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsmpl.base 138) (dropGluePolyEncoderSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_140).rebase (blkPl_140).base H)
      (lsmpl.base 137) (dropGlueSortedSetPt16Spec M A lim))
    (st_v : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_140).rebase (blkPl_140).base H) (blkPl_140).base
      (dropChunkedStatesLocal1PlacedVariantSpec M A lim (.ct1Sampled st_v)) := by
  simp only [dropChunkedStatesLocal1PlacedVariantSpec]
  wp_init a_st s0; rcases a_st with ⟨a, st⟩
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine enter_chunked_states_prologue (by assumption) (by assumption) (by assumption) (by assumption) ?_
  intro sp1 v_x19 hpc0 hrun0
    ⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩
    hacp_0 hx0_0
  have ⟨_, _, _, _, _, _, _⟩ := hacp_0
  dsimp only [chunkedStatesAt, chunkedCt1SampledAt, spqrPolyApi]
  refine SepWP.focus_weaken (polyEncoderAt_expose_tag A.repAlloc a st_v.sending_ct1) (by sep_focus) ?_
  wp_pull_exists; rename_i tag_w; wp_focus_pure; intro hw
  refine seq_evs_step (mid := (blkPl_140).base + 396#64)
    (P_mid := fun st1 sm =>
      (polyEncoderAt A.repAlloc a st_v.sending_ct1 ∗
        unchunkedCt1SentAt A.repAlloc (a + 400#64) st_v.uc ∗
        polyDecoderAt A.repAlloc (a + 528#64) st_v.receiving_ek) ∗
      chunkedStatesLocal1JumpTablePlacedExpanded ∗
      A.pool lim st1 sm ∗ stackAt (s0.sp - 32#64) dropStack32 ∗
      savedFrame32 s0 v_x19)
    (Q_mid := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · rcases hw with rfl | rfl
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      dsimp only [savedFrame32, chunkedStatesLocal1JumpTablePlacedExpanded]
      wp_steps
      refine SepWP.focus_weaken (polyEncoderAt_unexpose_tag A.repAlloc a 0#64 st_v.sending_ct1) (by sep_focus) ?_
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
    · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      dsimp only [savedFrame32, chunkedStatesLocal1JumpTablePlacedExpanded]
      wp_steps
      refine SepWP.focus_weaken (polyEncoderAt_unexpose_tag A.repAlloc a 1#64 st_v.sending_ct1) (by sep_focus) ?_
      refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_; wp_done
  · intro st1 s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    dsimp only [savedFrame32]
    refine SepWP.focus_weaken (polyDecoderAt_entails_vecs_tail A.repAlloc (a + 528#64) st_v.receiving_ek) (by sep_focus) ?_
    wp_pull_exists; rename_i dec_vecs; wp_focus_pure; intro hdec_len
    wp_steps
    rw [← hsp_1]
    wp_call hct1_raw (⟨a + 400#64, st_v.uc⟩, st1)
    have hacp_2 : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
    have hevs1 : FreeOnlyEvs w := by assumption
    have hsp_sf : sf.sp = s1.sp := by assumption
    wp_steps
    have hsplit_enc_stk : stackAt s1.sp dropStack32 = stackAt sf.sp dropGluePoly16Stack := by
      rw [hsp_sf]
    refine SepWP.focus_weaken (Entails.of_eq hsplit_enc_stk) (by sep_focus) ?_
    wp_call henc_raw (⟨a, st_v.sending_ct1⟩, M.stepEvents w st1)
    have hacp_3 : AllocCallPreserved s0 sf_1 := hacp_2.trans (by assumption)
    have hevs2 : FreeOnlyEvs w_1 := by assumption
    have hsp_sf1 : sf_1.sp = sf.sp := by assumption
    rw [← LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
    wp_steps
    have hsp_eq : stackAt sf.sp dropGluePoly16Stack = stackAt (s0.sp - 32#64) dropStack32 := by
      rw [hsp_sf, hsp_1]
    refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
    refine SepWP.focus_weaken
      (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x19) v_x19)
      (by sep_focus) ?_
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
    wp_call hdec_raw (⟨a + 528#64, dec_vecs⟩, M.stepEvents (w ++ w_1) st1)
    have hacp_f : AllocCallPreserved s0 sf_2 := hacp_3.trans (by assumption)
    have hevs3 : FreeOnlyEvs w_2 := by assumption
    rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
    rw [← LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
    dsimp only [polyArrayBytes, polyEncoderSize, unchunkedCt1SentSize]
    refine SepWP.focus_weaken (polyDecoder_post_join (a + 528#64)) (by sep_focus) ?_
    have hjoin528 : memRegion a 400 ∗ memRegion (a + 400#64) 128 ⊢ memRegion a 528 := by
      rw [show (528 : Nat) = 400 + 128 from rfl,
          ProofLib.memRegion_split a 400 128 (by decide)]
      exact Entails.refl _
    refine SepWP.focus_weaken hjoin528 (by sep_focus) ?_
    have hjoin928 : memRegion a 528 ∗ memRegion (a + 528#64) polyDecoderSize ⊢ memRegion a 928 := by
      rw [show (928 : Nat) = 528 + polyDecoderSize from rfl,
          ProofLib.memRegion_split a 528 polyDecoderSize (by decide)]
      exact Entails.refl _
    refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_
    apply sepWP_evs_of ((w ++ w_1) ++ w_2) ((hevs1.append hevs2).append hevs3)
    wp_done

end PlacedStates1aBudget

end LibsignalBinary.Proofs.SpqrV1.Drop.States1aBudget
