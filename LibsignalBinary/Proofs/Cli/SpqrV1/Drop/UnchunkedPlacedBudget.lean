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
public import LibsignalBinary.Proofs.SpqrV1.Drop.Unchunked
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.DecodesPlaced
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Unchunked `Ct1Sent` Drop Glue (Blocks `444` and `436`)

Proves `drop_unchunked_ct1_sent_local1_placed_ok` (Block `444`) and
`drop_opt_proto_unchunked_ct1_sent_placed_ok` (Block `436`) along with `HookSat` and `withPanics`
wrappers under `RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.Cli.SpqrV1.Drop.Placed (
  blkPC_436 blkPC_444 blkPl_436 blkPl_444 lsProg_436 lsProg_444
)
open CryptoVerification.LibsignalSpqrV1 (ProtoAuthenticator)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.SpqrV1.Drop (
  DropOptProtoUnchunkedCt1SentGhost DropUnchunkedCt1SentGhost
  Saved32x19Preserved Saved32x20Preserved ThreeVecGhost TwoVecGhost
  auth72HeadersAt auth72HeadersAt_entails_memRegion_48 cap_add_one_beq_zero_false
  cells4_entails_stack32_bottom dropStack32 fiveVec128HeadersAt
  fiveVec128HeadersAt_entails_memRegion_128 optProtoAuthenticatorAt_72_none
  optProtoAuthenticatorAt_72_none_entails_memRegion_48 optProtoAuthenticatorAt_some
  optProtoUnchunkedCt1SentAt_none optProtoUnchunkedCt1SentAt_none_entails_memRegion_128
  optProtoUnchunkedCt1SentAt_some protoAuthenticatorAt protoAuthenticatorAt_entails_dealloc
  protoUnchunked3VecHeadersAt protoUnchunked3VecHeadersAt_entails_memRegion_128
  protoUnchunkedCt1SentAt_entails_dealloc protoUnchunkedCt1SentSize
  stackAt_dropStack32_split stack_restore_32_allocHook tail_dealloc_unchunked_post
  twoVecHeadersAt_72_eq unchunkedCt1SentAt_entails_dealloc unchunkedCt1SentSize
  vecCapPtrDealloc
)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (
  dropOptProtoUnchunkedCt1SentSpec dropUnchunkedCt1SentSpec
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Drop.UnchunkedPlacedBudget

open Arm64 ProofLib
open ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

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
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, hp, hq⟩

private theorem sepWP_evs_dealloc {prog : Program} {target : BitVec 64}
    {s : State} (sz al : Nat)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm =>
      (Pm ⊢ P_evs (rustDeallocEvents sz al) sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ =>
    ⟨rustDeallocEvents sz al, LibsignalBinary.Heap.FreeOnlyEvs.singleton al sz, hp, hq⟩

private theorem sepWP_close_drop {prog : Program} {s0 s : State} {P : SepProp}
    {Post : State → SepProp → Prop}
    (Q_out : State → SepProp)
    (h : SepWP prog (s0.readReg64 .lr) s P (fun sf Pf =>
      (Pf ⊢ Q_out sf) ∧
      sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
      AllocCallPreserved s0 sf ∧ CalleeSavedPreserved s0 sf))
    (hpost : ∀ sf Pf, (Pf ⊢ Q_out sf) → sf.sp = s0.sp → sf.trace = s0.trace →
      AllocCallPreserved s0 sf → CalleeSavedPreserved s0 sf → Post sf Pf) :
    SepWP prog (s0.readReg64 .lr) s P Post :=
  SepWP.mono h fun sf Pf _ _ ⟨hp, hsp_f, htr_f, hacp_f, hcs_f⟩ =>
    hpost sf Pf hp hsp_f htr_f hacp_f hcs_f

private theorem protoUnchunked3Vec_auth_some_entails (A : RustAlloc) (a : BitVec 64)
    (g : ThreeVecGhost) (auth : ProtoAuthenticator) (Rest : SepProp) :
    protoUnchunked3VecHeadersAt a g ∗
      protoAuthenticatorAt A (a + 72#64) auth ∗
      memRegion (a + 120#64) 8 ∗
      vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
      vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
      vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗ Rest ⊢
    ∃∗ ga : TwoVecGhost,
      ⌜ga.v1.cap.toNat < 2 ^ 63⌝ ∗
      ((protoUnchunked3VecHeadersAt a g ∗
        (auth72HeadersAt a ga ∗
          vecCapPtrDealloc A ga.v1.cap ga.v1.ptr ∗
          vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
        memRegion (a + 120#64) 8 ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ Rest) := by
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (protoAuthenticatorAt_entails_dealloc A (a + 72#64) auth))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ga
  refine Entails.sepExists_right ga ?_
  rw [twoVecHeadersAt_72_eq]
  refine Entails.trans
    (Entails.of_eq (show _ =
      ⌜ga.v1.cap.toNat < 2 ^ 63⌝ ∗
      ((protoUnchunked3VecHeadersAt a g ∗
        (auth72HeadersAt a ga ∗
          vecCapPtrDealloc A ga.v1.cap ga.v1.ptr ∗
          vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
        memRegion (a + 120#64) 8 ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ Rest) by sep_ac_rfl))
    (Entails.refl _)

/-! ## 1. Block `444`: `drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#3]` -/

theorem drop_unchunked_ct1_sent_local1_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_444).rebase (blkPl_444).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_444).rebase (blkPl_444).base H) (blkPl_444).base
      (dropUnchunkedCt1SentSpec M A lim F) := by
  simp only [dropUnchunkedCt1SentSpec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [unchunkedCt1SentSize] at *
  wp_init x_st s0
  rcases x_st with ⟨⟨a, st⟩, st0⟩
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only [DropUnchunkedCt1SentGhost.a, DropUnchunkedCt1SentGhost.st] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre (sepConj_mono_left (unchunkedCt1SentAt_entails_dealloc A.repAlloc a st)) ?_
  rw [sepExists_sepConj_left]
  apply SepWP.exists_left; intro g
  refine seq_clean_evs (mid := (blkPl_444).base + 36#64)
    (P_evs := fun evs sm => (fiveVec128HeadersAt a g ∗
      vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
      vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
      vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
      vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr) ∗
      A.pool lim (M.stepEvents evs st0) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · refine seq_vm_clean (mid := (blkPl_444).base + 36#64)
        (P_mid := (fiveVec128HeadersAt a g ∗
          vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr) ∗
          A.pool lim st0 s0 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · by_vm_steps (
          dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          wp_steps; refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
      · intro sm hpcm hrunm hvmm ⟨⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hacpm, hx19m⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacpm
        rw [← A.pool_of_vmPreserved hvmm]
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        wp_done
    · refine seq_vm_clean (mid := (blkPl_444).base + 32#64)
        (P_mid := (fiveVec128HeadersAt a g ∗
          (A.live g.v1.ptr g.v1.cap.toNat 1 ∗ memRegion g.v1.ptr g.v1.cap.toNat) ∗
          vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr) ∗
          A.pool lim st0 s0 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
        (Q := fun sc => Saved32x19Preserved s0 sc (s0.sp - 32#64) ∧ AllocCallPreserved s0 sc ∧
          sc.readReg64 .x19 = a ∧ sc.readReg64 .x0 = g.v1.ptr ∧
          sc.readReg64 .x1 = g.v1.cap ∧ sc.readReg64 .x2 = 1#64)
        ?_ ?_
      · by_vm_steps (
          dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          wp_steps; refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
      · intro sc hpcc hrunc hvmc ⟨⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp_c, htrace, hvregs⟩, hacp_c, hx19_c, hx0_c, hx1_c, hx2_c⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_c
        rw [← A.pool_of_vmPreserved hvmc]
        apply sepWP_evs_dealloc g.v1.cap.toNat 1
        dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        wp_steps; wp_apply; rw [hsp_c]
        have hacp' : AllocCallPreserved s0 sf := hacp_c.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by sep_ac_rfl) ?_; wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    let st1 := M.stepEvents evs1 st0
    refine seq_clean_evs (mid := (blkPl_444).base + 56#64)
      (P_evs := fun evs sm => (fiveVec128HeadersAt a g ∗
        vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
        vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
        vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr) ∗
        A.pool lim (M.stepEvents evs st1) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
      · apply sepWP_evs_dealloc g.v2.cap.toNat 1
        wp_steps; wp_apply; rw [hsp_1]
        have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by sep_ac_rfl) ?_; wp_done
    · intro evs2 s2 hevs2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_2
      let st2 := M.stepEvents evs2 st1
      refine seq_clean_evs (mid := (blkPl_444).base + 76#64)
        (P_evs := fun evs sm => (fiveVec128HeadersAt a g ∗
          vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr) ∗
          A.pool lim (M.stepEvents evs st2) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
        · apply sepWP_evs_dealloc g.v3.cap.toNat 1
          wp_steps; wp_apply; rw [hsp_2]
          have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine align_pre_st (by sep_ac_rfl) ?_; wp_done
      · intro evs3 s3 hevs3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_3
        let st3 := M.stepEvents evs3 st2
        refine seq_clean_evs (mid := (blkPl_444).base + 96#64)
          (P_evs := fun evs sm => (fiveVec128HeadersAt a g ∗
            vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr) ∗
            A.pool lim (M.stepEvents evs st3) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
          (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
          ?_ ?_
        · dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hc4 : (g.v4.cap == 0#64) = true <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
          · apply sepWP_evs_dealloc g.v4.cap.toNat 1
            wp_steps; wp_apply; rw [hsp_3]
            have hacp' : AllocCallPreserved s0 sf := hacp_3.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            refine align_pre_st (by sep_ac_rfl) ?_; wp_done
        · intro evs4 s4 hevs4 hpc4 hrun4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hacp_4, hx19_4⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_4
          let st4 := M.stepEvents evs4 st3
          dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hc5 : (g.v5.cap == 0#64) = true <;>
            simp only [hc5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · refine sepWP_close_drop
              (fun sf => memRegion a 128 ∗
                A.pool lim (M.stepEvents (evs1 ++ evs2 ++ evs3 ++ evs4) st0) sf ∗
                stackAt s0.sp dropStack32) ?_
              (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
            · have heq_st : M.stepEvents (evs1 ++ evs2 ++ evs3 ++ evs4) st0 = st4 := by
                simp only [st1, st2, st3, st4, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
              rw [heq_st]
              wp_steps
              refine SepWP.weaken_pre (sepConj_mono
                (fiveVec128HeadersAt_entails_memRegion_128 a g)
                (sepConj_mono_right (stack_restore_32_allocHook s0.sp _ _ _ _))) ?_
              wp_done
            · rw [satisfies_sepExists]; refine ⟨evs1 ++ evs2 ++ evs3 ++ evs4, ?_⟩
              rw [satisfies_pure_sepConj]
              refine ⟨⟨htr_f, hacp_f, ((hevs1.append hevs2).append hevs3).append hevs4⟩, ?_⟩
              exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
          · refine sepWP_close_drop
              (fun sf => memRegion a 128 ∗
                A.pool lim (M.stepEvents (evs1 ++ evs2 ++ evs3 ++ evs4 ++ rustDeallocEvents g.v5.cap.toNat 1) st0) sf ∗
                stackAt s0.sp dropStack32) ?_
              (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
            · have heq_st : M.stepEvents (evs1 ++ evs2 ++ evs3 ++ evs4 ++ rustDeallocEvents g.v5.cap.toNat 1) st0 =
                  M.stepEvents (rustDeallocEvents g.v5.cap.toNat 1) st4 := by
                simp only [st1, st2, st3, st4, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
              rw [heq_st]
              have htail : SepWP ((blkPC_444).rebase (blkPl_444).base H) (s0.readReg64 .lr) s4
                  ((fiveVec128HeadersAt a g ∗
                    (A.live g.v5.ptr g.v5.cap.toNat 1 ∗ memRegion g.v5.ptr g.v5.cap.toNat)) ∗
                    A.pool lim st4 s4 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                    (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                     ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
                  (fun sf Pf =>
                    (Pf ⊢ memRegion a 128 ∗
                      A.pool lim (M.stepEvents (rustDeallocEvents g.v5.cap.toNat 1) st4) sf ∗
                      stackAt s0.sp dropStack32) ∧
                    sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
                    AllocCallPreserved s4 sf ∧ CalleeSavedPreserved s0 sf) := by
                dsimp only [fiveVec128HeadersAt]
                wp_steps
                refine SepWP.weaken_pre (sepConj_mono
                  (sepConj_mono_left (fiveVec128HeadersAt_entails_memRegion_128 a g))
                  (sepConj_mono_right (cells4_entails_stack32_bottom s0.sp _ _ _ _))) ?_
                wp_call hdealloc_fo (g.v5.ptr, g.v5.cap.toNat, 1, st4)
                have hpost4 : AllocCallPreserved s4 sf := by assumption
                rcases hpost4 with ⟨_, _, _, _, _, _, _⟩
                refine SepWP.weaken_pre
                  (tail_dealloc_unchunked_post a 128
                    (A.pool lim (M.stepEvents (rustDeallocEvents g.v5.cap.toNat 1) st4) sf) s0.sp) ?_
                wp_done
              exact SepWP.mono htail fun _ _ _ _ ⟨hp, hsp_f, htr_f, hacp_4f, hcs_f⟩ =>
                ⟨hp, hsp_f, htr_f, hacp_4.trans hacp_4f, hcs_f⟩
            · rw [satisfies_sepExists]
              refine ⟨evs1 ++ evs2 ++ evs3 ++ evs4 ++ rustDeallocEvents g.v5.cap.toNat 1, ?_⟩
              rw [satisfies_pure_sepConj]
              refine ⟨⟨htr_f, hacp_f, (((hevs1.append hevs2).append hevs3).append hevs4).append
                (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 g.v5.cap.toNat)⟩, ?_⟩
              exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

/-! ## 2. Block `436`: `drop_glue::<Option<proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#2]` -/

theorem drop_opt_proto_unchunked_ct1_sent_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_436).rebase (blkPl_436).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_436).rebase (blkPl_436).base H) (blkPl_436).base
      (dropOptProtoUnchunkedCt1SentSpec M A lim) := by
  simp only [dropOptProtoUnchunkedCt1SentSpec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [protoUnchunkedCt1SentSize] at *
  wp_init x_st s0
  rcases x_st with ⟨⟨a, optSt⟩, st0⟩
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only [DropOptProtoUnchunkedCt1SentGhost.a,
    DropOptProtoUnchunkedCt1SentGhost.optSt] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i fp_old lr_old x20_old x19_old
  cases optSt with
  | none =>
    rw [optProtoUnchunkedCt1SentAt_none]
    refine seq_vm_clean (mid := s0.readReg64 .lr)
      (P_mid := memRegion a 128 ∗ A.pool lim st0 s0 ∗ stackAt s0.sp dropStack32)
      (Q := fun sf => sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
        AllocCallPreserved s0 sf ∧ CalleeSavedPreserved s0 sf)
      ?_ ?_
    · by_vm_steps (
        wp_steps
        refine SepWP.weaken_pre (sepConj_mono
          (optProtoUnchunkedCt1SentAt_none_entails_memRegion_128 A.repAlloc a)
          (sepConj_mono_right (stack_restore_32_allocHook s0.sp _ _ _ _))) ?_
        refine align_pre_vm (by sep_ac_rfl) ?_
        wp_done)
    · intro sf hpcf hrunf hvmf ⟨hsp_f, htr_f, hacp_f, hcs_f⟩
      rw [← A.pool_of_vmPreserved hvmf]
      apply SepWP.done hpcf hrunf
      refine ⟨fun hm => ?_, hsp_f, hcs_f⟩
      rw [satisfies_sepExists]; refine ⟨[], ?_⟩
      rw [satisfies_pure_sepConj]
      refine ⟨⟨htr_f, hacp_f, LibsignalBinary.Heap.FreeOnlyEvs.nil⟩, ?_⟩
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  | some st =>
    rw [optProtoUnchunkedCt1SentAt_some]
    refine SepWP.weaken_pre
      (sepConj_mono_left (protoUnchunkedCt1SentAt_entails_dealloc A.repAlloc a st)) ?_
    rw [sepExists_sepConj_left]
    apply SepWP.exists_left; intro g
    wp_focus_pure; intro hcap1_lt
    have hne_none1 := cap_add_one_beq_zero_false hcap1_lt
    refine seq_clean_evs (mid := (blkPl_436).base + 76#64)
      (P_evs := fun evs sm => (protoUnchunked3VecHeadersAt a g ∗
        memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
        vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
        A.pool lim (M.stepEvents evs st0) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
        sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
      ?_ ?_
    · cases hauth : st.auth with
      | none =>
        rw [optProtoAuthenticatorAt_72_none]
        refine seq_vm_clean (mid := (blkPl_436).base + 76#64)
          (P_mid := (protoUnchunked3VecHeadersAt a g ∗
            (((a + 72#64) ↦₆₄ noneCap) ∗ memRegion (a + 80#64) 40) ∗
            memRegion (a + 120#64) 8 ∗
            vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
            vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
            vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
            A.pool lim st0 s0 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
          ?_ ?_
        · by_vm_steps (
            dsimp only [protoUnchunked3VecHeadersAt]
            wp_steps; refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
        · intro sm hpcm hrunm hvmm hqm
          rcases hqm with ⟨⟨_, _, _, _, _, _, _, _, _, _, _⟩, hacpm, _, _⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacpm
          rw [← A.pool_of_vmPreserved hvmm]
          apply sepWP_evs_nil
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
          refine SepWP.focus_weaken (optProtoAuthenticatorAt_72_none_entails_memRegion_48 A.repAlloc a) (by sep_focus) ?_
          refine align_pre_st (by sep_ac_rfl) ?_; wp_done
      | some auth =>
        rw [optProtoAuthenticatorAt_some]
        refine SepWP.weaken_pre
          (protoUnchunked3Vec_auth_some_entails A.repAlloc a g auth _) ?_
        apply SepWP.exists_left; intro ga
        wp_focus_pure; intro hga_lt
        have hne_none := cap_add_one_beq_zero_false hga_lt
        refine seq_clean_evs (mid := (blkPl_436).base + 56#64)
          (P_evs := fun evs sm => (protoUnchunked3VecHeadersAt a g ∗
            (auth72HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
            memRegion (a + 120#64) 8 ∗
            vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
            vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
            vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
            A.pool lim (M.stepEvents evs st0) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
          ?_ ?_
        · dsimp only [protoUnchunked3VecHeadersAt, auth72HeadersAt, vecCapPtrDealloc,
            LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
            simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · refine seq_vm_clean (mid := (blkPl_436).base + 56#64)
              (P_mid := (protoUnchunked3VecHeadersAt a g ∗
                (auth72HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
                memRegion (a + 120#64) 8 ∗
                vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
                vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
                vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
                A.pool lim st0 s0 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
              (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
                sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
              ?_ ?_
            · by_vm_steps (
                dsimp only [protoUnchunked3VecHeadersAt, auth72HeadersAt, vecCapPtrDealloc,
                  LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
                wp_steps; refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
            · intro sm hpcm hrunm hvmm ⟨⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hacpm, hx19m, hx20m⟩
              have ⟨_, _, _, _, _, _, _⟩ := hacpm
              rw [← A.pool_of_vmPreserved hvmm]
              apply sepWP_evs_nil
              simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
              dsimp only [protoUnchunked3VecHeadersAt, auth72HeadersAt, vecCapPtrDealloc,
                LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
              wp_done
          · refine seq_vm_clean (mid := (blkPl_436).base + 52#64)
              (P_mid := (protoUnchunked3VecHeadersAt a g ∗
                (auth72HeadersAt a ga ∗
                  (A.live ga.v1.ptr ga.v1.cap.toNat 1 ∗ memRegion ga.v1.ptr ga.v1.cap.toNat) ∗
                  vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
                memRegion (a + 120#64) 8 ∗
                vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
                vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
                vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
                A.pool lim st0 s0 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
              (Q := fun sc => Saved32x20Preserved s0 sc (s0.sp - 32#64) ∧ AllocCallPreserved s0 sc ∧
                sc.readReg64 .x19 = a ∧ sc.readReg64 .x20 = g.v1.cap ∧
                sc.readReg64 .x0 = ga.v1.ptr ∧ sc.readReg64 .x1 = ga.v1.cap ∧ sc.readReg64 .x2 = 1#64)
              ?_ ?_
            · by_vm_steps (
                dsimp only [protoUnchunked3VecHeadersAt, auth72HeadersAt, vecCapPtrDealloc,
                  LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
                wp_steps; refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
            · intro sc hpcc hrunc hvmc ⟨⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp_c, htrace, hvregs⟩, hacp_c, hx19_c, hx20_c, hx0_c, hx1_c, hx2_c⟩
              have ⟨_, _, _, _, _, _, _⟩ := hacp_c
              rw [← A.pool_of_vmPreserved hvmc]
              apply sepWP_evs_dealloc ga.v1.cap.toNat 1
              dsimp only [protoUnchunked3VecHeadersAt, auth72HeadersAt, vecCapPtrDealloc,
                LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
              wp_steps; wp_apply; rw [hsp_c]
              have hacp' : AllocCallPreserved s0 sf := hacp_c.trans (by assumption)
              rcases hacp' with ⟨_, _, _, _, _, _, _⟩
              refine align_pre_st (by sep_ac_rfl) ?_; wp_done
        · intro evsa1 sa1 hevsa1 hpca1 hruna1 ⟨⟨hx21_a1, hx22_a1, hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hacp_a1, hx19_a1, hx20_a1⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_a1
          let sta1 := M.stepEvents evsa1 st0
          have hstepa2 : SepWP ((blkPC_436).rebase (blkPl_436).base H) ((blkPl_436).base + 76#64) sa1
              ((protoUnchunked3VecHeadersAt a g ∗
                (auth72HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
                memRegion (a + 120#64) 8 ∗
                vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
                vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
                vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
                A.pool lim sta1 sa1 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
              (fun sm Pm =>
                ∃ evsa2, FreeOnlyEvs evsa2 ∧
                (Pm ⊢ (protoUnchunked3VecHeadersAt a g ∗
                  auth72HeadersAt a ga ∗
                  memRegion (a + 120#64) 8 ∗
                  vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
                  vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
                  vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
                  A.pool lim (M.stepEvents evsa2 sta1) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                  (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
                Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧
                sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap) := by
            dsimp only [auth72HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
              simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
            · apply sepWP_evs_dealloc ga.v2.cap.toNat 1
              wp_steps; wp_apply; rw [hsp_a1]
              have hacp' : AllocCallPreserved s0 sf := hacp_a1.trans (by assumption)
              rcases hacp' with ⟨_, _, _, _, _, _, _⟩
              refine align_pre_st (by sep_ac_rfl) ?_; wp_done
          refine SepWP.mono hstepa2 fun sm _Pm _ _ ⟨evsa2, hevsa2, hp, hq⟩ => ?_
          refine ⟨evsa1 ++ evsa2, hevsa1.append hevsa2, ?_, hq⟩
          have heq_sta : M.stepEvents (evsa1 ++ evsa2) st0 = M.stepEvents evsa2 sta1 := by
            simp only [sta1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          rw [heq_sta]
          exact Entails.trans hp
            (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
              (auth72HeadersAt_entails_memRegion_48 a ga))))
    · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1, hx20_1⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_1
      let st1 := M.stepEvents evs1 st0
      refine seq_clean_evs (mid := (blkPl_436).base + 96#64)
        (P_evs := fun evs sm => (protoUnchunked3VecHeadersAt a g ∗
          memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
          vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
          A.pool lim (M.stepEvents evs st1) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hc1 : (g.v1.cap == 0#64) = true <;>
          simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
        · apply sepWP_evs_dealloc g.v1.cap.toNat 1
          wp_steps; wp_apply; rw [hsp_1]
          have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine align_pre_st (by sep_ac_rfl) ?_; wp_done
      · intro evs2 s2 hevs2 hpc2 hrun2 ⟨⟨hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_2
        let st2 := M.stepEvents evs2 st1
        refine seq_clean_evs (mid := (blkPl_436).base + 116#64)
          (P_evs := fun evs sm => (protoUnchunked3VecHeadersAt a g ∗
            memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
            vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
            A.pool lim (M.stepEvents evs st2) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
          ?_ ?_
        · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hc2 : (g.v2.cap == 0#64) = true <;>
            simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
          · apply sepWP_evs_dealloc g.v2.cap.toNat 1
            wp_steps; wp_apply; rw [hsp_2]
            have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            refine align_pre_st (by sep_ac_rfl) ?_; wp_done
        · intro evs3 s3 hevs3 hpc3 hrun3 ⟨⟨hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_3
          let st3 := M.stepEvents evs3 st2
          dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hc3 : (g.v3.cap == 0#64) = true <;>
            simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · refine sepWP_close_drop
              (fun sf => memRegion a 128 ∗
                A.pool lim (M.stepEvents (evs1 ++ evs2 ++ evs3) st0) sf ∗
                stackAt s0.sp dropStack32) ?_
              (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
            · have heq_st : M.stepEvents (evs1 ++ evs2 ++ evs3) st0 = st3 := by
                simp only [st1, st2, st3, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
              rw [heq_st]
              wp_steps
              refine SepWP.weaken_pre (sepConj_mono
                (protoUnchunked3VecHeadersAt_entails_memRegion_128 a g)
                (sepConj_mono_right (stack_restore_32_allocHook s0.sp _ _ _ _))) ?_
              wp_done
            · rw [satisfies_sepExists]; refine ⟨evs1 ++ evs2 ++ evs3, ?_⟩
              rw [satisfies_pure_sepConj]
              refine ⟨⟨htr_f, hacp_f, (hevs1.append hevs2).append hevs3⟩, ?_⟩
              exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
          · refine sepWP_close_drop
              (fun sf => memRegion a 128 ∗
                A.pool lim (M.stepEvents (evs1 ++ evs2 ++ evs3 ++ rustDeallocEvents g.v3.cap.toNat 1) st0) sf ∗
                stackAt s0.sp dropStack32) ?_
              (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
            · have heq_st : M.stepEvents (evs1 ++ evs2 ++ evs3 ++ rustDeallocEvents g.v3.cap.toNat 1) st0 =
                  M.stepEvents (rustDeallocEvents g.v3.cap.toNat 1) st3 := by
                simp only [st1, st2, st3, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
              rw [heq_st]
              have htail : SepWP ((blkPC_436).rebase (blkPl_436).base H) (s0.readReg64 .lr) s3
                  ((protoUnchunked3VecHeadersAt a g ∗
                    memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
                    (A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat)) ∗
                    A.pool lim st3 s3 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                    (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                     ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
                  (fun sf Pf =>
                    (Pf ⊢ memRegion a 128 ∗
                      A.pool lim (M.stepEvents (rustDeallocEvents g.v3.cap.toNat 1) st3) sf ∗
                      stackAt s0.sp dropStack32) ∧
                    sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
                    AllocCallPreserved s3 sf ∧ CalleeSavedPreserved s0 sf) := by
                dsimp only [protoUnchunked3VecHeadersAt]
                wp_steps
                refine SepWP.weaken_pre (sepConj_mono
                  (Entails.trans
                    (Entails.of_eq (show _ =
                      (protoUnchunked3VecHeadersAt a g ∗ memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8) ∗
                      (A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) by
                        unfold protoUnchunked3VecHeadersAt; sep_ac_rfl))
                    (sepConj_mono_left (protoUnchunked3VecHeadersAt_entails_memRegion_128 a g)))
                  (sepConj_mono_right (cells4_entails_stack32_bottom s0.sp _ _ _ _))) ?_
                wp_call hdealloc_fo (g.v3.ptr, g.v3.cap.toNat, 1, st3)
                have hpost3 : AllocCallPreserved s3 sf := by assumption
                rcases hpost3 with ⟨_, _, _, _, _, _, _⟩
                refine SepWP.weaken_pre
                  (tail_dealloc_unchunked_post a 128
                    (A.pool lim (M.stepEvents (rustDeallocEvents g.v3.cap.toNat 1) st3) sf) s0.sp) ?_
                wp_done
              exact SepWP.mono htail fun _ _ _ _ ⟨hp, hsp_f, htr_f, hacp_3f, hcs_f⟩ =>
                ⟨hp, hsp_f, htr_f, hacp_3.trans hacp_3f, hcs_f⟩
            · rw [satisfies_sepExists]
              refine ⟨evs1 ++ evs2 ++ evs3 ++ rustDeallocEvents g.v3.cap.toNat 1, ?_⟩
              rw [satisfies_pure_sepConj]
              refine ⟨⟨htr_f, hacp_f, ((hevs1.append hevs2).append hevs3).append
                (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 g.v3.cap.toNat)⟩, ?_⟩
              exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

theorem drop_unchunked_ct1_sent_local1_placed
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_444 H) (blkPl_444).base (dropUnchunkedCt1SentSpec M A lim F) :=
  drop_unchunked_ct1_sent_local1_placed_ok
    (CryptoVerification.SpqrV1.Alloc.spqr_hook_ok_of_mem hdealloc)

private theorem hookSat_dealloc_withPanics [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim) := by
  rcases hdealloc with ⟨f, hf, hok⟩
  exact ⟨f, by simp [Rust.withPanics, Rust.isPanicSymbol, hf], hok⟩

theorem drop_unchunked_ct1_sent_local1_placed_x
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_444 (Rust.withPanics ext)) (blkPl_444).base
      (dropUnchunkedCt1SentSpec M A lim F) :=
  drop_unchunked_ct1_sent_local1_placed (hookSat_dealloc_withPanics hdealloc)

theorem drop_unchunked_ct1_sent_local1_placed_lscl
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [CryptoVerification.IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (CryptoVerification.lsmpl.base 444)
      (CryptoVerification.withLsCodeLoaded CryptoVerification.lsmpl
        (dropUnchunkedCt1SentSpec M A lim F)) :=
  CryptoVerification.ls_subroutine_ok_of_block (callerProg := callerProg)
    (CryptoVerification.subroutine_ok_withLsCodeLoaded_of_plain
      (drop_unchunked_ct1_sent_local1_placed hdealloc)) hi

theorem drop_unchunked_ct1_sent_local1_placed_cl
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [CryptoVerification.IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (CryptoVerification.lsmpl.base 444)
      (CryptoVerification.withLsCl CryptoVerification.lsmpl
        (dropUnchunkedCt1SentSpec M A lim F)) :=
  CryptoVerification.ls_subroutine_ok_cl_of_plain (callerProg := callerProg)
    (drop_unchunked_ct1_sent_local1_placed hdealloc) hi

theorem drop_opt_proto_unchunked_ct1_sent_placed
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_436 H) (blkPl_436).base (dropOptProtoUnchunkedCt1SentSpec M A lim) :=
  drop_opt_proto_unchunked_ct1_sent_placed_ok
    (CryptoVerification.SpqrV1.Alloc.spqr_hook_ok_of_mem hdealloc)

theorem drop_opt_proto_unchunked_ct1_sent_placed_x
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_436 (Rust.withPanics ext)) (blkPl_436).base
      (dropOptProtoUnchunkedCt1SentSpec M A lim) :=
  drop_opt_proto_unchunked_ct1_sent_placed (hookSat_dealloc_withPanics hdealloc)

theorem drop_opt_proto_unchunked_ct1_sent_placed_lscl
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [CryptoVerification.IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (CryptoVerification.lsmpl.base 436)
      (CryptoVerification.withLsCodeLoaded CryptoVerification.lsmpl
        (dropOptProtoUnchunkedCt1SentSpec M A lim)) :=
  CryptoVerification.ls_subroutine_ok_of_block (callerProg := callerProg)
    (CryptoVerification.subroutine_ok_withLsCodeLoaded_of_plain
      (drop_opt_proto_unchunked_ct1_sent_placed hdealloc)) hi

theorem drop_opt_proto_unchunked_ct1_sent_placed_cl
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [CryptoVerification.IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (CryptoVerification.lsmpl.base 436)
      (CryptoVerification.withLsCl CryptoVerification.lsmpl
        (dropOptProtoUnchunkedCt1SentSpec M A lim)) :=
  CryptoVerification.ls_subroutine_ok_cl_of_plain (callerProg := callerProg)
    (drop_opt_proto_unchunked_ct1_sent_placed hdealloc) hi

end LibsignalBinary.Proofs.Cli.SpqrV1.Drop.UnchunkedPlacedBudget
