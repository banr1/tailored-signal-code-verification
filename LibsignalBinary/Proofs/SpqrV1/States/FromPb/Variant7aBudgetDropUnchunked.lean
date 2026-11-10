/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscBudgetAux
public meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
meta import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Drop.Decodes
meta import LibsignalBinary.Proofs.SpqrV1.Drop.Decodes -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Fixed-Offset Unchunked `Ct1Sent` Drop Helpers for `Variant7aBudget`

Proves `drop_unchunked_ct1_sent_local2_ok_ext` and `drop_proto_unchunked_ct1_sent_ek_received_ok_ext`
on `dropProgAtExt b ext` under `AllocContracts4K` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aBudgetDropUnchunked

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.LibsignalSpqrV1 (ProtoAuthenticator ProtoPolynomialEncoder V1State)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop (
  DropProtoPolyEncoderGhost DropProtoUnchunkedCt1SentEkReceivedGhost DropUnchunkedCt1SentGhost
  Saved32x19Preserved Saved48Preserved ThreeVecGhost TwoVecGhost
  add_24_add_8 auth72HeadersAt auth72HeadersAt_entails_memRegion_48
  cap_add_one_beq_zero_false cap_mul_24 cells4_entails_stack32_bottom cons_len_mul
  dropProtoPolyEncoderName dropProtoUnchunkedCt1SentEkReceivedName dropProgAtExt
  dropStack32 dropStack48 dropUnchunkedCt1SentLocal2Name
  fiveVec128HeadersAt fiveVec128HeadersAt_entails_memRegion_128
  header_cells_entails_memRegion_24 ofNat_add_one_beq_one_false_24
  ofNat_beq_zero_false_24 ofNat_succ_eq_add_one
  optProtoAuthenticatorAt_72_none optProtoAuthenticatorAt_72_none_entails_memRegion_48
  optProtoAuthenticatorAt_some protoAuthenticatorAt protoAuthenticatorAt_entails_dealloc
  protoPolyEncoderAt_entails_dealloc protoPolyEncoderHeaders_entails_memRegion_56
  protoUnchunked3VecHeadersAt protoUnchunked3VecHeadersAt_entails_memRegion_128
  protoUnchunkedCt1SentEkReceivedAt protoUnchunkedCt1SentEkReceivedAt_entails_dealloc
  protoUnchunkedCt1SentEkReceivedSize sep_pull_body sep_push_body sep_rejoin_loop
  stackAt_dropStack32_split stackAt_dropStack48_split stackAt_dropStack48_split_bottom
  stack_restore_32_allocHook stack_restore_48_allocHook
  tail_dealloc_unchunked_post tail_len_mul_lt twoVecHeadersAt_72_eq
  unchunkedCt1SentAt unchunkedCt1SentAt_entails_dealloc unchunkedCt1SentSize
  vecCapPtrDealloc vecU8_entails_capPtr_dealloc
)
open CryptoVerification.SpqrV1.Poly (protoPolynomialEncoderAt protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Layout.Stubs (
  fnOff_drop_ct1_sent_local2 fnOff_drop_proto_ct1_sent_ek_received
  fnOff_drop_proto_poly_encoder stubOff_rust_dealloc
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpecBase rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget (AllocContracts4K)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (
  dropProtoUnchunkedCt1SentEkReceivedSpecBase dropUnchunkedCt1SentSpecBase
)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscBudgetAux (
  deallocFreeOnlySpec fnAddr_rebase_hooks_eq sepWP_evs_dealloc sepWP_evs_nil
  seq_clean_evs seq_clean_st seq_vm_clean subroutine_ok_deallocFreeOnly
)
open scoped CryptoVerification.CodeLayout

open Lean Elab Tactic ProofLib ProofLib.ProgramReflection in
scoped elab "drop_fetches_sym " b:term:max H:term:max sym:str len:num : tactic => do
  let eOff ← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff sym.getString
  let hfn := mkCIdentFrom sym eOff.decl
  let offLit := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic|
    code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.SpqrV1.Drop.spqrDropChainEpochBin $b $H $hfn $offLit $len))

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem align_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (heq : P = P_mid s)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) := by
  subst heq; exact h

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

/-! ## 1. Fixed-Offset `drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]` -/

/-- Fixed-offset `core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]`
satisfies `dropUnchunkedCt1SentSpecBase M A lim F` on `dropProgAtExt b ext` under `AllocContracts4K b A lim ext`. -/
theorem drop_unchunked_ct1_sent_local2_ok_ext
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropUnchunkedCt1SentLocal2Name)
      (dropUnchunkedCt1SentSpecBase M A lim F) := by
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropUnchunkedCt1SentLocal2Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]" "__rustc::__rust_dealloc"))
      (rustCliDeallocBudgetSpecBase M A lim) :=
    hA.dealloc_ok_at dropUnchunkedCt1SentLocal2Name
      (num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]" "__rustc::__rust_dealloc"))
      (by simp only [dropUnchunkedCt1SentLocal2Name, fnOff_drop_ct1_sent_local2, stubOff_rust_dealloc, arm64_norm])
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc_fo
  simp only [dropUnchunkedCt1SentSpecBase]
  dsimp only [unchunkedCt1SentSize] at *
  apply subroutine_ok_of_sepWP_init
  rintro ⟨⟨a, st⟩, st0⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [DropUnchunkedCt1SentGhost.a, DropUnchunkedCt1SentGhost.st] at hpre ⊢
  have hpre' : s0.mem ⊨ ⌜s0.readReg64 .x0 = a⌝ ∗
      ((unchunkedCt1SentAt A.repAlloc a st ∗ A.pool lim st0 s0 ∗ stackAt s0.sp dropStack32) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨hx0, hpre'⟩
  refine ⟨_, hpre', ?_⟩
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 hsp_align (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]
  cells_unfold; wp_pull_exists; rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre (sepConj_mono_left (unchunkedCt1SentAt_entails_dealloc A.repAlloc a st)) ?_
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro g
  refine seq_clean_evs (mid := (dropProgAtExt b ext).fnAddr dropUnchunkedCt1SentLocal2Name + 36#64)
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
    · refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
        (mid := (dropProgAtExt b ext).fnAddr dropUnchunkedCt1SentLocal2Name + 36#64)
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
      · drop_fetches_sym b trapHooks "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]" 136
        dsimp only [dropProgAtExt, dropUnchunkedCt1SentLocal2Name, fiveVec128HeadersAt, vecCapPtrDealloc,
          LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, BitVec.ofNat_eq_ofNat] at *
        rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]" = entry
        examples_hide_fetches
        by_vm_steps {
          wp_steps
          apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, *])
          refine ⟨by simp [wp_norm, arm64_norm], ?_,
            by simp [Saved32x19Preserved, AllocCallPreserved, wp_norm, arm64_norm, *]⟩
          dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x29, Reg.x30]
          simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)
        }
      · intro sm hpcm hrunm hvmm ⟨hpresm, hacpm, hx19m⟩
        rw [← A.pool_of_vmPreserved hvmm]
        apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        dsimp only [dropProgAtExt, dropUnchunkedCt1SentLocal2Name, BitVec.ofNat_eq_ofNat] at hpcm ⊢
        exact SepWP.done hpcm hrunm ⟨Entails.refl _, hpresm, hacpm, hx19m⟩
    · refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
        (mid := (dropProgAtExt b ext).fnAddr dropUnchunkedCt1SentLocal2Name + 32#64)
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
      · drop_fetches_sym b trapHooks "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]" 136
        dsimp only [dropProgAtExt, dropUnchunkedCt1SentLocal2Name, fiveVec128HeadersAt, vecCapPtrDealloc,
          LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, BitVec.ofNat_eq_ofNat] at *
        rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]" = entry
        examples_hide_fetches
        by_vm_steps {
          wp_steps
          apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, *])
          refine ⟨by simp [wp_norm, arm64_norm], ?_,
            by simp [Saved32x19Preserved, AllocCallPreserved, wp_norm, arm64_norm, *]⟩
          dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x29, Reg.x30]
          simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)
        }
      · intro sc hpcc hrunc hvmc ⟨⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp_c, htrace, hvregs⟩, hacp_c, hx19_c, hx0_c, hx1_c, hx2_c⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_c
        rw [← A.pool_of_vmPreserved hvmc]
        drop_fetches_sym b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]" 136
        dsimp only [dropProgAtExt, dropUnchunkedCt1SentLocal2Name, fiveVec128HeadersAt, vecCapPtrDealloc,
          LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpcc ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]" = entry
        examples_hide_fetches
        apply sepWP_evs_dealloc g.v1.cap.toNat 1
        wp_steps; wp_apply; rw [hsp_c]
        have hacp' : AllocCallPreserved s0 sf := hacp_c.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        dsimp only [Saved32x19Preserved]
        refine align_pre_st (by sep_ac_rfl) ?_; wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    let st1 := M.stepEvents evs1 st0
    drop_fetches_sym b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]" 136
    dsimp only [dropProgAtExt, dropUnchunkedCt1SentLocal2Name, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]" = fnEntry
    examples_hide_fetches
    refine seq_clean_evs (mid := fnEntry + 56#64)
      (P_evs := fun evs sm => (fiveVec128HeadersAt a g ∗
        vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
        vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
        vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr) ∗
        A.pool lim (M.stepEvents evs st1) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32x19Preserved]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;> simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
      · apply sepWP_evs_dealloc g.v2.cap.toNat 1
        wp_steps; wp_apply; rw [hsp_1]
        have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by sep_ac_rfl) ?_; wp_done
    · intro evs2 s2 hevs2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_2
      let st2 := M.stepEvents evs2 st1
      refine seq_clean_evs (mid := fnEntry + 76#64)
        (P_evs := fun evs sm => (fiveVec128HeadersAt a g ∗
          vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr) ∗
          A.pool lim (M.stepEvents evs st2) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32x19Preserved]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;> simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
        · apply sepWP_evs_dealloc g.v3.cap.toNat 1
          wp_steps; wp_apply; rw [hsp_2]
          have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine align_pre_st (by sep_ac_rfl) ?_; wp_done
      · intro evs3 s3 hevs3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_3
        let st3 := M.stepEvents evs3 st2
        refine seq_clean_evs (mid := fnEntry + 96#64)
          (P_evs := fun evs sm => (fiveVec128HeadersAt a g ∗
            vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr) ∗
            A.pool lim (M.stepEvents evs st3) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
          (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
          ?_ ?_
        · dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32x19Preserved]
          by_cases hc4 : (g.v4.cap == 0#64) = true <;> simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
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
          by_cases hc5 : (g.v5.cap == 0#64) = true <;> simp only [hc5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · refine sepWP_close_drop
              (fun sf => memRegion a 128 ∗ A.pool lim (M.stepEvents (evs1 ++ evs2 ++ evs3 ++ evs4) st0) sf ∗ stackAt s0.sp dropStack32) ?_
              (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
            · have heq_st : M.stepEvents (evs1 ++ evs2 ++ evs3 ++ evs4) st0 = st4 := by
                simp only [st1, st2, st3, st4, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
              rw [heq_st]; wp_steps
              refine SepWP.weaken_pre (sepConj_mono (fiveVec128HeadersAt_entails_memRegion_128 a g)
                (sepConj_mono_right (stack_restore_32_allocHook s0.sp _ _ _ _))) ?_
              wp_done
            · try rw [sepExists_sepConj_left]
              rw [satisfies_sepExists]; refine ⟨evs1 ++ evs2 ++ evs3 ++ evs4, ?_⟩
              repeat rw [sepConj_assoc]
              rw [satisfies_pure_sepConj]
              refine ⟨⟨htr_f, hacp_f, ((hevs1.append hevs2).append hevs3).append hevs4⟩, ?_⟩
              exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
          · refine sepWP_close_drop
              (fun sf => memRegion a 128 ∗ A.pool lim (M.stepEvents (evs1 ++ evs2 ++ evs3 ++ evs4 ++ rustDeallocEvents g.v5.cap.toNat 1) st0) sf ∗ stackAt s0.sp dropStack32) ?_
              (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
            · have heq_st : M.stepEvents (evs1 ++ evs2 ++ evs3 ++ evs4 ++ rustDeallocEvents g.v5.cap.toNat 1) st0 =
                  M.stepEvents (rustDeallocEvents g.v5.cap.toNat 1) st4 := by
                simp only [st1, st2, st3, st4, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
              rw [heq_st]
              have htail : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 .lr) s4
                  ((fiveVec128HeadersAt a g ∗ (A.live g.v5.ptr g.v5.cap.toNat 1 ∗ memRegion g.v5.ptr g.v5.cap.toNat)) ∗
                    A.pool lim st4 s4 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                    (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                     ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
                  (fun sf Pf =>
                    (Pf ⊢ memRegion a 128 ∗ A.pool lim (M.stepEvents (rustDeallocEvents g.v5.cap.toNat 1) st4) sf ∗ stackAt s0.sp dropStack32) ∧
                    sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ AllocCallPreserved s4 sf ∧ CalleeSavedPreserved s0 sf) := by
                dsimp only [fiveVec128HeadersAt]; wp_steps
                refine SepWP.weaken_pre (sepConj_mono (sepConj_mono_left (fiveVec128HeadersAt_entails_memRegion_128 a g))
                  (sepConj_mono_right (cells4_entails_stack32_bottom s0.sp _ _ _ _))) ?_
                wp_call hdealloc_fo (g.v5.ptr, g.v5.cap.toNat, 1, st4)
                have hpost4 : AllocCallPreserved s4 sf := by assumption
                rcases hpost4 with ⟨_, _, _, _, _, _, _⟩
                refine SepWP.weaken_pre
                  (tail_dealloc_unchunked_post a 128 (A.pool lim (M.stepEvents (rustDeallocEvents g.v5.cap.toNat 1) st4) sf) s0.sp) ?_
                wp_done
              exact SepWP.mono htail fun _ _ _ _ ⟨hp, hsp_f, htr_f, hacp_4f, hcs_f⟩ =>
                ⟨hp, hsp_f, htr_f, hacp_4.trans hacp_4f, hcs_f⟩
            · try rw [sepExists_sepConj_left]
              rw [satisfies_sepExists]; refine ⟨evs1 ++ evs2 ++ evs3 ++ evs4 ++ rustDeallocEvents g.v5.cap.toNat 1, ?_⟩
              repeat rw [sepConj_assoc]
              rw [satisfies_pure_sepConj]
              refine ⟨⟨htr_f, hacp_f, (((hevs1.append hevs2).append hevs3).append hevs4).append
                (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 g.v5.cap.toNat)⟩, ?_⟩
              exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

/-! ## 2. Fixed-Offset `drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>` -/

/-- Fixed-offset `core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>`
satisfies `dropProtoUnchunkedCt1SentEkReceivedSpecBase M A lim` on `dropProgAtExt b ext` under `AllocContracts4K b A lim ext`. -/
theorem drop_proto_unchunked_ct1_sent_ek_received_ok_ext
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoUnchunkedCt1SentEkReceivedName)
      (dropProtoUnchunkedCt1SentEkReceivedSpecBase M A lim) := by
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoUnchunkedCt1SentEkReceivedName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>" "__rustc::__rust_dealloc"))
      (rustCliDeallocBudgetSpecBase M A lim) :=
    hA.dealloc_ok_at dropProtoUnchunkedCt1SentEkReceivedName
      (num% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>" "__rustc::__rust_dealloc"))
      (by simp only [dropProtoUnchunkedCt1SentEkReceivedName, fnOff_drop_proto_ct1_sent_ek_received, stubOff_rust_dealloc, arm64_norm])
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc_fo
  simp only [dropProtoUnchunkedCt1SentEkReceivedSpecBase]
  dsimp only [protoUnchunkedCt1SentEkReceivedSize] at *
  apply subroutine_ok_of_sepWP_init
  rintro ⟨⟨a, st⟩, st0⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [DropProtoUnchunkedCt1SentEkReceivedGhost.a,
    DropProtoUnchunkedCt1SentEkReceivedGhost.st] at hpre ⊢
  have hpre' : s0.mem ⊨ ⌜s0.readReg64 .x0 = a⌝ ∗
      ((protoUnchunkedCt1SentEkReceivedAt A.repAlloc a st ∗ A.pool lim st0 s0 ∗ stackAt s0.sp dropStack32) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨hx0, hpre'⟩
  refine ⟨_, hpre', ?_⟩
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 hsp_align (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]
  cells_unfold; wp_pull_exists; rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre
    (sepConj_mono_left (protoUnchunkedCt1SentEkReceivedAt_entails_dealloc A.repAlloc a st)) ?_
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro g
  wp_focus_pure; intro _
  refine seq_clean_evs (mid := (dropProgAtExt b ext).fnAddr dropProtoUnchunkedCt1SentEkReceivedName + 64#64)
    (P_evs := fun evs sm => (protoUnchunked3VecHeadersAt a g ∗
      memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
      vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
      vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
      vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
      A.pool lim (M.stepEvents evs st0) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · cases hauth : st.auth with
    | none =>
      rw [optProtoAuthenticatorAt_72_none]
      refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
        (mid := (dropProgAtExt b ext).fnAddr dropProtoUnchunkedCt1SentEkReceivedName + 64#64)
        (P_mid := (protoUnchunked3VecHeadersAt a g ∗
          (((a + 72#64) ↦₆₄ noneCap) ∗ memRegion (a + 80#64) 40) ∗
          memRegion (a + 120#64) 8 ∗
          vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
          A.pool lim st0 s0 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · drop_fetches_sym b trapHooks "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>" 144
        dsimp only [dropProgAtExt, dropProtoUnchunkedCt1SentEkReceivedName, BitVec.ofNat_eq_ofNat] at *
        rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>" = entry
        examples_hide_fetches
        by_vm_steps {
          wp_steps
          apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, *])
          refine ⟨by simp [wp_norm, arm64_norm], ?_,
            by simp [Saved32x19Preserved, AllocCallPreserved, wp_norm, arm64_norm, *]⟩
          dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x29, Reg.x30]
          simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)
        }
      · intro sm hpcm hrunm hvmm ⟨hpresm, hacpm, hx19m⟩
        rw [← A.pool_of_vmPreserved hvmm]
        apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        refine SepWP.focus_weaken (optProtoAuthenticatorAt_72_none_entails_memRegion_48 A.repAlloc a) (by sep_focus) ?_
        dsimp only [dropProgAtExt, dropProtoUnchunkedCt1SentEkReceivedName, BitVec.ofNat_eq_ofNat] at hpcm ⊢
        exact SepWP.done hpcm hrunm ⟨Entails.of_eq (by sep_ac_rfl), hpresm, hacpm, hx19m⟩
    | some auth =>
      rw [optProtoAuthenticatorAt_some]
      refine SepWP.weaken_pre (protoUnchunked3Vec_auth_some_entails A.repAlloc a g auth _) ?_
      apply SepWP.exists_left; intro ga
      wp_focus_pure; intro hga_lt
      have hne_none := cap_add_one_beq_zero_false hga_lt
      refine seq_clean_evs (mid := (dropProgAtExt b ext).fnAddr dropProtoUnchunkedCt1SentEkReceivedName + 44#64)
        (P_evs := fun evs sm => (protoUnchunked3VecHeadersAt a g ∗
          (auth72HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
          memRegion (a + 120#64) 8 ∗
          vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
          A.pool lim (M.stepEvents evs st0) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · dsimp only [auth72HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
          simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
            (mid := (dropProgAtExt b ext).fnAddr dropProtoUnchunkedCt1SentEkReceivedName + 44#64)
            (P_mid := (protoUnchunked3VecHeadersAt a g ∗
              (auth72HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
              memRegion (a + 120#64) 8 ∗
              vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
              vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
              A.pool lim st0 s0 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
              (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
            (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
            ?_ ?_
          · drop_fetches_sym b trapHooks "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>" 144
            dsimp only [dropProgAtExt, dropProtoUnchunkedCt1SentEkReceivedName, auth72HeadersAt, vecCapPtrDealloc,
              LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, BitVec.ofNat_eq_ofNat] at *
            rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
            generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
              "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>" = entry
            examples_hide_fetches
            by_vm_steps {
              wp_steps
              apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, *])
              refine ⟨by simp [wp_norm, arm64_norm], ?_,
                by simp [Saved32x19Preserved, AllocCallPreserved, wp_norm, arm64_norm, *]⟩
              dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x29, Reg.x30]
              simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)
            }
          · intro sm hpcm hrunm hvmm ⟨hpresm, hacpm, hx19m⟩
            rw [← A.pool_of_vmPreserved hvmm]
            apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
            dsimp only [dropProgAtExt, dropProtoUnchunkedCt1SentEkReceivedName, BitVec.ofNat_eq_ofNat] at hpcm ⊢
            exact SepWP.done hpcm hrunm ⟨Entails.refl _, hpresm, hacpm, hx19m⟩
        · refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
            (mid := (dropProgAtExt b ext).fnAddr dropProtoUnchunkedCt1SentEkReceivedName + 40#64)
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
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
            (Q := fun sc => Saved32x19Preserved s0 sc (s0.sp - 32#64) ∧ AllocCallPreserved s0 sc ∧
              sc.readReg64 .x19 = a ∧ sc.readReg64 .x0 = ga.v1.ptr ∧
              sc.readReg64 .x1 = ga.v1.cap ∧ sc.readReg64 .x2 = 1#64)
            ?_ ?_
          · drop_fetches_sym b trapHooks "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>" 144
            dsimp only [dropProgAtExt, dropProtoUnchunkedCt1SentEkReceivedName, auth72HeadersAt, vecCapPtrDealloc,
              LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, BitVec.ofNat_eq_ofNat] at *
            rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
            generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
              "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>" = entry
            examples_hide_fetches
            by_vm_steps {
              wp_steps
              apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, *])
              refine ⟨by simp [wp_norm, arm64_norm], ?_,
                by simp [Saved32x19Preserved, AllocCallPreserved, wp_norm, arm64_norm, *]⟩
              dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x29, Reg.x30]
              simp only [wp_norm, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)
            }
          · intro sc hpcc hrunc hvmc ⟨⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp_c, htrace, hvregs⟩, hacp_c, hx19_c, hx0_c, hx1_c, hx2_c⟩
            have ⟨_, _, _, _, _, _, _⟩ := hacp_c
            rw [← A.pool_of_vmPreserved hvmc]
            drop_fetches_sym b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>" 144
            dsimp only [dropProgAtExt, dropProtoUnchunkedCt1SentEkReceivedName, auth72HeadersAt, vecCapPtrDealloc,
              LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpcc ⊢
            generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
              "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>" = entry
            examples_hide_fetches
            apply sepWP_evs_dealloc ga.v1.cap.toNat 1
            wp_steps; wp_apply; rw [hsp_c]
            have hacp' : AllocCallPreserved s0 sf := hacp_c.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            dsimp only [Saved32x19Preserved]
            refine align_pre_st (by sep_ac_rfl) ?_; wp_done
      · intro evsa1 sa1 hevsa1 hpca1 hruna1 ⟨⟨hx20_a1, hx21_a1, hx22_a1, hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hacp_a1, hx19_a1⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_a1
        let sta1 := M.stepEvents evsa1 st0
        drop_fetches_sym b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>" 144
        dsimp only [dropProgAtExt, dropProtoUnchunkedCt1SentEkReceivedName, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpca1 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>" = entryA
        examples_hide_fetches
        have hstepa2 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entryA + 64#64) sa1
            ((protoUnchunked3VecHeadersAt a g ∗
              (auth72HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
              memRegion (a + 120#64) 8 ∗
              vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
              vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
              A.pool lim sta1 sa1 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
              (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
            (fun sm Pm =>
              ∃ evsa2, FreeOnlyEvs evsa2 ∧
              (Pm ⊢ (protoUnchunked3VecHeadersAt a g ∗ auth72HeadersAt a ga ∗
                memRegion (a + 120#64) 8 ∗
                vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
                vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
                vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
                A.pool lim (M.stepEvents evsa2 sta1) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old))) ∧
              Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) := by
          dsimp only [auth72HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32x19Preserved]
          by_cases hca2 : (ga.v2.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
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
          (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (auth72HeadersAt_entails_memRegion_48 a ga))))
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    let st1 := M.stepEvents evs1 st0
    drop_fetches_sym b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>" 144
    dsimp only [dropProgAtExt, dropProtoUnchunkedCt1SentEkReceivedName, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>" = fnEntry
    examples_hide_fetches
    refine seq_clean_evs (mid := fnEntry + 84#64)
      (P_evs := fun evs sm => (protoUnchunked3VecHeadersAt a g ∗
        memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
        vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
        A.pool lim (M.stepEvents evs st1) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32x19Preserved]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
      · apply sepWP_evs_dealloc g.v1.cap.toNat 1
        wp_steps; wp_apply; rw [hsp_1]
        have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by sep_ac_rfl) ?_; wp_done
    · intro evs2 s2 hevs2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_2
      let st2 := M.stepEvents evs2 st1
      refine seq_clean_evs (mid := fnEntry + 104#64)
        (P_evs := fun evs sm => (protoUnchunked3VecHeadersAt a g ∗
          memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
          vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
          A.pool lim (M.stepEvents evs st2) sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved32x19Preserved]
        by_cases hc2 : (g.v2.cap == 0#64) = true <;> simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]; wp_steps; wp_done
        · apply sepWP_evs_dealloc g.v2.cap.toNat 1
          wp_steps; wp_apply; rw [hsp_2]
          have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine align_pre_st (by sep_ac_rfl) ?_; wp_done
      · intro evs3 s3 hevs3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_3
        let st3 := M.stepEvents evs3 st2
        dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;> simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · refine sepWP_close_drop
            (fun sf => memRegion a 128 ∗ A.pool lim (M.stepEvents (evs1 ++ evs2 ++ evs3) st0) sf ∗ stackAt s0.sp dropStack32) ?_
            (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
          · have heq_st : M.stepEvents (evs1 ++ evs2 ++ evs3) st0 = st3 := by
              simp only [st1, st2, st3, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
            rw [heq_st]; wp_steps
            refine SepWP.weaken_pre (sepConj_mono (protoUnchunked3VecHeadersAt_entails_memRegion_128 a g)
              (sepConj_mono_right (stack_restore_32_allocHook s0.sp _ _ _ _))) ?_
            wp_done
          · try rw [sepExists_sepConj_left]
            rw [satisfies_sepExists]; refine ⟨evs1 ++ evs2 ++ evs3, ?_⟩
            repeat rw [sepConj_assoc]
            rw [satisfies_pure_sepConj]
            refine ⟨⟨htr_f, hacp_f, (hevs1.append hevs2).append hevs3⟩, ?_⟩
            exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
        · refine sepWP_close_drop
            (fun sf => memRegion a 128 ∗ A.pool lim (M.stepEvents (evs1 ++ evs2 ++ evs3 ++ rustDeallocEvents g.v3.cap.toNat 1) st0) sf ∗ stackAt s0.sp dropStack32) ?_
            (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
          · have heq_st : M.stepEvents (evs1 ++ evs2 ++ evs3 ++ rustDeallocEvents g.v3.cap.toNat 1) st0 =
                M.stepEvents (rustDeallocEvents g.v3.cap.toNat 1) st3 := by
              simp only [st1, st2, st3, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
            rw [heq_st]
            have htail : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 .lr) s3
                ((protoUnchunked3VecHeadersAt a g ∗ memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
                  (A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat)) ∗
                  A.pool lim st3 s3 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                  (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
                (fun sf Pf =>
                  (Pf ⊢ memRegion a 128 ∗ A.pool lim (M.stepEvents (rustDeallocEvents g.v3.cap.toNat 1) st3) sf ∗ stackAt s0.sp dropStack32) ∧
                  sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ AllocCallPreserved s3 sf ∧ CalleeSavedPreserved s0 sf) := by
              dsimp only [protoUnchunked3VecHeadersAt]; wp_steps
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
                (tail_dealloc_unchunked_post a 128 (A.pool lim (M.stepEvents (rustDeallocEvents g.v3.cap.toNat 1) st3) sf) s0.sp) ?_
              wp_done
            exact SepWP.mono htail fun _ _ _ _ ⟨hp, hsp_f, htr_f, hacp_3f, hcs_f⟩ =>
              ⟨hp, hsp_f, htr_f, hacp_3.trans hacp_3f, hcs_f⟩
          · try rw [sepExists_sepConj_left]
            rw [satisfies_sepExists]; refine ⟨evs1 ++ evs2 ++ evs3 ++ rustDeallocEvents g.v3.cap.toNat 1, ?_⟩
            repeat rw [sepConj_assoc]
            rw [satisfies_pure_sepConj]
            refine ⟨⟨htr_f, hacp_f, ((hevs1.append hevs2).append hevs3).append
              (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 g.v3.cap.toNat)⟩, ?_⟩
            exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aBudgetDropUnchunked
