/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aBudgetDropUnchunked
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
# Fixed-Offset `ProtoPolynomialEncoder` Drop Helper for `Variant7aBudget`

Proves `drop_glue_proto_poly_encoder_ok_ext` on `dropProgAtExt b ext` under `AllocContracts4K`
and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aBudgetAux

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
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec dropProtoPolyEncoderSpecBase)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (
  dropProtoUnchunkedCt1SentEkReceivedSpec dropUnchunkedCt1SentSpec
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

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aBudgetDropUnchunked (
  drop_unchunked_ct1_sent_local2_ok_ext
  drop_proto_unchunked_ct1_sent_ek_received_ok_ext
)

/-! ## 3. Fixed-Offset `drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>` -/

private theorem drop_proto_poly_encoder_body1
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc_fo : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "__rustc::__rust_dealloc"))
      (deallocFreeOnlySpec M A lim))
    (s0 : State) (fsp a ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 48#64 → s.status = .Running →
      Saved48Preserved s0 s fsp → AllocCallPreserved s0 s →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptr →
      s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 36#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc_fo
  drop_fetches_sym b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" 208
  dsimp only [dropProgAtExt, dropProtoPolyEncoderName, BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" = entry
  examples_hide_fetches
  intro cur cnt bs st s Frame hpc hrun hpres hacp hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro cap
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro vptr
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved48Preserved]
  by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 36#64) s
        (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
            A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
      dsimp only [Saved48Preserved]; wp_steps; wp_done
    exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
      ⟨Entails.trans hp (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hq⟩
  · apply sepWP_evs_dealloc cap.toNat 1
    have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 36#64) s
        (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
          (A.live vptr cap.toNat 1 ∗ memRegion vptr cap.toNat)) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
            A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
      dsimp only [Saved48Preserved]; wp_steps; wp_apply
      have hacp' : AllocCallPreserved s0 sf := hacp.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      wp_steps; rw [hsp]; wp_done
    exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
      ⟨Entails.trans hp (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hq⟩

private theorem drop_proto_poly_encoder_loop1
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc_fo : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "__rustc::__rust_dealloc"))
      (deallocFreeOnlySpec M A lim))
    (s0 : State) (fsp a ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 48#64 → s.status = .Running →
      Saved48Preserved s0 s fsp → AllocCallPreserved s0 s →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptr →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 72#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr) := by
  have hbody := drop_proto_poly_encoder_body1 (b := b) (ext := ext) hdealloc_fo s0 fsp a ptr hfsp_align
  drop_fetches_sym b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" 208
  dsimp only [dropProgAtExt, dropProtoPolyEncoderName, BitVec.ofNat_eq_ofNat] at hbody ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" = fnEntry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur st s Frame _ hlen hpc hrun hpres hacp hx19 hx20 hx21 hx22
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean_evs (mid := fnEntry + 36#64)
      (P_evs := fun evs sm => memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
        stackAt fsp allocHookStack ∗ (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
        sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs st s _ hpc hrun hpres hacp hx19 hx20 hx21 hx22) ?_
    intro evs_hd s1 hevs_hd hpc1 hrun1 ⟨hpres1, hacp1, hx19_1, hx20_1, hx21_1, hx22_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp1
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      have hfin : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (fnEntry + 72#64) s1
          (memRegion cur 24 ∗ A.pool lim (M.stepEvents evs_hd st) s1 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs_hd st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr) := by
        dsimp only [Saved48Preserved]; wp_steps; wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs_hd, hevs_hd, hp, hq⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx21_1
      refine seq_clean_st (mid := fnEntry + 48#64)
        (P_mid := fun sm => arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool lim (M.stepEvents evs_hd st) sm ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun s2 => Saved48Preserved s0 s2 fsp ∧ AllocCallPreserved s0 s2 ∧
          s2.readReg64 .x19 = a ∧ s2.readReg64 .x20 = ptr ∧
          s2.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧ s2.readReg64 .x22 = cur + 32#64)
        ?_ ?_
      · rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
        rw [sep_push_body]; wp_steps
        apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
        refine ⟨?_, ?_⟩
        · simp only [wp_norm, arm64_norm]; exact Entails.refl _
        · refine ⟨by simp [Saved48Preserved, wp_norm, arm64_norm, *],
            hacp1.trans (by simp [AllocCallPreserved, wp_norm, arm64_norm]),
            by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
            by simp [wp_norm, arm64_norm, *], ?_⟩
          simp [wp_norm, arm64_norm, hx22_1]
      · intro s2 hpc2 hrun2 ⟨hpres2, hacp2, hx19_2, hx20_2, hx21_2, hx22_2⟩
        have hrec := ih (cur + 24#64) (M.stepEvents evs_hd st) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hacp2 hx19_2 hx20_2 hx21_2
          (by rw [hx22_2, add_24_add_8])
        refine SepWP.mono hrec fun sf _Pf _ _ ⟨evs_tl, hevs_tl, hp, hq⟩ => ?_
        refine ⟨evs_hd ++ evs_tl, hevs_hd.append hevs_tl, ?_, hq⟩
        rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        refine Entails.trans hp ?_
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

private theorem drop_proto_poly_encoder_body2
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc_fo : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "__rustc::__rust_dealloc"))
      (deallocFreeOnlySpec M A lim))
    (s0 : State) (fsp a ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 128#64 → s.status = .Running →
      Saved48Preserved s0 s fsp → AllocCallPreserved s0 s →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptr →
      s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 116#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc_fo
  drop_fetches_sym b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" 208
  dsimp only [dropProgAtExt, dropProtoPolyEncoderName, BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" = entry
  examples_hide_fetches
  intro cur cnt bs st s Frame hpc hrun hpres hacp hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro cap
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro vptr
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, Saved48Preserved]
  by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 116#64) s
        (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
            A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
      dsimp only [Saved48Preserved]; wp_steps; wp_done
    exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
      ⟨Entails.trans hp (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hq⟩
  · apply sepWP_evs_dealloc cap.toNat 1
    have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 116#64) s
        (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
          (A.live vptr cap.toNat 1 ∗ memRegion vptr cap.toNat)) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
            A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
      dsimp only [Saved48Preserved]; wp_steps; wp_apply
      have hacp' : AllocCallPreserved s0 sf := hacp.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      wp_steps; rw [hsp]; wp_done
    exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
      ⟨Entails.trans hp (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hq⟩

private theorem drop_proto_poly_encoder_loop2
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc_fo : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "__rustc::__rust_dealloc"))
      (deallocFreeOnlySpec M A lim))
    (s0 : State) (fsp a ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 128#64 → s.status = .Running →
      Saved48Preserved s0 s fsp → AllocCallPreserved s0 s →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptr →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 152#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr) := by
  have hbody := drop_proto_poly_encoder_body2 (b := b) (ext := ext) hdealloc_fo s0 fsp a ptr hfsp_align
  drop_fetches_sym b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" 208
  dsimp only [dropProgAtExt, dropProtoPolyEncoderName, BitVec.ofNat_eq_ofNat] at hbody ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" = fnEntry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur st s Frame _ hlen hpc hrun hpres hacp hx19 hx20 hx21 hx22
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean_evs (mid := fnEntry + 116#64)
      (P_evs := fun evs sm => memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
        stackAt fsp allocHookStack ∗ (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
        sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs st s _ hpc hrun hpres hacp hx19 hx20 hx21 hx22) ?_
    intro evs_hd s1 hevs_hd hpc1 hrun1 ⟨hpres1, hacp1, hx19_1, hx20_1, hx21_1, hx22_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp1
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      have hfin : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (fnEntry + 152#64) s1
          (memRegion cur 24 ∗ A.pool lim (M.stepEvents evs_hd st) s1 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs_hd st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptr) := by
        dsimp only [Saved48Preserved]; wp_steps; wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs_hd, hevs_hd, hp, hq⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx21_1
      refine seq_clean_st (mid := fnEntry + 128#64)
        (P_mid := fun sm => arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool lim (M.stepEvents evs_hd st) sm ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun s2 => Saved48Preserved s0 s2 fsp ∧ AllocCallPreserved s0 s2 ∧
          s2.readReg64 .x19 = a ∧ s2.readReg64 .x20 = ptr ∧
          s2.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧ s2.readReg64 .x22 = cur + 32#64)
        ?_ ?_
      · rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
        rw [sep_push_body]; wp_steps
        apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
        refine ⟨?_, ?_⟩
        · simp only [wp_norm, arm64_norm]; exact Entails.refl _
        · refine ⟨by simp [Saved48Preserved, wp_norm, arm64_norm, *],
            hacp1.trans (by simp [AllocCallPreserved, wp_norm, arm64_norm]),
            by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
            by simp [wp_norm, arm64_norm, *], ?_⟩
          simp [wp_norm, arm64_norm, hx22_1]
      · intro s2 hpc2 hrun2 ⟨hpres2, hacp2, hx19_2, hx20_2, hx21_2, hx22_2⟩
        have hrec := ih (cur + 24#64) (M.stepEvents evs_hd st) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hacp2 hx19_2 hx20_2 hx21_2
          (by rw [hx22_2, add_24_add_8])
        refine SepWP.mono hrec fun sf _Pf _ _ ⟨evs_tl, hevs_tl, hp, hq⟩ => ?_
        refine ⟨evs_hd ++ evs_tl, hevs_hd.append hevs_tl, ?_, hq⟩
        rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        refine Entails.trans hp ?_
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

/-- Fixed-offset `core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>`
satisfies `dropProtoPolyEncoderSpecBase M A lim` on `dropProgAtExt b ext` under `AllocContracts4K b A lim ext`. -/
theorem drop_glue_proto_poly_encoder_ok_ext
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName)
      (dropProtoPolyEncoderSpecBase M A lim) := by
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "__rustc::__rust_dealloc"))
      (rustCliDeallocBudgetSpecBase M A lim) :=
    hA.dealloc_ok_at dropProtoPolyEncoderName
      (num% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "__rustc::__rust_dealloc"))
      (by simp only [dropProtoPolyEncoderName, fnOff_drop_proto_poly_encoder, stubOff_rust_dealloc, arm64_norm])
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  have hloop1 := drop_proto_poly_encoder_loop1 (b := b) (ext := ext) hdealloc_fo
  have hloop2 := drop_proto_poly_encoder_loop2 (b := b) (ext := ext) hdealloc_fo
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpecBase] at hdealloc_fo
  simp only [dropProtoPolyEncoderSpecBase]
  dsimp only [protoPolynomialEncoderSize] at *
  apply subroutine_ok_of_sepWP_init
  rintro ⟨⟨a, pb⟩, st⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [DropProtoPolyEncoderGhost.a, DropProtoPolyEncoderGhost.pb] at hpre ⊢
  have hpre' : s0.mem ⊨ ⌜s0.readReg64 .x0 = a⌝ ∗
      ((protoPolynomialEncoderAt A.repAlloc a pb ∗ A.pool lim st s0 ∗ stackAt s0.sp dropStack48) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨hx0, hpre'⟩
  refine ⟨_, hpre', ?_⟩
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 hsp_align (by decide)
  refine SepWP.weaken_pre (sepConj_mono_left (protoPolyEncoderAt_entails_dealloc A.repAlloc a pb)) ?_
  dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  wp_pull_exists; rename_i g
  nth_rw 1 [stackAt_dropStack48_split s0.sp]; cells_unfold; wp_pull_exists; wp_focus_pure
  rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne, hpolys_le, hpolys_cap_lt, hpolys_ptr_ne⟩
  refine seq_clean_evs (mid := (dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 72#64)
    (P_evs := fun evs sm =>
      (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      (if g.pts.cap = 0 then emp
       else A.live g.pts.ptr (g.pts.cap.toNat * 24) 8 ∗ memRegion g.pts.ptr (g.pts.cap.toNat * 24)) ∗
      ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
      (if g.polys.cap = 0 then emp
       else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
         arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.polys.ptr pb.polys ∗
         memRegion (g.polys.ptr + BitVec.ofNat 64 (pb.polys.length * 24)) ((g.polys.cap.toNat - pb.polys.length) * 24)) ∗
      memRegion (a + 48#64) 8 ∗ A.pool lim (M.stepEvents evs st) sm ∗
      stackAt (s0.sp - 48#64) allocHookStack ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
      sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.pts.ptr) ?_ ?_
  · generalize hxs : pb.pts = xs at hpts_le ⊢
    cases xs with
    | nil =>
      simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, arrayAt, emp_sepConj]
      refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
        (mid := (dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 72#64)
        (P_mid :=
          (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
          (if g.pts.cap = 0 then emp
           else A.live g.pts.ptr (g.pts.cap.toNat * 24) 8 ∗ memRegion g.pts.ptr (g.pts.cap.toNat * 24)) ∗
          ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
          (if g.polys.cap = 0 then emp
           else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
             arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.polys.ptr pb.polys ∗
             memRegion (g.polys.ptr + BitVec.ofNat 64 (pb.polys.length * 24)) ((g.polys.cap.toNat - pb.polys.length) * 24)) ∗
          memRegion (a + 48#64) 8 ∗ A.pool lim st s0 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.pts.ptr) ?_ ?_
      · drop_fetches_sym b trapHooks "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" 208
        dsimp only [dropProgAtExt, dropProtoPolyEncoderName, BitVec.ofNat_eq_ofNat] at *
        rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" = entry
        examples_hide_fetches
        by_vm_steps {
          wp_steps
          apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, *])
          refine ⟨by simp [wp_norm, arm64_norm], ?_,
            by simp [Saved48Preserved, AllocCallPreserved, wp_norm, arm64_norm, *]⟩
          dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x29, Reg.x30]
          try simp only [wp_norm, arm64_norm]
          exact Entails.of_eq (by sep_ac_rfl)
        }
      · intro sm hpcm hrunm hvmm ⟨hpresm, hacpm, hx19m, hx20m⟩
        rw [← A.pool_of_vmPreserved hvmm]
        apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        dsimp only [dropProgAtExt, dropProtoPolyEncoderName, BitVec.ofNat_eq_ofNat] at hpcm ⊢
        exact SepWP.done hpcm hrunm ⟨Entails.refl _, hpresm, hacpm, hx19m, hx20m⟩
    | cons bs tl =>
      have hlen_pos : 0 < (bs :: tl).length := by simp
      have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
        have : (bs :: tl).length * 24 ≤ g.pts.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le; omega
      have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
      have hcap_ne : g.pts.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
      simp only [hcap_ne, ↓reduceIte]
      refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
        (mid := (dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 48#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.pts.ptr (bs :: tl) ∗
          A.pool lim st s0 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
          ((a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
           ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
           A.live g.pts.ptr (g.pts.cap.toNat * 24) 8 ∗
           memRegion (g.pts.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.pts.cap.toNat - (bs :: tl).length) * 24) ∗
           ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
           ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
           (if g.polys.cap = 0 then emp
            else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
              arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.polys.ptr pb.polys ∗
              memRegion (g.polys.ptr + BitVec.ofNat 64 (pb.polys.length * 24)) ((g.polys.cap.toNat - pb.polys.length) * 24)) ∗
           memRegion (a + 48#64) 8 ∗
           (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.pts.ptr ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.pts.ptr + 8#64) ?_ ?_
      · drop_fetches_sym b trapHooks "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" 208
        dsimp only [dropProgAtExt, dropProtoPolyEncoderName, BitVec.ofNat_eq_ofNat] at *
        rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" = entry
        examples_hide_fetches
        by_vm_steps {
          wp_steps
          apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, *])
          refine ⟨by simp [wp_norm, arm64_norm], ?_,
            by simp [Saved48Preserved, AllocCallPreserved, wp_norm, arm64_norm, *]⟩
          dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x29, Reg.x30]
          try simp only [wp_norm, arm64_norm]
          exact Entails.of_eq (by sep_ac_rfl)
        }
      · intro s_loop hpc_loop hrun_loop hvm_loop ⟨hpres_loop, hacp_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
        rw [← A.pool_of_vmPreserved hvm_loop]
        refine SepWP.mono
          (hloop1 s0 (s0.sp - 48#64) a g.pts.ptr hfsp_align (bs :: tl) g.pts.ptr st s_loop _
            (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop hacp_loop
            hx19_loop hx20_loop hx21_loop hx22_loop) ?_
        intro sm _Pm _ _ ⟨evs, hevs, hp, hq⟩
        refine ⟨evs, hevs, Entails.trans hp ?_, hq⟩
        have hsplit : g.pts.cap.toNat * 24 =
            (bs :: tl).length * 24 + (g.pts.cap.toNat - (bs :: tl).length) * 24 := by
          rw [← Nat.add_mul]; congr 1; omega
        have hbound : (bs :: tl).length * 24 + (g.pts.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; omega
        conv_rhs =>
          arg 2; arg 2; arg 2; arg 1; arg 2
          rw [hsplit, ProofLib.memRegion_split g.pts.ptr ((bs :: tl).length * 24)
                ((g.pts.cap.toNat - (bs :: tl).length) * 24) hbound]
        exact Entails.of_eq (by sep_ac_rfl)
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1, hx20_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    let st1 := M.stepEvents evs1 st
    refine seq_clean_evs (mid := (dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 100#64)
      (P_evs := fun evs sm =>
        (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        (if g.polys.cap = 0 then emp
         else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.polys.ptr pb.polys ∗
           memRegion (g.polys.ptr + BitVec.ofNat 64 (pb.polys.length * 24)) ((g.polys.cap.toNat - pb.polys.length) * 24)) ∗
        memRegion (a + 48#64) 8 ∗ A.pool lim (M.stepEvents evs st1) sm ∗
        stackAt (s0.sp - 48#64) allocHookStack ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
    · drop_fetches_sym b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" 208
      dsimp only [dropProgAtExt, dropProtoPolyEncoderName, Saved48Preserved, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" = entry1
      examples_hide_fetches
      by_cases hc : g.pts.cap = 0#64
      · have hc_beq : (g.pts.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
        simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp]
        apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps; wp_done
      · have hc_beq : ¬((g.pts.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
        have hlsl := cap_mul_24 hpts_cap_lt
        simp only [hc, ↓reduceIte]
        apply sepWP_evs_dealloc (g.pts.cap.toNat * 24) 8
        wp_steps
        wp_call hdealloc_fo (g.pts.ptr, g.pts.cap.toNat * 24, 8, st1)
        rw [hsp_1]
        have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        wp_done
    · intro evs2 s2 hevs2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_2
      let st2 := M.stepEvents evs2 st1
      refine seq_clean_evs (mid := (dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 152#64)
        (P_evs := fun evs sm =>
          (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
          (if g.polys.cap = 0 then emp
           else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗ memRegion g.polys.ptr (g.polys.cap.toNat * 24)) ∗
          memRegion (a + 48#64) 8 ∗ A.pool lim (M.stepEvents evs st2) sm ∗
          stackAt (s0.sp - 48#64) allocHookStack ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.polys.ptr) ?_ ?_
      · generalize hys : pb.polys = ys at hpolys_le ⊢
        cases ys with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
            BitVec.add_zero, arrayAt, emp_sepConj]
          refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
            (mid := (dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 152#64)
            (P_mid :=
              (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
              ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
              ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
              (if g.polys.cap = 0 then emp
               else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗ memRegion g.polys.ptr (g.polys.cap.toNat * 24)) ∗
              memRegion (a + 48#64) 8 ∗ A.pool lim st2 s2 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
              (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.polys.ptr) ?_ ?_
          · drop_fetches_sym b trapHooks "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" 208
            dsimp only [dropProgAtExt, dropProtoPolyEncoderName, BitVec.ofNat_eq_ofNat] at *
            rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
            generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
              "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" = entry
            examples_hide_fetches
            by_vm_steps {
              wp_steps
              apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, *])
              refine ⟨by simp [wp_norm, arm64_norm], ?_,
                by simp [Saved48Preserved, AllocCallPreserved, wp_norm, arm64_norm, *]⟩
              try simp only [wp_norm, arm64_norm]
              exact Entails.of_eq (by sep_ac_rfl)
            }
          · intro sm hpcm hrunm hvmm ⟨hpresm, hacpm, hx19m, hx20m⟩
            rw [← A.pool_of_vmPreserved hvmm]
            apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
            dsimp only [dropProgAtExt, dropProtoPolyEncoderName, BitVec.ofNat_eq_ofNat] at hpcm ⊢
            exact SepWP.done hpcm hrunm ⟨Entails.refl _, hpresm, hacpm, hx19m, hx20m⟩
        | cons bs tl =>
          have hlen_pos : 0 < (bs :: tl).length := by simp
          have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
            have : (bs :: tl).length * 24 ≤ g.polys.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpolys_le; omega
          have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
          have hcap_ne : g.polys.cap ≠ 0 := by intro hc0; rw [hc0] at hpolys_le; simp at hpolys_le
          simp only [hcap_ne, ↓reduceIte]
          refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
            (mid := (dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + 128#64)
            (P_mid := arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.polys.ptr (bs :: tl) ∗
              A.pool lim st2 s2 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
              ((a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
               ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
               ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
               ((a + 40#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
               A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
               memRegion (g.polys.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.polys.cap.toNat - (bs :: tl).length) * 24) ∗
               memRegion (a + 48#64) 8 ∗
               (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.polys.ptr ∧
              sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.polys.ptr + 8#64) ?_ ?_
          · drop_fetches_sym b trapHooks "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" 208
            dsimp only [dropProgAtExt, dropProtoPolyEncoderName, BitVec.ofNat_eq_ofNat] at *
            rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
            generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
              "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" = entry
            examples_hide_fetches
            by_vm_steps {
              wp_steps
              apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, *])
              refine ⟨by simp [wp_norm, arm64_norm], ?_,
                by simp [Saved48Preserved, AllocCallPreserved, wp_norm, arm64_norm, *]⟩
              try simp only [wp_norm, arm64_norm]
              exact Entails.of_eq (by sep_ac_rfl)
            }
          · intro s_loop hpc_loop hrun_loop hvm_loop ⟨hpres_loop, hacp_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
            rw [← A.pool_of_vmPreserved hvm_loop]
            refine SepWP.mono
              (hloop2 s0 (s0.sp - 48#64) a g.polys.ptr hfsp_align (bs :: tl) g.polys.ptr st2 s_loop _
                (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop hacp_loop
                hx19_loop hx20_loop hx21_loop hx22_loop) ?_
            intro sm _Pm _ _ ⟨evs, hevs, hp, hq⟩
            refine ⟨evs, hevs, Entails.trans hp ?_, hq⟩
            have hsplit : g.polys.cap.toNat * 24 =
                (bs :: tl).length * 24 + (g.polys.cap.toNat - (bs :: tl).length) * 24 := by
              rw [← Nat.add_mul]; congr 1; omega
            have hbound : (bs :: tl).length * 24 + (g.polys.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
              rw [← hsplit]; omega
            conv_rhs =>
              arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; arg 1; arg 2
              rw [hsplit, ProofLib.memRegion_split g.polys.ptr ((bs :: tl).length * 24)
                    ((g.polys.cap.toNat - (bs :: tl).length) * 24) hbound]
            exact Entails.of_eq (by sep_ac_rfl)
      · intro evs3 s3 hevs3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3, hx20_3⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_3
        let st3 := M.stepEvents evs3 st2
        drop_fetches_sym b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" 208
        dsimp only [dropProgAtExt, dropProtoPolyEncoderName, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc3 ⊢
        generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" = entry3
        examples_hide_fetches
        by_cases hc : g.polys.cap = 0#64
        · have hc_beq : (g.polys.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
          simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp]
          refine sepWP_close_drop
            (fun sf => memRegion a 56 ∗ A.pool lim (M.stepEvents (evs1 ++ evs2 ++ evs3) st) sf ∗ stackAt s0.sp dropStack48) ?_
            (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
          · have heq_st3 : M.stepEvents (evs1 ++ evs2 ++ evs3) st = st3 := by
              simp only [st1, st2, st3, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
            rw [heq_st3]; wp_steps
            refine SepWP.focus_weaken
              (protoPolyEncoderHeaders_entails_memRegion_56 a g.pts.cap g.pts.ptr
                (BitVec.ofNat 64 pb.pts.length) 0#64 g.polys.ptr (BitVec.ofNat 64 pb.polys.length))
              (by sep_focus) ?_
            refine SepWP.focus_weaken
              (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
              (by sep_focus) ?_
            wp_done
          · try rw [sepExists_sepConj_left]
            rw [satisfies_sepExists]; refine ⟨evs1 ++ evs2 ++ evs3, ?_⟩
            repeat rw [sepConj_assoc]
            rw [satisfies_pure_sepConj]; refine ⟨⟨htr_f, hacp_f, (hevs1.append hevs2).append hevs3⟩, ?_⟩
            exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
        · have hc_beq : ¬((g.polys.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
          have hlsl := cap_mul_24 hpolys_cap_lt
          simp only [hc, ↓reduceIte]
          refine sepWP_close_drop
            (fun sf => memRegion a 56 ∗ A.pool lim (M.stepEvents (evs1 ++ evs2 ++ evs3 ++ rustDeallocEvents (g.polys.cap.toNat * 24) 8) st) sf ∗ stackAt s0.sp dropStack48) ?_
            (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
          · have heq_st4 : M.stepEvents (evs1 ++ evs2 ++ evs3 ++ rustDeallocEvents (g.polys.cap.toNat * 24) 8) st =
                M.stepEvents (rustDeallocEvents (g.polys.cap.toNat * 24) 8) st3 := by
              simp only [st1, st2, st3, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
            rw [heq_st4]
            have htail : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 .lr) s3
                ((a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
                  ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
                  ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
                  ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
                  (A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗ memRegion g.polys.ptr (g.polys.cap.toNat * 24)) ∗
                  memRegion (a + 48#64) 8 ∗ A.pool lim st3 s3 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
                  (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
                (fun sf Pf =>
                  (Pf ⊢ memRegion a 56 ∗ A.pool lim (M.stepEvents (rustDeallocEvents (g.polys.cap.toNat * 24) 8) st3) sf ∗ stackAt s0.sp dropStack48) ∧
                  sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ AllocCallPreserved s3 sf ∧ CalleeSavedPreserved s0 sf) := by
              wp_steps
              refine SepWP.focus_weaken
                (protoPolyEncoderHeaders_entails_memRegion_56 a g.pts.cap g.pts.ptr
                  (BitVec.ofNat 64 pb.pts.length) g.polys.cap g.polys.ptr (BitVec.ofNat 64 pb.polys.length))
                (by sep_focus) ?_
              refine SepWP.focus_weaken
                (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                  (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
                (by sep_focus) ?_
              rw [stackAt_dropStack48_split_bottom s0.sp]
              wp_call hdealloc_fo (g.polys.ptr, g.polys.cap.toNat * 24, 8, st3)
              have hpost3 : AllocCallPreserved s3 sf := by assumption
              rcases hpost3 with ⟨_, _, _, _, _, _, _⟩
              wp_done
            exact SepWP.mono htail fun _ _ _ _ ⟨hp, hsp_f, htr_f, hacp_3f, hcs_f⟩ =>
              ⟨hp, hsp_f, htr_f, hacp_3.trans hacp_3f, hcs_f⟩
          · try rw [sepExists_sepConj_left]
            rw [satisfies_sepExists]
            refine ⟨evs1 ++ evs2 ++ evs3 ++ rustDeallocEvents (g.polys.cap.toNat * 24) 8, ?_⟩
            repeat rw [sepConj_assoc]
            rw [satisfies_pure_sepConj]
            refine ⟨⟨htr_f, hacp_f, ((hevs1.append hevs2).append hevs3).append
              (LibsignalBinary.Heap.FreeOnlyEvs.singleton 8 (g.polys.cap.toNat * 24))⟩, ?_⟩
            exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aBudgetAux
