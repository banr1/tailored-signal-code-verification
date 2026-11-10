/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPoly
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.DecodesPlaced
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Relocatable `Option<proto::pq_ratchet::PolynomialEncoder>` Drop Glue (Block `435`)

Proves `drop_glue_opt_proto_poly_encoder_placed_ok` and `drop_opt_proto_poly_encoder_placed_ok`
(plus `HookSat` and `withPanics` wrappers) on Block `435` (`lsProg_435 H`) under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.SpqrV1.Drop.Placed

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp]
private theorem optProtoPolynomialEncoderAt_none (A : RustAlloc) (a : BitVec 64) :
    optProtoPolynomialEncoderAt A a none =
      ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) optProtoPolynomialEncoderNoneTailSize) := rfl

@[local simp]
private theorem optProtoPolynomialEncoderAt_some (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialEncoder) :
    optProtoPolynomialEncoderAt A a (some pb) = protoPolynomialEncoderAt A a pb := rfl

private theorem drop_opt_proto_poly_encoder_cli_placed_body1 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_435).rebase (blkPl_435).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp a ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (blkPl_435).base + 64#64 →
      s.status = .Running → Saved64Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptsPtr → s.readReg64 .x21 = ptsCap →
      s.readReg64 .x22 = cnt → s.readReg64 .x23 = cur + 8#64 →
      SepWP ((blkPC_435).rebase (blkPl_435).base H) ((blkPl_435).base + 52#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptsPtr ∧
          sm.readReg64 .x21 = ptsCap ∧ sm.readReg64 .x22 = cnt ∧ sm.readReg64 .x23 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc
  intro cur cnt bs s Frame hpc hrun hpres hx19 hx20 hx21 hx22 hx23
  rcases hpres with ⟨hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap
  apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP ((blkPC_435).rebase (blkPl_435).base H) ((blkPl_435).base + 52#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptsPtr ∧
        sm.readReg64 .x21 = ptsCap ∧ sm.readReg64 .x22 = cnt ∧ sm.readReg64 .x23 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const
    (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep

private theorem drop_opt_proto_poly_encoder_cli_placed_loop1 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_435).rebase (blkPl_435).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp a ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_435).base + 64#64 →
      s.status = .Running → Saved64Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptsPtr → s.readReg64 .x21 = ptsCap →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length → s.readReg64 .x23 = cur + 8#64 →
      SepWP ((blkPC_435).rebase (blkPl_435).base H) ((blkPl_435).base + 88#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧
          sm.readReg64 .x20 = ptsPtr ∧ sm.readReg64 .x21 = ptsCap) := by
  have hbody := drop_opt_proto_poly_encoder_cli_placed_body1 hdealloc s0 fsp a ptsPtr ptsCap hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22 hx23
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := (blkPl_435).base + 52#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧
        sm.readReg64 .x20 = ptsPtr ∧ sm.readReg64 .x21 = ptsCap ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x23 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx19 hx20 hx21 hx22 hx23) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx22_1 ⊢
      rcases hpres1 with ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx22_1
      refine seq_clean (mid := (blkPl_435).base + 64#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧
          sm.readReg64 .x20 = ptsPtr ∧ sm.readReg64 .x21 = ptsCap ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 (bs2 :: tl2).length ∧ sm.readReg64 .x23 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2⟩
        have hrec := ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

private theorem drop_opt_proto_poly_encoder_cli_placed_body2 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_435).rebase (blkPl_435).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp a polysPtr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (blkPl_435).base + 140#64 →
      s.status = .Running → Saved64Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = polysPtr →
      s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_435).rebase (blkPl_435).base H) ((blkPl_435).base + 128#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = polysPtr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc
  intro cur cnt bs s Frame hpc hrun hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap
  apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP ((blkPC_435).rebase (blkPl_435).base H) ((blkPl_435).base + 128#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = polysPtr ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const
    (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep

private theorem drop_opt_proto_poly_encoder_cli_placed_loop2 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_435).rebase (blkPl_435).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp a polysPtr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_435).base + 140#64 →
      s.status = .Running → Saved64Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = polysPtr →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_435).rebase (blkPl_435).base H) ((blkPl_435).base + 164#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = polysPtr) := by
  have hbody := drop_opt_proto_poly_encoder_cli_placed_body2 hdealloc s0 fsp a polysPtr hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := (blkPl_435).base + 128#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = polysPtr ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx19 hx20 hx21 hx22) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx19_1, hx20_1, hx21_1, hx22_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      rcases hpres1 with ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx21_1
      refine seq_clean (mid := (blkPl_435).base + 140#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => Saved64Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = polysPtr ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧ sm.readReg64 .x22 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx19_2, hx20_2, hx21_2, hx22_2⟩
        have hrec := ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx19_2 hx20_2 hx21_2 hx22_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

/-- Relocatable `core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#2]`
    (Block `435`) satisfies `dropOptProtoPolyEncoderSpec A` under `[LibsignalPlacement]`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_glue_opt_proto_poly_encoder_placed_ok
    [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc_raw : subroutine_ok ((blkPC_435).rebase (blkPl_435).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_435).rebase (blkPl_435).base H)
      (blkPl_435).base (dropOptProtoPolyEncoderSpec A) := by
  simp only [dropOptProtoPolyEncoderSpec]
  have hloop1 := drop_opt_proto_poly_encoder_cli_placed_loop1 hdealloc_raw
  have hloop2 := drop_opt_proto_poly_encoder_cli_placed_loop2 hdealloc_raw
  dsimp only [protoPolynomialEncoderSize, optProtoPolynomialEncoderNoneTailSize, BitVec.ofNat_eq_ofNat] at hloop1 hloop2 hdealloc_raw ⊢
  wp_init x s0; rcases x with ⟨a, optPb⟩
  dsimp only [DropOptProtoPolyEncoderGhost.a, DropOptProtoPolyEncoderGhost.optPb] at *
  nth_rw 1 [stackAt_dropStack64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x23 v_w3 v_x22 v_x21 v_x20 v_x19
  have hfsp_align : ((s0.sp - 64#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 64#64 (by assumption) (by decide)
  cases optPb with
  | none =>
    rw [optProtoPolynomialEncoderAt_none]; dsimp only [optProtoPolynomialEncoderNoneTailSize]; wp_steps
    refine SepWP.focus_weaken (optProtoPolyEncoder_none_entails_memRegion_56 a) (by sep_focus) ?_
    refine SepWP.focus_weaken
      (stack_restore_64_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x23) v_w3 (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19))
      (by sep_focus) ?_
    wp_done
  | some pb =>
    rw [optProtoPolynomialEncoderAt_some]
    refine SepWP.weaken_pre (sepConj_mono_left (protoPolyEncoderAt_entails_dealloc A a pb)) ?_
    wp_pull_exists; rename_i g; wp_focus_pure
    rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne, hpolys_le, hpolys_cap_lt, hpolys_ptr_ne⟩
    have hpts_cap_pow : g.pts.cap.toNat < 2 ^ 63 := by omega
    have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
    refine seq_clean (mid := (blkPl_435).base + 88#64)
      (P_mid := (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        (if g.pts.cap = 0 then emp
         else A.live g.pts.ptr (g.pts.cap.toNat * 24) 8 ∗ memRegion g.pts.ptr (g.pts.cap.toNat * 24)) ∗
        ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        (if g.polys.cap = 0 then emp
         else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 g.polys.ptr pb.polys ∗
           memRegion (g.polys.ptr + BitVec.ofNat 64 (pb.polys.length * 24))
             ((g.polys.cap.toNat - pb.polys.length) * 24)) ∗
        memRegion (a + 48#64) 8 ∗ A.pool ∗ stackAt (s0.sp - 64#64) allocHookStack ∗
        (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ v_w3) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved64Preserved s0 sm (s0.sp - 64#64) ∧
        sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.pts.ptr ∧ sm.readReg64 .x21 = g.pts.cap)
      ?_ ?_
    · generalize hxs : pb.pts = xs at hpts_le ⊢
      cases xs with
      | nil =>
        simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
          BitVec.add_zero, arrayAt, emp_sepConj]
        wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
      | cons bs tl =>
        have hlen_pos : 0 < (bs :: tl).length := by simp
        have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
          have : (bs :: tl).length * 24 ≤ g.pts.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
          omega
        have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
        have hcap_ne : g.pts.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
        simp only [hcap_ne, ↓reduceIte]
        refine seq_clean (mid := (blkPl_435).base + 64#64)
          (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.pts.ptr (bs :: tl) ∗
            A.pool ∗ stackAt (s0.sp - 64#64) allocHookStack ∗
            ((a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
             ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
             A.live g.pts.ptr (g.pts.cap.toNat * 24) 8 ∗
             memRegion (g.pts.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24))
               ((g.pts.cap.toNat - (bs :: tl).length) * 24) ∗
             ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
             ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
             (if g.polys.cap = 0 then emp
              else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
                arrayAt (fun bs addr => vecU8 A addr bs) 24 g.polys.ptr pb.polys ∗
                memRegion (g.polys.ptr + BitVec.ofNat 64 (pb.polys.length * 24))
                  ((g.polys.cap.toNat - pb.polys.length) * 24)) ∗
             memRegion (a + 48#64) 8 ∗
             (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ v_w3) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
          (Q := fun sm => Saved64Preserved s0 sm (s0.sp - 64#64) ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.pts.ptr ∧ sm.readReg64 .x21 = g.pts.cap ∧
            sm.readReg64 .x22 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x23 = g.pts.ptr + 8#64)
          ?_ ?_
        · wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
        · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop, hx23_loop⟩
          refine SepWP.strengthen_entails_const ?_
            (hloop1 s0 (s0.sp - 64#64) a g.pts.ptr g.pts.cap hfsp_align (bs :: tl) g.pts.ptr s_loop _
              (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
              hx19_loop hx20_loop hx21_loop hx22_loop hx23_loop)
          have hsplit : g.pts.cap.toNat * 24 =
              (bs :: tl).length * 24 + (g.pts.cap.toNat - (bs :: tl).length) * 24 := by
            rw [← Nat.add_mul]; congr 1; omega
          have hbound : (bs :: tl).length * 24 + (g.pts.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
            rw [← hsplit]; omega
          conv_rhs =>
            arg 2; arg 2; arg 2; arg 1; arg 2
            rw [hsplit, ProofLib.memRegion_split g.pts.ptr ((bs :: tl).length * 24)
                  ((g.pts.cap.toNat - (bs :: tl).length) * 24) hbound]
          exact Entails.of_eq (by ac_rfl)
    · intro s1 hpc1 hrun1 ⟨⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1⟩
      refine seq_clean (mid := (blkPl_435).base + 112#64)
        (P_mid := (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
          (if g.polys.cap = 0 then emp
           else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
             arrayAt (fun bs addr => vecU8 A addr bs) 24 g.polys.ptr pb.polys ∗
             memRegion (g.polys.ptr + BitVec.ofNat 64 (pb.polys.length * 24))
               ((g.polys.cap.toNat - pb.polys.length) * 24)) ∗
          memRegion (a + 48#64) 8 ∗ A.pool ∗ stackAt (s0.sp - 64#64) allocHookStack ∗
          (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ v_w3) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved64Preserved s0 sm (s0.sp - 64#64) ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · by_cases hc : g.pts.cap = 0
        · have hc_beq : (g.pts.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
          simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx21_1 ⊢; wp_steps; wp_done
        · have hc_beq : ¬((g.pts.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
          have hlsl := cap_mul_24 hpts_cap_lt
          simp only [hc, ↓reduceIte]; wp_steps
          wp_call hdealloc_raw (g.pts.ptr, g.pts.cap.toNat * 24, 8)
          refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
      · intro s2 hpc2 hrun2 ⟨⟨hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
        refine seq_clean (mid := (blkPl_435).base + 164#64)
          (P_mid := (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
            ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
            ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
            ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
            (if g.polys.cap = 0 then emp
             else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗ memRegion g.polys.ptr (g.polys.cap.toNat * 24)) ∗
            memRegion (a + 48#64) 8 ∗ A.pool ∗ stackAt (s0.sp - 64#64) allocHookStack ∗
            (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ v_w3) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved64Preserved s0 sm (s0.sp - 64#64) ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.polys.ptr)
          ?_ ?_
        · generalize hys : pb.polys = ys at hpolys_le ⊢
          cases ys with
          | nil =>
            simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
              BitVec.add_zero, arrayAt, emp_sepConj]
            wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
          | cons bs tl =>
            have hlen_pos : 0 < (bs :: tl).length := by simp
            have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
              have : (bs :: tl).length * 24 ≤ g.polys.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpolys_le
              omega
            have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
            have hcap_ne : g.polys.cap ≠ 0 := by intro hc0; rw [hc0] at hpolys_le; simp at hpolys_le
            simp only [hcap_ne, ↓reduceIte]
            refine seq_clean (mid := (blkPl_435).base + 140#64)
              (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.polys.ptr (bs :: tl) ∗
                A.pool ∗ stackAt (s0.sp - 64#64) allocHookStack ∗
                ((a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
                 ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
                 ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
                 ((a + 40#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
                 A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
                 memRegion (g.polys.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24))
                   ((g.polys.cap.toNat - (bs :: tl).length) * 24) ∗
                 memRegion (a + 48#64) 8 ∗
                 (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ v_w3) ∗
                  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
              (Q := fun sm => Saved64Preserved s0 sm (s0.sp - 64#64) ∧
                sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.polys.ptr ∧
                sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.polys.ptr + 8#64)
              ?_ ?_
            · wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
            · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
              refine SepWP.strengthen_entails_const ?_
                (hloop2 s0 (s0.sp - 64#64) a g.polys.ptr hfsp_align (bs :: tl) g.polys.ptr s_loop _
                  (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
                  hx19_loop hx20_loop hx21_loop hx22_loop)
              have hsplit : g.polys.cap.toNat * 24 =
                  (bs :: tl).length * 24 + (g.polys.cap.toNat - (bs :: tl).length) * 24 := by
                rw [← Nat.add_mul]; congr 1; omega
              have hbound : (bs :: tl).length * 24 + (g.polys.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
                rw [← hsplit]; omega
              conv_rhs =>
                arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; arg 1; arg 2
                rw [hsplit, ProofLib.memRegion_split g.polys.ptr ((bs :: tl).length * 24)
                      ((g.polys.cap.toNat - (bs :: tl).length) * 24) hbound]
              exact Entails.of_eq (by ac_rfl)
        · intro s3 hpc3 hrun3 ⟨⟨hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3⟩
          by_cases hc : g.polys.cap = 0
          · have hc_beq : (g.polys.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
            simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp]; wp_steps
            refine SepWP.focus_weaken
              (protoPolyEncoderHeaders_entails_memRegion_56 a g.pts.cap g.pts.ptr
                (BitVec.ofNat 64 pb.pts.length) 0#64 g.polys.ptr (BitVec.ofNat 64 pb.polys.length))
              (by sep_focus) ?_
            refine SepWP.focus_weaken
              (stack_restore_64_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                (s0.readReg64 .x23) v_w3 (s0.readReg64 .x22) (s0.readReg64 .x21)
                (s0.readReg64 .x20) (s0.readReg64 .x19))
              (by sep_focus) ?_
            wp_done
          · have hc_beq : ¬((g.polys.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
            have hlsl := cap_mul_24 hpolys_cap_lt
            simp only [hc, ↓reduceIte]; wp_steps
            refine SepWP.focus_weaken
              (protoPolyEncoderHeaders_entails_memRegion_56 a g.pts.cap g.pts.ptr
                (BitVec.ofNat 64 pb.pts.length) g.polys.cap g.polys.ptr (BitVec.ofNat 64 pb.polys.length))
              (by sep_focus) ?_
            refine SepWP.focus_weaken
              (stack_restore_64_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                (s0.readReg64 .x23) v_w3 (s0.readReg64 .x22) (s0.readReg64 .x21)
                (s0.readReg64 .x20) (s0.readReg64 .x19))
              (by sep_focus) ?_
            rw [stackAt_dropStack64_split_bottom s0.sp]
            wp_call hdealloc_raw (g.polys.ptr, g.polys.cap.toNat * 24, 8)
            rw [← stackAt_dropStack64_split_bottom s0.sp]
            wp_done

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_opt_proto_poly_encoder_placed_ok
    [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (lsProg_435 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok (lsProg_435 H) (blkPl_435).base (dropOptProtoPolyEncoderSpec A) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_glue_opt_proto_poly_encoder_placed_ok hdealloc

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_opt_proto_poly_encoder_placed
    [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    subroutine_ok (lsProg_435 H) (blkPl_435).base (dropOptProtoPolyEncoderSpec A) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_glue_opt_proto_poly_encoder_placed_ok
    (SpqrV1.Alloc.spqr_hook_ok_of_mem hdealloc)

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_glue_opt_proto_poly_encoder_placed
    [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    subroutine_ok (lsProg_435 H) (blkPl_435).base (dropOptProtoPolyEncoderSpec A) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_opt_proto_poly_encoder_placed hdealloc

private theorem hookSat_dealloc_withPanics {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A) := by
  rcases hdealloc with ⟨f, hf, hok⟩
  exact ⟨f, by simp [Rust.withPanics, Rust.isPanicSymbol, hf], hok⟩

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_opt_proto_poly_encoder_placed_x
    [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    subroutine_ok (lsProg_435 (Rust.withPanics ext)) (blkPl_435).base (dropOptProtoPolyEncoderSpec A) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_opt_proto_poly_encoder_placed
    (hookSat_dealloc_withPanics hdealloc)

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_glue_opt_proto_poly_encoder_placed_x
    [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    subroutine_ok (lsProg_435 (Rust.withPanics ext)) (blkPl_435).base (dropOptProtoPolyEncoderSpec A) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_opt_proto_poly_encoder_placed_x hdealloc

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_opt_proto_poly_encoder_placed_lscl
    [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 435) (withLsCodeLoaded lsmpl (dropOptProtoPolyEncoderSpec A)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (CryptoVerification.Cli.SpqrV1.Drop.drop_opt_proto_poly_encoder_placed hdealloc)) hi

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_opt_proto_poly_encoder_placed_cl
    [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 435) (withLsCl lsmpl (dropOptProtoPolyEncoderSpec A)) :=
  ls_subroutine_ok_cl_of_plain (callerProg := callerProg)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_opt_proto_poly_encoder_placed hdealloc) hi

end CryptoVerification.SpqrV1.Drop
