/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.Unchunked
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.DecodesPlaced
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Relocatable Unchunked `Ct1Sent` Drop Glue (Blocks `444` and `436`)

Proves `drop_unchunked_ct1_sent_local1_placed_ok` (Block `444`) and
`drop_opt_proto_unchunked_ct1_sent_placed_ok` (Block `436`) along with `HookSat` and `withPanics`
wrappers under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.SpqrV1.Drop.Placed

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Block `444`: `drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#3]` -/

/-- Relocatable `core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#3]`
    (Block `444`) satisfies `dropUnchunkedCt1SentSpec A F` under `[LibsignalPlacement]`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_unchunked_ct1_sent_local1_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_444).rebase (blkPl_444).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_444).rebase (blkPl_444).base H)
      (blkPl_444).base
      (dropUnchunkedCt1SentSpec A F) := by
  simp only [dropUnchunkedCt1SentSpec]
  have hdealloc_raw := hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [unchunkedCt1SentSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw ⊢
  wp_init x s0
  rcases x with ⟨a, st⟩
  have hx0 : s0.readReg64 .x0 = a := h
  dsimp only [DropUnchunkedCt1SentGhost.a, DropUnchunkedCt1SentGhost.st] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre (sepConj_mono_left (unchunkedCt1SentAt_entails_dealloc A a st)) ?_
  rw [sepExists_sepConj_left]
  apply SepWP.exists_left; intro g
  refine seq_clean (mid := (blkPl_444).base + 36#64)
    (P_mid := (fiveVec128HeadersAt a g ∗
      vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
      vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
      vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
      vecCapPtrDealloc A g.v5.cap g.v5.ptr) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine align_pre (by ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := (blkPl_444).base + 56#64)
      (P_mid := (fiveVec128HeadersAt a g ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
        vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
        vecCapPtrDealloc A g.v5.cap g.v5.ptr) ∗
        A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine seq_clean (mid := (blkPl_444).base + 76#64)
        (P_mid := (fiveVec128HeadersAt a g ∗
          vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
          vecCapPtrDealloc A g.v5.cap g.v5.ptr) ∗
          A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine seq_clean (mid := (blkPl_444).base + 96#64)
          (P_mid := (fiveVec128HeadersAt a g ∗
            vecCapPtrDealloc A g.v5.cap g.v5.ptr) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
          (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
          ?_ ?_
        · dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc]
          by_cases hc4 : (g.v4.cap == 0#64) = true <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine align_pre (by rw [hsp_3]; ac_rfl) ?_; wp_done
        · intro s4 hpc4 hrun4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
          dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc]
          by_cases hc5 : (g.v5.cap == 0#64) = true <;>
            simp only [hc5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            refine SepWP.weaken_pre (sepConj_mono
              (fiveVec128HeadersAt_entails_memRegion_128 a g)
              (sepConj_mono_right (stack_restore_32_allocHook s0.sp _ _ _ _))) ?_
            wp_done
          · wp_steps
            refine SepWP.weaken_pre (sepConj_mono
              (sepConj_mono_left (fiveVec128HeadersAt_entails_memRegion_128 a g))
              (sepConj_mono_right (cells4_entails_stack32_bottom s0.sp _ _ _ _))) ?_
            wp_apply
            refine SepWP.weaken_pre (tail_dealloc_unchunked_post a 128 A.pool s0.sp) ?_
            wp_done

/-! ## 2. Block `436`: `drop_glue::<Option<proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#2]` -/

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
        vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ Rest) by ac_rfl))
    (Entails.refl _)

/-- Relocatable `core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#2]`
    (Block `436`) satisfies `dropOptProtoUnchunkedCt1SentSpec A` under `[LibsignalPlacement]`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_opt_proto_unchunked_ct1_sent_placed_ok
    [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_436).rebase (blkPl_436).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_436).rebase (blkPl_436).base H)
      (blkPl_436).base
      (dropOptProtoUnchunkedCt1SentSpec A) := by
  simp only [dropOptProtoUnchunkedCt1SentSpec]
  have hdealloc_raw := hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [protoUnchunkedCt1SentSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw ⊢
  wp_init x s0
  rcases x with ⟨a, optSt⟩
  have hx0 : s0.readReg64 .x0 = a := h
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
    wp_steps
    refine SepWP.weaken_pre (sepConj_mono
      (optProtoUnchunkedCt1SentAt_none_entails_memRegion_128 A a)
      (sepConj_mono_right (stack_restore_32_allocHook s0.sp _ _ _ _))) ?_
    wp_done
  | some st =>
    rw [optProtoUnchunkedCt1SentAt_some]
    refine SepWP.weaken_pre
      (sepConj_mono_left (protoUnchunkedCt1SentAt_entails_dealloc A a st)) ?_
    rw [sepExists_sepConj_left]
    apply SepWP.exists_left; intro g
    wp_focus_pure; intro hcap1_lt
    have hne_none1 := cap_add_one_beq_zero_false hcap1_lt
    refine seq_clean (mid := (blkPl_436).base + 76#64)
      (P_mid := (protoUnchunked3VecHeadersAt a g ∗
        memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
        A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧
        sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
      ?_ ?_
    · cases hauth : st.auth with
      | none =>
        rw [optProtoAuthenticatorAt_72_none]
        have hstep : SepWP ((blkPC_436).rebase (blkPl_436).base H) ((blkPl_436).base + 76#64) s0
            ((protoUnchunked3VecHeadersAt a g ∗
              (((a + 72#64) ↦₆₄ noneCap) ∗ memRegion (a + 80#64) 40) ∗
              memRegion (a + 120#64) 8 ∗
              vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
              vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
              A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
              ((s0.sp - 32#64) ↦₆₄ fp_old) ∗ ((s0.sp - 24#64) ↦₆₄ lr_old) ∗
              ((s0.sp - 16#64) ↦₆₄ x20_old) ∗ ((s0.sp - 8#64) ↦₆₄ x19_old))
            (fun sm Pm =>
              (Pm ⊢ (protoUnchunked3VecHeadersAt a g ∗
                (((a + 72#64) ↦₆₄ noneCap) ∗ memRegion (a + 80#64) 40) ∗
                memRegion (a + 120#64) 8 ∗
                vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
                vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
                vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
                A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
              Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap) := by
          dsimp only [protoUnchunked3VecHeadersAt]
          wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x20, Reg.x19]) ?_; wp_done
        exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
          (SepWP.strengthen_entails_const
            (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
              (optProtoAuthenticatorAt_72_none_entails_memRegion_48 A a))))
            hstep)
      | some auth =>
        rw [optProtoAuthenticatorAt_some]
        refine SepWP.weaken_pre
          (protoUnchunked3Vec_auth_some_entails A a g auth _) ?_
        apply SepWP.exists_left; intro ga
        wp_focus_pure; intro hga_lt
        have hne_none := cap_add_one_beq_zero_false hga_lt
        refine seq_clean (mid := (blkPl_436).base + 56#64)
          (P_mid := (protoUnchunked3VecHeadersAt a g ∗
            (auth72HeadersAt a ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
            memRegion (a + 120#64) 8 ∗
            vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
            vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
            vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
          ?_ ?_
        · dsimp only [protoUnchunked3VecHeadersAt, auth72HeadersAt, vecCapPtrDealloc]
          by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
            simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
          · wp_steps; wp_apply; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
        · intro sa1 hpca1 hruna1 ⟨⟨hx21_a1, hx22_a1, hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hx19_a1, hx20_a1⟩
          have hstepa2 : SepWP ((blkPC_436).rebase (blkPl_436).base H) ((blkPl_436).base + 76#64) sa1
              ((protoUnchunked3VecHeadersAt a g ∗
                (auth72HeadersAt a ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
                memRegion (a + 120#64) 8 ∗
                vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
                vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
                vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
                A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
              (fun sm Pm =>
                (Pm ⊢ (protoUnchunked3VecHeadersAt a g ∗
                  auth72HeadersAt a ga ∗
                  memRegion (a + 120#64) 8 ∗
                  vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
                  vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
                  vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
                  A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                  (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
                Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧
                sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap) := by
            dsimp only [auth72HeadersAt, vecCapPtrDealloc]
            by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
              simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; wp_done
            · wp_steps; wp_apply; refine align_pre (by rw [hsp_a1]; ac_rfl) ?_; wp_done
          exact SepWP.strengthen_entails_const
            (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
              (auth72HeadersAt_entails_memRegion_48 a ga))))
            hstepa2
    · intro s1 hpc1 hrun1 ⟨⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1⟩
      refine seq_clean (mid := (blkPl_436).base + 96#64)
        (P_mid := (protoUnchunked3VecHeadersAt a g ∗
          memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
          vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
          A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc]
        by_cases hc1 : (g.v1.cap == 0#64) = true <;>
          simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
      · intro s2 hpc2 hrun2 ⟨⟨hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
        refine seq_clean (mid := (blkPl_436).base + 116#64)
          (P_mid := (protoUnchunked3VecHeadersAt a g ∗
            memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
            vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
          ?_ ?_
        · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc]
          by_cases hc2 : (g.v2.cap == 0#64) = true <;>
            simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
        · intro s3 hpc3 hrun3 ⟨⟨hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
          dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc]
          by_cases hc3 : (g.v3.cap == 0#64) = true <;>
            simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            refine SepWP.weaken_pre (sepConj_mono
              (protoUnchunked3VecHeadersAt_entails_memRegion_128 a g)
              (sepConj_mono_right (stack_restore_32_allocHook s0.sp _ _ _ _))) ?_
            wp_done
          · wp_steps
            refine SepWP.weaken_pre (sepConj_mono
              (Entails.trans
                (Entails.of_eq (show _ =
                  (protoUnchunked3VecHeadersAt a g ∗ memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8) ∗
                  (A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) by
                    unfold protoUnchunked3VecHeadersAt; ac_rfl))
                (sepConj_mono_left (protoUnchunked3VecHeadersAt_entails_memRegion_128 a g)))
              (sepConj_mono_right (cells4_entails_stack32_bottom s0.sp _ _ _ _))) ?_
            wp_apply
            refine SepWP.weaken_pre (tail_dealloc_unchunked_post a 128 A.pool s0.sp) ?_
            wp_done

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_unchunked_ct1_sent_local1_placed
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    subroutine_ok (lsProg_444 H) (blkPl_444).base (dropUnchunkedCt1SentSpec A F) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_unchunked_ct1_sent_local1_placed_ok
    (SpqrV1.Alloc.spqr_hook_ok_of_mem hdealloc)

private theorem hookSat_dealloc_withPanics {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A) := by
  rcases hdealloc with ⟨f, hf, hok⟩
  exact ⟨f, by simp [Rust.withPanics, Rust.isPanicSymbol, hf], hok⟩

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_unchunked_ct1_sent_local1_placed_x
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    subroutine_ok (lsProg_444 (Rust.withPanics ext)) (blkPl_444).base (dropUnchunkedCt1SentSpec A F) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_unchunked_ct1_sent_local1_placed
    (hookSat_dealloc_withPanics hdealloc)

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_unchunked_ct1_sent_local1_placed_lscl
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 444) (withLsCodeLoaded lsmpl (dropUnchunkedCt1SentSpec A F)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (CryptoVerification.Cli.SpqrV1.Drop.drop_unchunked_ct1_sent_local1_placed hdealloc)) hi

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_unchunked_ct1_sent_local1_placed_cl
    [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 444) (withLsCl lsmpl (dropUnchunkedCt1SentSpec A F)) :=
  ls_subroutine_ok_cl_of_plain (callerProg := callerProg)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_unchunked_ct1_sent_local1_placed hdealloc) hi

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_opt_proto_unchunked_ct1_sent_placed
    [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    subroutine_ok (lsProg_436 H) (blkPl_436).base (dropOptProtoUnchunkedCt1SentSpec A) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_opt_proto_unchunked_ct1_sent_placed_ok
    (SpqrV1.Alloc.spqr_hook_ok_of_mem hdealloc)

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_opt_proto_unchunked_ct1_sent_placed_x
    [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    subroutine_ok (lsProg_436 (Rust.withPanics ext)) (blkPl_436).base (dropOptProtoUnchunkedCt1SentSpec A) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_opt_proto_unchunked_ct1_sent_placed
    (hookSat_dealloc_withPanics hdealloc)

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_opt_proto_unchunked_ct1_sent_placed_lscl
    [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 436) (withLsCodeLoaded lsmpl (dropOptProtoUnchunkedCt1SentSpec A)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (CryptoVerification.Cli.SpqrV1.Drop.drop_opt_proto_unchunked_ct1_sent_placed hdealloc)) hi

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_opt_proto_unchunked_ct1_sent_placed_cl
    [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 436) (withLsCl lsmpl (dropOptProtoUnchunkedCt1SentSpec A)) :=
  ls_subroutine_ok_cl_of_plain (callerProg := callerProg)
    (CryptoVerification.Cli.SpqrV1.Drop.drop_opt_proto_unchunked_ct1_sent_placed hdealloc) hi

end CryptoVerification.SpqrV1.Drop
