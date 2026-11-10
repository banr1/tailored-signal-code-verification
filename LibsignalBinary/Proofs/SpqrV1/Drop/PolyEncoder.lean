/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.Poly
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Drop Glue for `spqr::encoding::polynomial::PolyEncoder`

**Checked by Lean.**

Proves fixed-image and relocatable `[LibsignalPlacement]` contracts for:
- `core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]` (Block `138`, 105 instructions)
- `core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]` (Block `272`, 2 instructions)
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.L12

open Lean Elab Tactic ProofLib CryptoVerification.SpqrV1.Drop in
elab "drop_poly_encoder_local1_fetches " b:term:max H:term:max : tactic => do
  let eOff ← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff
    "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]"
  let hfn := mkCIdent eOff.decl
  let offLit := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic|
    code_fetches CryptoVerification.libsignalSessionCode spqrDropChainEpochBin $b $H $hfn $offLit 420))

open Lean Elab Tactic ProofLib CryptoVerification.SpqrV1.Drop in
elab "drop_poly_encoder_local2_fetches " b:term:max H:term:max : tactic => do
  let eOff ← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff
    "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]"
  let hfn := mkCIdent eOff.decl
  let offLit := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic|
    code_fetches CryptoVerification.libsignalSessionCode spqrDropChainEpochBin $b $H $hfn $offLit 8))

end CryptoVerification.SpqrV1.Layout.L12

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L12

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option hygiene false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Specifications -/

/-- Ghost arguments of `drop_glue::<PolyEncoder>`. -/
structure DropGluePolyEncoderGhost where
  /-- Pointer to the 400-byte `PolyEncoder` (`x0`). -/
  encA : BitVec 64
  /-- Logical `PolyEncoder` value at `encA`. -/
  enc : PolyEncoder

/-- Specification of `core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder>`
    (`[local#1]` and `[local#2]`):
    consumes `polyEncoderAt A x.encA x.enc` (400 bytes) and leaves `memRegion x.encA 400`. -/
def dropGluePolyEncoderSpec (A : RustAlloc) : Spec DropGluePolyEncoderGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.encA⌝ ∗
      polyEncoderAt A x.encA x.enc ∗
      A.pool ∗ stackAt s.sp dropGluePoly16Stack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.encA polyEncoderSize ∗
      A.pool ∗ stackAt s0.sp dropGluePoly16Stack

/-! ## Entailment Helpers for `PolyEncoder` (`400` Bytes) -/

theorem polyEncoderTail_entails_memRegion_8 (encA : BitVec 64) (idx : BitVec 32) :
    ((encA + polyEncoderIdxOff) ↦₃₂ idx) ∗
      memRegion (encA + polyEncoderPadOff) polyEncoderPadSize ⊢
    memRegion (encA + 392#64) 8 := by
  unfold polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  have hpad : encA + 0x18c#64 = (encA + 0x188#64) + 4#64 := by bv_omega
  rw [show (392#64 : BitVec 64) = 0x188#64 from rfl,
      ProofLib.memRegion_split' (b := encA + 0x188#64) (n := 4) (k := 4)
        (b' := encA + 0x18c#64) rfl hpad (by decide)]
  exact sepConj_mono_left (pointsTo32_entails_memRegion _ _)

theorem polyEncoderAt_entails_tag_vecs_tail (A : RustAlloc) (encA : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A encA enc ⊢
      ∃∗ tag : BitVec 64, ∃∗ vecs : List (List GF16),
        ⌜vecs.length = NUM_POLYS⌝ ∗
        (encA ↦₆₄ tag) ∗
        vecGF16ListOf A (encA + 8#64) vecs ∗
        memRegion (encA + 392#64) 8 := by
  unfold polyEncoderAt encoderStateAt polyEncoderVecsOff
  cases hs : enc.s with
  | points pts =>
    dsimp only
    rw [pointListOf_eq_vecGF16ListOf]
    refine Entails.sepExists_right polyEncoderPointsTag ?_
    refine Entails.sepExists_right (pts.map Point.value) ?_
    rw [sepConj_assoc (⌜pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)⌝),
        sepConj_assoc (encA ↦₆₄ polyEncoderPointsTag)]
    refine Entails.pure_left fun ⟨hlen, _⟩ => ?_
    have hlen' : (pts.map Point.value).length = NUM_POLYS := by simp [hlen]
    refine Entails.pure_right hlen' ?_
    exact sepConj_mono_right (sepConj_mono_right (polyEncoderTail_entails_memRegion_8 encA enc.idx))
  | polys ps =>
    dsimp only
    rw [polyListOf_eq_vecGF16ListOf]
    refine Entails.sepExists_right polyEncoderPolysTag ?_
    refine Entails.sepExists_right (ps.map LibsignalSpqrV1.Poly.coefficients) ?_
    rw [sepConj_assoc (⌜ps.length = NUM_POLYS⌝),
        sepConj_assoc (encA ↦₆₄ polyEncoderPolysTag)]
    refine Entails.pure_left fun hlen => ?_
    have hlen' : (ps.map LibsignalSpqrV1.Poly.coefficients).length = NUM_POLYS := by simp [hlen]
    refine Entails.pure_right hlen' ?_
    exact sepConj_mono_right (sepConj_mono_right (polyEncoderTail_entails_memRegion_8 encA enc.idx))

theorem slot0_tag_entails_memRegion_32 (encA tag cap ptr : BitVec 64) (Rest : SepProp) :
    ((encA ↦₆₄ tag) ∗ ((encA + 8#64) ↦₆₄ cap) ∗ ((encA + 16#64) ↦₆₄ ptr) ∗
      memRegion (encA + 24#64) 8) ∗ Rest ⊢
    memRegion encA 32 ∗ Rest := by
  have h8 : (encA ↦₆₄ tag) ⊢ memRegion encA 8 := pointsTo64_entails_memRegion encA tag
  have h24 := DropGlueFacts.header_cells_entails_memRegion_24 (encA + 8#64) cap ptr
  have ha1 : (encA + 8#64) + 8#64 = encA + 16#64 := by bv_omega
  have ha2 : (encA + 8#64) + 16#64 = encA + 24#64 := by bv_omega
  rw [ha1, ha2] at h24
  have hsplit : memRegion encA 32 = memRegion encA 8 ∗ memRegion (encA + 8#64) 24 :=
    ProofLib.memRegion_split encA 8 24 (by decide)
  rw [hsplit]
  refine Entails.trans
    (Entails.of_eq (show _ = ((encA ↦₆₄ tag) ∗ (((encA + 8#64) ↦₆₄ cap) ∗ ((encA + 16#64) ↦₆₄ ptr) ∗ memRegion (encA + 24#64) 8)) ∗ Rest by ac_rfl))
    (sepConj_mono_left (sepConj_mono h8 h24))

theorem SepWP.dealloc_enc_cons0_step {A : RustAlloc} {prog : Program} {target_pc : BitVec 64} {s : State}
    (encA tag : BitVec 64) (cs : List GF16) (rest : List (List GF16)) (Tail : SepProp) {Q : State → Prop}
    (h : ∀ cap ptr : BitVec 64,
      SepWP prog target_pc s
        ((((encA + 8#64) ↦₆₄ cap) ∗ ((encA + 16#64) ↦₆₄ ptr) ∗ memRegion (encA + 24#64) 8 ∗
          vecGF16Dealloc A cap ptr) ∗
          ((encA ↦₆₄ tag) ∗ (vecGF16ListOf A (encA + 32#64) rest ∗ Tail)))
        (fun sm Pm =>
          (Pm ⊢ ((encA ↦₆₄ tag) ∗ ((encA + 8#64) ↦₆₄ cap) ∗ ((encA + 16#64) ↦₆₄ ptr) ∗
            memRegion (encA + 24#64) 8) ∗
            (vecGF16ListOf A (encA + 32#64) rest ∗ Tail)) ∧
          Q sm)) :
    SepWP prog target_pc s
      (vecGF16ListOf A (encA + 8#64) (cs :: rest) ∗ ((encA ↦₆₄ tag) ∗ Tail))
      (fun sm Pm =>
        (Pm ⊢ vecGF16ListOf A (encA + 32#64) rest ∗ (memRegion encA 32 ∗ Tail)) ∧
        Q sm) := by
  have hnext : (encA + 8#64) + 24#64 = encA + 32#64 := by bv_omega
  have hpre : vecGF16ListOf A (encA + 8#64) (cs :: rest) ∗ ((encA ↦₆₄ tag) ∗ Tail) =
      vecGF16Of A (encA + 8#64) cs ∗ ((encA ↦₆₄ tag) ∗ (vecGF16ListOf A (encA + 32#64) rest ∗ Tail)) := by
    show (vecGF16Of A (encA + 8#64) cs ∗ vecGF16ListOf A ((encA + 8#64) + 24#64) rest) ∗ ((encA ↦₆₄ tag) ∗ Tail) = _
    rw [hnext]
    ac_rfl
  rw [hpre]
  refine SepWP.weaken_pre (vecGF16Of_step_entails A encA 8#64 16#64 24#64 (by bv_omega) (by bv_omega) cs _) ?_
  apply SepWP.exists_left; intro cap
  apply SepWP.exists_left; intro ptr
  have hpost :
      ((encA ↦₆₄ tag) ∗ ((encA + 8#64) ↦₆₄ cap) ∗ ((encA + 16#64) ↦₆₄ ptr) ∗
        memRegion (encA + 24#64) 8) ∗
        (vecGF16ListOf A (encA + 32#64) rest ∗ Tail) ⊢
      vecGF16ListOf A (encA + 32#64) rest ∗ (memRegion encA 32 ∗ Tail) := by
    refine Entails.trans (slot0_tag_entails_memRegion_32 encA tag cap ptr _) ?_
    exact Entails.of_eq (by ac_rfl)
  exact SepWP.strengthen_entails_const hpost (h cap ptr)

theorem tail_dealloc_polyenc_pre_weaken (encA cap ptr : BitVec 64)
    (live prev tail8 pool : SepProp) (sp fp lr x19 w3 : BitVec 64) :
    ((encA + 368#64) ↦₆₄ cap) ∗ ((encA + 376#64) ↦₆₄ ptr) ∗
      memRegion (encA + 384#64) 8 ∗
      live ∗ prev ∗ tail8 ∗ pool ∗
      stackAt (sp - 32#64) allocHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ w3) ⊢
    memRegion (encA + 368#64) 24 ∗ prev ∗ tail8 ∗ pool ∗
      memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack ∗ live := by
  have h1 := DropGlueFacts.header_cells_entails_memRegion_24 (encA + 368#64) cap ptr
  have ha1 : (encA + 368#64) + 8#64 = encA + 376#64 := by bv_omega
  have ha2 : (encA + 368#64) + 16#64 = encA + 384#64 := by bv_omega
  rw [ha1, ha2] at h1
  have h2 := cells4_entails_stack_bottom sp fp lr x19 w3
  have hreord :
      ((encA + 368#64) ↦₆₄ cap) ∗ ((encA + 376#64) ↦₆₄ ptr) ∗
        memRegion (encA + 384#64) 8 ∗
        live ∗ prev ∗ tail8 ∗ pool ∗
        stackAt (sp - 32#64) allocHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ w3) =
      (((encA + 368#64) ↦₆₄ cap) ∗ ((encA + 376#64) ↦₆₄ ptr) ∗
        memRegion (encA + 384#64) 8) ∗
        (live ∗ prev ∗ tail8 ∗ pool ∗
          (stackAt (sp - 32#64) allocHookStack ∗
            ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
            ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ w3))) := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h2))))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem tail_dealloc_polyenc_post (encA : BitVec 64) (Pool : SepProp) (sp : BitVec 64) :
    Pool ∗ stackAt sp allocHookStack ∗ memRegion (encA + 368#64) 24 ∗
      memRegion encA 368 ∗ memRegion (encA + 392#64) 8 ∗ memRegion (sp - 4128#64) 32 ⊢
    memRegion encA polyEncoderSize ∗ Pool ∗ stackAt sp dropGluePoly16Stack := by
  have h400 : memRegion encA polyEncoderSize =
      (memRegion encA 368 ∗ memRegion (encA + 368#64) 24) ∗ memRegion (encA + 392#64) 8 := by
    rw [show polyEncoderSize = 392 + 8 from rfl,
        ProofLib.memRegion_split encA 392 8 (by decide),
        show (392 : Nat) = 368 + 24 from rfl,
        ProofLib.memRegion_split encA 368 24 (by decide)]
  rw [h400, stackAt_dropGluePoly16_split sp, ← tail_stack_32_from_bottom sp]
  exact Entails.of_eq (by ac_rfl)

theorem cap0_polyenc_post (encA cap ptr : BitVec 64) (Pool : SepProp)
    (sp fp lr x19 w3 : BitVec 64) :
    ((encA + 368#64) ↦₆₄ cap) ∗ ((encA + 376#64) ↦₆₄ ptr) ∗
      memRegion (encA + 384#64) 8 ∗
      memRegion encA 368 ∗ memRegion (encA + 392#64) 8 ∗ Pool ∗
      stackAt (sp - 32#64) allocHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ w3) ⊢
    memRegion encA polyEncoderSize ∗ Pool ∗ stackAt sp dropGluePoly16Stack := by
  have hjoin := slot_join_memRegion encA 368#64 cap ptr 368 392 rfl rfl (by decide)
    (memRegion (encA + 392#64) 8 ∗ Pool ∗ stackAt (sp - 32#64) allocHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ w3))
  have ha1 : (encA + 368#64) + 8#64 = encA + 376#64 := by bv_omega
  have ha2 : (encA + 368#64) + 16#64 = encA + 384#64 := by bv_omega
  rw [ha1, ha2] at hjoin
  refine Entails.trans hjoin ?_
  have h400 : memRegion encA polyEncoderSize = memRegion encA 392 ∗ memRegion (encA + 392#64) 8 :=
    ProofLib.memRegion_split encA 392 8 (by decide)
  rw [h400, ← sepConj_assoc (memRegion encA 392)]
  apply sepConj_mono_right
  apply sepConj_mono_right
  exact stack_restore_32_allocHook sp fp lr x19 w3

/-! ## `PolyEncoder [local#1]` (105 instructions) -/

local macro "poly_encoder_local1_first8_steps " entry:term : tactic => `(tactic| (
  refine DropGlueFacts.seq_clean (mid := $entry + 40#64) (P_mid :=
    vecGF16ListOf A (encA + 32#64) (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
      (memRegion encA 32 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
    (Q := fun sm => Saved32Preserved s0 sm fsp encA) ?_ ?_
  · refine SepWP.dealloc_enc_cons0_step encA tag c0 _ _ ?_
    intro cap ptr
    dsimp only [vecGF16Dealloc, Saved32Preserved]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp]
    · wp_steps; refine DropGlueFacts.align_pre (by ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hsp_1, htrace_1, hvregs_1⟩
    refine DropGlueFacts.seq_clean (mid := $entry + 64#64) (P_mid :=
      vecGF16ListOf A (encA + 56#64) (c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
        (memRegion encA 56 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
      (Q := fun sm => Saved32Preserved s0 sm fsp encA) ?_ ?_
    · refine SepWP.dealloc_list_cons_step encA 32#64 40#64 48#64 56#64 32 56 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c1 _ _ ?_
      intro cap ptr
      dsimp only [vecGF16Dealloc, Saved32Preserved]
      by_cases hcap : (cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hsp_2, htrace_2, hvregs_2⟩
      refine DropGlueFacts.seq_clean (mid := $entry + 88#64) (P_mid :=
        vecGF16ListOf A (encA + 80#64) (c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
          (memRegion encA 80 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
        (Q := fun sm => Saved32Preserved s0 sm fsp encA) ?_ ?_
      · refine SepWP.dealloc_list_cons_step encA 56#64 64#64 72#64 80#64 56 80 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c2 _ _ ?_
        intro cap ptr
        dsimp only [vecGF16Dealloc, Saved32Preserved]
        by_cases hcap : (cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hsp_3, htrace_3, hvregs_3⟩
        refine DropGlueFacts.seq_clean (mid := $entry + 112#64) (P_mid :=
          vecGF16ListOf A (encA + 104#64) (c4 :: c5 :: c6 :: c7 :: rest) ∗
            (memRegion encA 104 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
          (Q := fun sm => Saved32Preserved s0 sm fsp encA) ?_ ?_
        · refine SepWP.dealloc_list_cons_step encA 80#64 88#64 96#64 104#64 80 104 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c3 _ _ ?_
          intro cap ptr
          dsimp only [vecGF16Dealloc, Saved32Preserved]
          by_cases hcap : (cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_3]; ac_rfl) ?_; wp_done
        · intro s4 hpc4 hrun4 ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, hsp_4, htrace_4, hvregs_4⟩
          refine DropGlueFacts.seq_clean (mid := $entry + 136#64) (P_mid :=
            vecGF16ListOf A (encA + 128#64) (c5 :: c6 :: c7 :: rest) ∗
              (memRegion encA 128 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
            (Q := fun sm => Saved32Preserved s0 sm fsp encA) ?_ ?_
          · refine SepWP.dealloc_list_cons_step encA 104#64 112#64 120#64 128#64 104 128 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c4 _ _ ?_
            intro cap ptr
            dsimp only [vecGF16Dealloc, Saved32Preserved]
            by_cases hcap : (cap == 0#64) = true <;>
              simp only [hcap, ↓reduceIte, sepConj_emp]
            · wp_steps; wp_done
            · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_4]; ac_rfl) ?_; wp_done
          · intro s5 hpc5 hrun5 ⟨hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hx29_5, hsp_5, htrace_5, hvregs_5⟩
            refine DropGlueFacts.seq_clean (mid := $entry + 160#64) (P_mid :=
              vecGF16ListOf A (encA + 152#64) (c6 :: c7 :: rest) ∗
                (memRegion encA 152 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
              (Q := fun sm => Saved32Preserved s0 sm fsp encA) ?_ ?_
            · refine SepWP.dealloc_list_cons_step encA 128#64 136#64 144#64 152#64 128 152 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c5 _ _ ?_
              intro cap ptr
              dsimp only [vecGF16Dealloc, Saved32Preserved]
              by_cases hcap : (cap == 0#64) = true <;>
                simp only [hcap, ↓reduceIte, sepConj_emp]
              · wp_steps; wp_done
              · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_5]; ac_rfl) ?_; wp_done
            · intro s6 hpc6 hrun6 ⟨hx19_6, hx20_6, hx21_6, hx22_6, hx23_6, hx24_6, hx25_6, hx26_6, hx27_6, hx28_6, hx29_6, hsp_6, htrace_6, hvregs_6⟩
              refine DropGlueFacts.seq_clean (mid := $entry + 184#64) (P_mid :=
                vecGF16ListOf A (encA + 176#64) (c7 :: rest) ∗
                  (memRegion encA 176 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
                (Q := fun sm => Saved32Preserved s0 sm fsp encA) ?_ ?_
              · refine SepWP.dealloc_list_cons_step encA 152#64 160#64 168#64 176#64 152 176 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c6 _ _ ?_
                intro cap ptr
                dsimp only [vecGF16Dealloc, Saved32Preserved]
                by_cases hcap : (cap == 0#64) = true <;>
                  simp only [hcap, ↓reduceIte, sepConj_emp]
                · wp_steps; wp_done
                · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_6]; ac_rfl) ?_; wp_done
              · intro s7 hpc7 hrun7 ⟨hx19_7, hx20_7, hx21_7, hx22_7, hx23_7, hx24_7, hx25_7, hx26_7, hx27_7, hx28_7, hx29_7, hsp_7, htrace_7, hvregs_7⟩
                refine SepWP.dealloc_list_cons_step encA 176#64 184#64 192#64 200#64 176 200 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c7 _ _ ?_
                intro cap ptr
                dsimp only [vecGF16Dealloc, Saved32Preserved]
                by_cases hcap : (cap == 0#64) = true <;>
                  simp only [hcap, ↓reduceIte, sepConj_emp]
                · wp_steps; wp_done
                · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_7]; ac_rfl) ?_; wp_done))

local macro "poly_encoder_local1_mid7_steps " entry:term : tactic => `(tactic| (
  rcases hpres with ⟨hx19_8, hx20_8, hx21_8, hx22_8, hx23_8, hx24_8, hx25_8, hx26_8, hx27_8, hx28_8, hx29_8, hsp_8, htrace_8, hvregs_8⟩
  refine DropGlueFacts.seq_clean (mid := $entry + 232#64) (P_mid :=
    vecGF16ListOf A (encA + 224#64) (c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: rest) ∗
      (memRegion encA 224 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
    (Q := fun sm => Saved32Preserved s0 sm fsp encA) ?_ ?_
  · refine SepWP.dealloc_list_cons_step encA 200#64 208#64 216#64 224#64 200 224 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c8 _ _ ?_
    intro cap ptr
    dsimp only [vecGF16Dealloc, Saved32Preserved]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp]
    · wp_steps; wp_done
    · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_8]; ac_rfl) ?_; wp_done
  · intro s9 hpc9 hrun9 ⟨hx19_9, hx20_9, hx21_9, hx22_9, hx23_9, hx24_9, hx25_9, hx26_9, hx27_9, hx28_9, hx29_9, hsp_9, htrace_9, hvregs_9⟩
    refine DropGlueFacts.seq_clean (mid := $entry + 256#64) (P_mid :=
      vecGF16ListOf A (encA + 248#64) (c10 :: c11 :: c12 :: c13 :: c14 :: rest) ∗
        (memRegion encA 248 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
      (Q := fun sm => Saved32Preserved s0 sm fsp encA) ?_ ?_
    · refine SepWP.dealloc_list_cons_step encA 224#64 232#64 240#64 248#64 224 248 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c9 _ _ ?_
      intro cap ptr
      dsimp only [vecGF16Dealloc, Saved32Preserved]
      by_cases hcap : (cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_9]; ac_rfl) ?_; wp_done
    · intro s10 hpc10 hrun10 ⟨hx19_10, hx20_10, hx21_10, hx22_10, hx23_10, hx24_10, hx25_10, hx26_10, hx27_10, hx28_10, hx29_10, hsp_10, htrace_10, hvregs_10⟩
      refine DropGlueFacts.seq_clean (mid := $entry + 280#64) (P_mid :=
        vecGF16ListOf A (encA + 272#64) (c11 :: c12 :: c13 :: c14 :: rest) ∗
          (memRegion encA 272 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
        (Q := fun sm => Saved32Preserved s0 sm fsp encA) ?_ ?_
      · refine SepWP.dealloc_list_cons_step encA 248#64 256#64 264#64 272#64 248 272 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c10 _ _ ?_
        intro cap ptr
        dsimp only [vecGF16Dealloc, Saved32Preserved]
        by_cases hcap : (cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_10]; ac_rfl) ?_; wp_done
      · intro s11 hpc11 hrun11 ⟨hx19_11, hx20_11, hx21_11, hx22_11, hx23_11, hx24_11, hx25_11, hx26_11, hx27_11, hx28_11, hx29_11, hsp_11, htrace_11, hvregs_11⟩
        refine DropGlueFacts.seq_clean (mid := $entry + 304#64) (P_mid :=
          vecGF16ListOf A (encA + 296#64) (c12 :: c13 :: c14 :: rest) ∗
            (memRegion encA 296 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
          (Q := fun sm => Saved32Preserved s0 sm fsp encA) ?_ ?_
        · refine SepWP.dealloc_list_cons_step encA 272#64 280#64 288#64 296#64 272 296 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c11 _ _ ?_
          intro cap ptr
          dsimp only [vecGF16Dealloc, Saved32Preserved]
          by_cases hcap : (cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_11]; ac_rfl) ?_; wp_done
        · intro s12 hpc12 hrun12 ⟨hx19_12, hx20_12, hx21_12, hx22_12, hx23_12, hx24_12, hx25_12, hx26_12, hx27_12, hx28_12, hx29_12, hsp_12, htrace_12, hvregs_12⟩
          refine DropGlueFacts.seq_clean (mid := $entry + 328#64) (P_mid :=
            vecGF16ListOf A (encA + 320#64) (c13 :: c14 :: rest) ∗
              (memRegion encA 320 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
            (Q := fun sm => Saved32Preserved s0 sm fsp encA) ?_ ?_
          · refine SepWP.dealloc_list_cons_step encA 296#64 304#64 312#64 320#64 296 320 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c12 _ _ ?_
            intro cap ptr
            dsimp only [vecGF16Dealloc, Saved32Preserved]
            by_cases hcap : (cap == 0#64) = true <;>
              simp only [hcap, ↓reduceIte, sepConj_emp]
            · wp_steps; wp_done
            · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_12]; ac_rfl) ?_; wp_done
          · intro s13 hpc13 hrun13 ⟨hx19_13, hx20_13, hx21_13, hx22_13, hx23_13, hx24_13, hx25_13, hx26_13, hx27_13, hx28_13, hx29_13, hsp_13, htrace_13, hvregs_13⟩
            refine DropGlueFacts.seq_clean (mid := $entry + 352#64) (P_mid :=
              vecGF16ListOf A (encA + 344#64) (c14 :: rest) ∗
                (memRegion encA 344 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
              (Q := fun sm => Saved32Preserved s0 sm fsp encA) ?_ ?_
            · refine SepWP.dealloc_list_cons_step encA 320#64 328#64 336#64 344#64 320 344 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c13 _ _ ?_
              intro cap ptr
              dsimp only [vecGF16Dealloc, Saved32Preserved]
              by_cases hcap : (cap == 0#64) = true <;>
                simp only [hcap, ↓reduceIte, sepConj_emp]
              · wp_steps; wp_done
              · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_13]; ac_rfl) ?_; wp_done
            · intro s14 hpc14 hrun14 ⟨hx19_14, hx20_14, hx21_14, hx22_14, hx23_14, hx24_14, hx25_14, hx26_14, hx27_14, hx28_14, hx29_14, hsp_14, htrace_14, hvregs_14⟩
              refine SepWP.dealloc_list_cons_step encA 344#64 352#64 360#64 368#64 344 368 rfl (by bv_omega) (by bv_omega) (by bv_omega) rfl (by decide) c14 _ _ ?_
              intro cap ptr
              dsimp only [vecGF16Dealloc, Saved32Preserved]
              by_cases hcap : (cap == 0#64) = true <;>
                simp only [hcap, ↓reduceIte, sepConj_emp]
              · wp_steps; wp_done
              · wp_steps; wp_apply; refine DropGlueFacts.align_pre (by rw [hsp_14]; ac_rfl) ?_; wp_done))

local macro "poly_encoder_local1_main_steps " entry:term : tactic => `(tactic| (
  wp_init x s0
  obtain ⟨encA, enc⟩ := x
  subst ‹s0.readReg64 (Reg.gpr 0#5) = encA›
  refine SepWP.weaken_pre
    (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A (s0.readReg64 (Reg.gpr 0#5)) enc)) ?_
  apply SepWP.exists_sepConj_left; intro tag
  apply SepWP.exists_sepConj_left; intro vecs
  wp_focus_pure
  intro hvecs_len
  dsimp only [NUM_POLYS] at hvecs_len
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, rfl⟩ :=
    list_length_16_elim hvecs_len
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropGluePoly16_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i w0 w1 w2 w3
  refine DropGlueFacts.seq_clean (mid := $entry + 12#64)
    (P_mid :=
      vecGF16ListOf A (s0.readReg64 (Reg.gpr 0#5) + 8#64)
        [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] ∗
      ((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ tag) ∗
        (A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (memRegion (s0.readReg64 (Reg.gpr 0#5) + 392#64) 8 ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3))))))
    (Q := fun sm =>
      sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5) ∧
      sm.readReg64 .x20 = s0.readReg64 .x20 ∧
      sm.readReg64 .x21 = s0.readReg64 .x21 ∧
      sm.readReg64 .x22 = s0.readReg64 .x22 ∧
      sm.readReg64 .x23 = s0.readReg64 .x23 ∧
      sm.readReg64 .x24 = s0.readReg64 .x24 ∧
      sm.readReg64 .x25 = s0.readReg64 .x25 ∧
      sm.readReg64 .x26 = s0.readReg64 .x26 ∧
      sm.readReg64 .x27 = s0.readReg64 .x27 ∧
      sm.readReg64 .x28 = s0.readReg64 .x28 ∧
      sm.readReg64 .x29 = s0.sp - 32#64 ∧
      sm.sp = s0.sp - 32#64 ∧
      sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · wp_steps
    refine DropGlueFacts.align_pre (by dsimp only [Reg.x19, Reg.lr, Reg.fp]; ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hx0_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hsp_1, htrace_1, hvregs_1⟩
    refine DropGlueFacts.seq_clean (mid := $entry + 208#64)
      (P_mid :=
        vecGF16ListOf A (s0.readReg64 (Reg.gpr 0#5) + 200#64)
          [c8, c9, c10, c11, c12, c13, c14, c15] ∗
        (memRegion (s0.readReg64 (Reg.gpr 0#5)) 200 ∗
          (A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (memRegion (s0.readReg64 (Reg.gpr 0#5) + 392#64) 8 ∗
              (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3))))))
      (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
      (hfirst8 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) tag hfsp_align
        c0 c1 c2 c3 c4 c5 c6 c7 [c8, c9, c10, c11, c12, c13, c14, c15] s1 _
        hpc1 hrun1 hx0_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hsp_1 htrace_1 hvregs_1)
      ?_
    intro s2 hpc2 hrun2 hpres2
    refine DropGlueFacts.seq_clean (mid := $entry + 376#64)
      (P_mid :=
        vecGF16ListOf A (s0.readReg64 (Reg.gpr 0#5) + 368#64) [c15] ∗
        (memRegion (s0.readReg64 (Reg.gpr 0#5)) 368 ∗
          (A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (memRegion (s0.readReg64 (Reg.gpr 0#5) + 392#64) 8 ∗
              (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3))))))
      (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
      (hmid7 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align
        c8 c9 c10 c11 c12 c13 c14 [c15] s2 _ hpc2 hrun2 hpres2)
      ?_
    intro s3 hpc3 hrun3 ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, hsp_3, htrace_3, hvregs_3⟩
    have hsingleton : vecGF16ListOf A (s0.readReg64 (Reg.gpr 0#5) + 368#64) [c15] =
        vecGF16Of A (s0.readReg64 (Reg.gpr 0#5) + 368#64) c15 :=
      arrayAt_singleton (fun cs addr => vecGF16Of A addr cs) 24 (s0.readReg64 (Reg.gpr 0#5) + 368#64) c15
    rw [hsingleton]
    refine SepWP.weaken_pre
      (vecGF16Of_step_entails A (s0.readReg64 (Reg.gpr 0#5)) 368#64 376#64 384#64 (by bv_omega) (by bv_omega) c15 _) ?_
    apply SepWP.exists_left; intro cap
    apply SepWP.exists_left; intro ptr
    dsimp only [vecGF16Dealloc]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp]
    · wp_steps
      refine SepWP.weaken_pre
        (Entails.trans (Entails.of_eq (by ac_rfl))
          (cap0_polyenc_post (s0.readReg64 (Reg.gpr 0#5)) cap ptr A.pool s0.sp
            (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3)) ?_
      wp_done
    · wp_steps
      refine SepWP.weaken_pre
        (Entails.trans (Entails.of_eq (by ac_rfl))
          (tail_dealloc_polyenc_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) cap ptr
            (A.live ptr (cap <<< 1#64).toNat 2 ∗ memRegion ptr (cap <<< 1#64).toNat)
            (memRegion (s0.readReg64 (Reg.gpr 0#5)) 368)
            (memRegion (s0.readReg64 (Reg.gpr 0#5) + 392#64) 8)
            A.pool s0.sp
            (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3)) ?_
      wp_apply
      refine SepWP.weaken_pre
        (Entails.trans (Entails.of_eq (by ac_rfl))
          (tail_dealloc_polyenc_post (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp)) ?_
      wp_done))

private theorem drop_glue_poly_encoder_local1_first8 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPolyEncoderLocal1Name +
        BitVec.ofNat 64 (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (s0 : State) (fsp encA tag : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c0 c1 c2 c3 c4 c5 c6 c7 : List GF16) (rest : List (List GF16))
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr dropPolyEncoderLocal1Name + 12#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = encA)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx21 : s.readReg64 .x21 = s0.readReg64 .x21)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x22)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23)
    (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hx29 : s.readReg64 .x29 = fsp)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPolyEncoderLocal1Name + 208#64)
      s
      (vecGF16ListOf A (encA + 8#64) (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
        ((encA ↦₆₄ tag) ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
      (fun sm Pm =>
        (Pm ⊢ vecGF16ListOf A (encA + 200#64) rest ∗
          (memRegion encA 200 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame))) ∧
        Saved32Preserved s0 sm fsp encA) := by
  simp only [rustDeallocSpec] at hdealloc
  dsimp only [dropProgAtExt, dropPolyEncoderLocal1Name, BitVec.ofNat_eq_ofNat] at *
  drop_poly_encoder_local1_fetches b (Rust.withPanics ext)
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" = entry
  examples_hide_fetches
  poly_encoder_local1_first8_steps entry

private theorem drop_glue_poly_encoder_local1_mid7 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPolyEncoderLocal1Name +
        BitVec.ofNat 64 (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (s0 : State) (fsp encA : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c8 c9 c10 c11 c12 c13 c14 : List GF16) (rest : List (List GF16))
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr dropPolyEncoderLocal1Name + 208#64)
    (hrun : s.status = .Running)
    (hpres : Saved32Preserved s0 s fsp encA) :
    SepWP (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPolyEncoderLocal1Name + 376#64)
      s
      (vecGF16ListOf A (encA + 200#64) (c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: rest) ∗
        (memRegion encA 200 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
      (fun sm Pm =>
        (Pm ⊢ vecGF16ListOf A (encA + 368#64) rest ∗
          (memRegion encA 368 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame))) ∧
        Saved32Preserved s0 sm fsp encA) := by
  simp only [rustDeallocSpec] at hdealloc
  dsimp only [dropProgAtExt, dropPolyEncoderLocal1Name, BitVec.ofNat_eq_ofNat] at *
  drop_poly_encoder_local1_fetches b (Rust.withPanics ext)
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" = entry
  examples_hide_fetches
  poly_encoder_local1_mid7_steps entry

/-- `core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]`
    (105 instructions) satisfies `dropGluePolyEncoderSpec A`. -/
theorem drop_glue_poly_encoder_local1_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc_base : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPolyEncoderLocal1Name)
      (dropGluePolyEncoderSpec A) := by
  simp only [dropGluePolyEncoderSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPolyEncoderLocal1Name +
        BitVec.ofNat 64 (ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := ls_rel% "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" "__rustc::__rust_dealloc")
      (b := b) (X := Rust.withPanics ext)
      dropPolyEncoderLocal1_fnOff dealloc_fnOff_drop (by decide))
    hdealloc_base
  have hdealloc := hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc
  have hfirst8 := drop_glue_poly_encoder_local1_first8 (b := b) (ext := ext) hdealloc_raw
  have hmid7 := drop_glue_poly_encoder_local1_mid7 (b := b) (ext := ext) hdealloc_raw
  drop_poly_encoder_local1_fetches b (Rust.withPanics ext)
  dsimp only [dropProgAtExt, dropPolyEncoderLocal1Name, BitVec.ofNat_eq_ofNat] at hdealloc hfirst8 hmid7 ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]" = entry
  examples_hide_fetches
  poly_encoder_local1_main_steps entry

/-! ## Relocatable `[LibsignalPlacement]` Proof of `PolyEncoder [local#1]` (Block `138`) -/

private theorem drop_glue_poly_encoder_local1_placed_first8 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_138).rebase (blkPl_138).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    (s0 : State) (fsp encA tag : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c0 c1 c2 c3 c4 c5 c6 c7 : List GF16) (rest : List (List GF16))
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_138).base + 12#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = encA)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx21 : s.readReg64 .x21 = s0.readReg64 .x21)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x22)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23)
    (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hx29 : s.readReg64 .x29 = fsp)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_138).rebase (blkPl_138).base H)
      ((blkPl_138).base + 208#64)
      s
      (vecGF16ListOf A (encA + 8#64) (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) ∗
        ((encA ↦₆₄ tag) ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
      (fun sm Pm =>
        (Pm ⊢ vecGF16ListOf A (encA + 200#64) rest ∗
          (memRegion encA 200 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame))) ∧
        Saved32Preserved s0 sm fsp encA) := by
  simp only [rustDeallocSpec] at hdealloc
  poly_encoder_local1_first8_steps (blkPl_138).base

private theorem drop_glue_poly_encoder_local1_placed_mid7 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_138).rebase (blkPl_138).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    (s0 : State) (fsp encA : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (c8 c9 c10 c11 c12 c13 c14 : List GF16) (rest : List (List GF16))
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_138).base + 208#64)
    (hrun : s.status = .Running)
    (hpres : Saved32Preserved s0 s fsp encA) :
    SepWP ((blkPC_138).rebase (blkPl_138).base H)
      ((blkPl_138).base + 376#64)
      s
      (vecGF16ListOf A (encA + 200#64) (c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: rest) ∗
        (memRegion encA 200 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))
      (fun sm Pm =>
        (Pm ⊢ vecGF16ListOf A (encA + 368#64) rest ∗
          (memRegion encA 368 ∗ (A.pool ∗ stackAt fsp allocHookStack ∗ Frame))) ∧
        Saved32Preserved s0 sm fsp encA) := by
  simp only [rustDeallocSpec] at hdealloc
  poly_encoder_local1_mid7_steps (blkPl_138).base

/-- Relocatable `core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#1]`
    (Block `138`) satisfies `dropGluePolyEncoderSpec A` under `[LibsignalPlacement]`. -/
theorem drop_glue_poly_encoder_local1_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc_raw : subroutine_ok ((blkPC_138).rebase (blkPl_138).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_138).rebase (blkPl_138).base H)
      (blkPl_138).base
      (dropGluePolyEncoderSpec A) := by
  simp only [dropGluePolyEncoderSpec]
  have hdealloc := hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc
  have hfirst8 := drop_glue_poly_encoder_local1_placed_first8 hdealloc_raw
  have hmid7 := drop_glue_poly_encoder_local1_placed_mid7 hdealloc_raw
  poly_encoder_local1_main_steps (blkPl_138).base

/-! ## `PolyEncoder [local#2]` (Block `272`, 2 instructions) -/

theorem polyEncoder_local2_post_join (encA tag : BitVec 64) :
    (encA ↦₆₄ tag) ∗ memRegion (encA + 8#64) polyArrayBytes ∗ memRegion (encA + 392#64) 8 ⊢
    memRegion encA polyEncoderSize := by
  have h8 : (encA ↦₆₄ tag) ⊢ memRegion encA 8 := pointsTo64_entails_memRegion encA tag
  have h392 : encA + 392#64 = (encA + 8#64) + BitVec.ofNat 64 polyArrayBytes := by
    show encA + 392#64 = (encA + 8#64) + 384#64
    bv_omega
  have h400 : memRegion encA polyEncoderSize =
      memRegion encA 8 ∗ (memRegion (encA + 8#64) polyArrayBytes ∗ memRegion (encA + 392#64) 8) := by
    rw [show polyEncoderSize = 8 + (polyArrayBytes + 8) from rfl,
        ProofLib.memRegion_split encA 8 (polyArrayBytes + 8) (by decide),
        ProofLib.memRegion_split' (b := encA + 8#64) (n := polyArrayBytes) (k := 8)
          (b' := encA + 392#64) rfl h392 (by decide)]
  rw [h400]
  exact sepConj_mono_left h8

/-- `core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]`
    (2 instructions: `add x0, x0, #8; b ...`) satisfies `dropGluePolyEncoderSpec A`. -/
theorem drop_glue_poly_encoder_local2_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc_base : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPolyEncoderLocal2Name)
      (dropGluePolyEncoderSpec A) := by
  simp only [dropGluePolyEncoderSpec]
  have hpoly16_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropPolyEncoderLocal2Name +
        (0#64 - BitVec.ofNat 64 (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]")))
      (dropGluePoly16Spec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropPolyEncoderLocal2Name =
        (dropProgAtExt b ext).fnAddr dropPoly16Name +
          BitVec.ofNat 64 (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]") :=
      Program.fnAddr_rel
        (k := ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]")
        (b := b) (X := Rust.withPanics ext)
        dropPoly16_fnOff dropPolyEncoderLocal2_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly16_ok_ext hdealloc_base)
    rw [hrel, BitVec.add_assoc]
    simp
  drop_poly_encoder_local2_fetches b (Rust.withPanics ext)
  dsimp only [dropProgAtExt, dropPolyEncoderLocal2Name, BitVec.ofNat_eq_ofNat] at hpoly16_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]" = entry
  examples_hide_fetches
  wp_init x s0
  obtain ⟨encA, enc⟩ := x
  subst ‹s0.readReg64 (Reg.gpr 0#5) = encA›
  refine SepWP.weaken_pre
    (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A (s0.readReg64 (Reg.gpr 0#5)) enc)) ?_
  apply SepWP.exists_sepConj_left; intro tag
  apply SepWP.exists_sepConj_left; intro vecs
  wp_focus_pure
  intro hvecs_len
  wp_steps
  wp_call hpoly16_raw ⟨s0.readReg64 (Reg.gpr 0#5) + 8#64, vecs⟩
  refine SepWP.focus_weaken
    (polyEncoder_local2_post_join (s0.readReg64 (Reg.gpr 0#5)) tag)
    (by sep_focus) ?_
  wp_done

/-- Relocatable `core::ptr::drop_glue::<spqr::encoding::polynomial::PolyEncoder> [local#2]`
    (Block `272`) satisfies `dropGluePolyEncoderSpec A` under `[LibsignalPlacement]`. -/
theorem drop_glue_poly_encoder_local2_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hpoly16_raw : subroutine_ok ((blkPC_272).rebase (blkPl_272).base H)
      (lsmpl.base 265)
      (dropGluePoly16Spec A)) :
    subroutine_ok ((blkPC_272).rebase (blkPl_272).base H)
      (blkPl_272).base
      (dropGluePolyEncoderSpec A) := by
  simp only [dropGluePolyEncoderSpec]
  wp_init x s0
  obtain ⟨encA, enc⟩ := x
  subst ‹s0.readReg64 (Reg.gpr 0#5) = encA›
  refine SepWP.weaken_pre
    (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A (s0.readReg64 (Reg.gpr 0#5)) enc)) ?_
  apply SepWP.exists_sepConj_left; intro tag
  apply SepWP.exists_sepConj_left; intro vecs
  wp_focus_pure
  intro hvecs_len
  wp_steps
  wp_call hpoly16_raw ⟨s0.readReg64 (Reg.gpr 0#5) + 8#64, vecs⟩
  refine SepWP.focus_weaken
    (polyEncoder_local2_post_join (s0.readReg64 (Reg.gpr 0#5)) tag)
    (by sep_focus) ?_
  wp_done

end CryptoVerification.SpqrV1.Drop
