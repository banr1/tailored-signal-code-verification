/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbOuter
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyDecoder>::into_pb`: Top-Level Proof

**Checked by Lean.**

Composes prologue allocation (`+0..+148`), the 16-slot outer loop (`IntoPbOuter`), and the
`drop_glue::<[SortedSet<Pt>; 16]>` epilogue (`+328 → s0.lr`) to prove `decoder_into_pb_ok_ext`,
`decoder_into_pb_ok_x`, and their Block `377` `[LibsignalPlacement]` counterparts.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
  (vecPtOf vecPtListOf sortedSetPtOf_eq_vecPtOf sortedSetPtListOf_eq_vecPtListOf
   dropGluePoly16Stack DropGlueSortedSetPt16Ghost dropGlueSortedSetPt16Spec
   dropProgAtExt dropSortedSetPt16Name dropSortedSetPt16_fnOff)
open CryptoVerification.CodeLayout
open CryptoGames.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
@[local arm64_norm, local wp_norm] theorem bv384_toNat : (384#64 : BitVec 64).toNat = 384 := rfl
@[local arm64_norm, local wp_norm] theorem bv8_toNat : (8#64 : BitVec 64).toNat = 8 := rfl

section Legacy

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

local macro "into_pb_fetches_range " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode spqrDecoderIntoPbBin $b $H libsignalSessionCode_fnOff_0x5dc38 0x5dc38 $k0 $len)

/-! ## Address Normalization and Memory / Stack Splitting Lemmas -/

@[local arm64_norm, local wp_norm] theorem off_8_add_8 (base : BitVec 64) : (base + 8#64) + 8#64 = base + 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem off_16_add_8 (base : BitVec 64) : (base + 16#64) + 8#64 = base + 24#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem off_24_add_4 (base : BitVec 64) : (base + 24#64) + 4#64 = base + 28#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem off_24_add_8 (base : BitVec 64) : (base + 24#64) + 8#64 = base + 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem off_32_add_8 (base : BitVec 64) : (base + 32#64) + 8#64 = base + 40#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem off_40_add_8 (base : BitVec 64) : (base + 40#64) + 8#64 = base + 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem off_48_add_8 (base : BitVec 64) : (base + 48#64) + 8#64 = base + 56#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem off_56_add_8 (base : BitVec 64) : (base + 56#64) + 8#64 = base + 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem off_64_add_8 (base : BitVec 64) : (base + 64#64) + 8#64 = base + 72#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem off_72_add_8 (base : BitVec 64) : (base + 72#64) + 8#64 = base + 80#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem off_80_add_8 (base : BitVec 64) : (base + 80#64) + 8#64 = base + 88#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem off_88_add_8 (base : BitVec 64) : (base + 88#64) + 8#64 = base + 96#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem off_96_add_8 (base : BitVec 64) : (base + 96#64) + 8#64 = base + 104#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem off_104_add_8 (base : BitVec 64) : (base + 104#64) + 8#64 = base + 112#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem off_112_add_8 (base : BitVec 64) : (base + 112#64) + 8#64 = base + 120#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem off_120_add_8 (base : BitVec 64) : (base + 120#64) + 8#64 = base + 128#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem off_128_add_8 (base : BitVec 64) : (base + 128#64) + 8#64 = base + 136#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem off_136_add_8 (base : BitVec 64) : (base + 136#64) + 8#64 = base + 144#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem off_144_add_8 (base : BitVec 64) : (base + 144#64) + 8#64 = base + 152#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sub_160_add_160 (sp : BitVec 64) : (sp - 160#64) + 160#64 = sp := by bv_omega

theorem pointsTo64_split32 (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) = (a ↦₃₂ v.truncate 32) ∗ ((a + 4#64) ↦₃₂ v.extractLsb' 32 32) := by
  apply IsBlock.eq (IsBlock.pointsTo64 a v)
    ((IsBlock.pointsTo32 a _).sepConj (IsBlock.pointsTo32 (a + 4#64) _) rfl (by decide))
  intro m
  rw [Memory.read32_eq_truncate_read64, Memory.read32_add4_eq_extract_read64]
  generalize m.read64 a = w
  constructor <;> intro h <;> bv_kernel

theorem pointsTo32_merge64 (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) = (a ↦₆₄ (hi ++ lo)) := by
  rw [pointsTo64_split32]
  have h1 : (hi ++ lo).truncate 32 = lo := by bv_kernel
  have h2 : (hi ++ lo).extractLsb' 32 32 = hi := by bv_kernel
  rw [h1, h2]

theorem pointsTo64_off24_split32 (base : BitVec 64) (v : BitVec 64) :
    ((base + 24#64) ↦₆₄ v) =
      ((base + 24#64) ↦₃₂ v.truncate 32) ∗ ((base + 28#64) ↦₃₂ v.extractLsb' 32 32) := by
  have h28 : (base + 24#64) + 4#64 = base + 28#64 := by bv_omega
  rw [pointsTo64_split32, h28]

theorem pointsTo32_off24_merge64 (base : BitVec 64) (lo hi : BitVec 32) :
    (((base + 24#64) ↦₃₂ lo) ∗ ((base + 28#64) ↦₃₂ hi)) = ((base + 24#64) ↦₆₄ (hi ++ lo)) := by
  have h28 : (base + 24#64) + 4#64 = base + 28#64 := by bv_omega
  rw [← h28, pointsTo32_merge64]

theorem unpack64_replace_low8 (v : BitVec 64) (b0 : BitVec 8) :
    unpack64 (v.extractLsb' 8 56 ++ b0) = b0 :: (unpack64 v).tail := by
  simp only [unpack64, List.tail_cons, List.cons.injEq, and_true]
  refine ⟨by bv_slice, by bv_slice, by bv_slice, by bv_slice,
          by bv_slice, by bv_slice, by bv_slice, by bv_slice⟩

theorem pointsTo64_off32_split_low8 (base : BitVec 64) (v : BitVec 64) :
    ((base + 32#64) ↦₆₄ v) =
      ((base + 32#64) ↦₈ v.extractLsb' 0 8) ∗
        ((base + 33#64) ↦ₛ (unpack64 v).tail) := by
  have h33 : (base + 32#64) + 1#64 = base + 33#64 := by bv_omega
  rw [pointsTo64_eq_pointsToBytes]
  conv => lhs; unfold unpack64
  rw [pointsToBytes_cons, h33]
  rfl

theorem pointsTo64_off32_merge_low8 (base : BitVec 64) (v : BitVec 64) (b0 : BitVec 8) :
    (((base + 32#64) ↦₈ b0) ∗ ((base + 33#64) ↦ₛ (unpack64 v).tail)) =
      ((base + 32#64) ↦₆₄ (v.extractLsb' 8 56 ++ b0)) := by
  have h33 : (base + 32#64) + 1#64 = base + 33#64 := by bv_omega
  rw [pointsTo64_eq_pointsToBytes, unpack64_replace_low8, pointsToBytes_cons, h33]

theorem pointsToBytes_entails_memRegion :
    ∀ (bs : List (BitVec 8)) (a : BitVec 64), bs.length < 2 ^ 64 → (a ↦ₛ bs) ⊢ memRegion a bs.length
  | [], a, _ => by
    simp [pointsToBytes_nil, memRegion_zero]
    exact Entails.refl _
  | b :: bs, a, hbs => by
    have hbs' : bs.length < 2 ^ 64 := by simp at hbs; omega
    rw [pointsToBytes_cons, List.length_cons, Nat.add_comm bs.length 1,
        ProofLib.memRegion_split a 1 bs.length (by omega)]
    exact sepConj_mono (pointsTo8_entails_memRegion a b)
      (pointsToBytes_entails_memRegion bs (a + 1#64) hbs')

theorem pointsTo64_off32_entails_isComplete_pad (out : BitVec 64) (v : BitVec 64) (b0 : BitVec 8) :
    ((out + 32#64) ↦₆₄ (v.extractLsb' 8 56 ++ b0)) ⊢
      ((out + 32#64) ↦₈ b0) ∗ memRegion (out + 33#64) 7 := by
  rw [← pointsTo64_off32_merge_low8 out v b0]
  have hlen : (unpack64 v).tail.length = 7 := rfl
  rw [← hlen]
  exact sepConj_mono_right (pointsToBytes_entails_memRegion (unpack64 v).tail (out + 33#64) (by rw [hlen]; decide))

theorem memRegion_40_split (out : BitVec 64) :
    memRegion out 40 =
      (∃∗ d0 : BitVec 64, out ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (out + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (out + 16#64) ↦₆₄ d2) ∗ (∃∗ d3 : BitVec 64, (out + 24#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (out + 32#64) ↦₆₄ d4) := by
  rw [show (40 : Nat) = 8 + (8 + (8 + (8 + 8))) by rfl,
      ProofLib.memRegion_split out 8 32 (by decide),
      ProofLib.memRegion_split (out + 8#64) 8 24 (by decide), off_8_add_8,
      ProofLib.memRegion_split (out + 16#64) 8 16 (by decide), off_16_add_8,
      ProofLib.memRegion_split (out + 24#64) 8 8 (by decide), off_24_add_8,
      ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
      ProofLib.memRegion_eight, ProofLib.memRegion_eight]

theorem decA_tail_rejoin_16 (decA : BitVec 64) (ptsNeeded : BitVec 64) (isComplete : BitVec 8) :
    ((decA + 384#64) ↦₆₄ ptsNeeded) ∗
      ((decA + 392#64) ↦₈ isComplete) ∗
      memRegion (decA + 393#64) 7 ⊢
    memRegion (decA + 384#64) 16 := by
  have h392 : (decA + 384#64) + 8#64 = decA + 392#64 := by bv_omega
  have h393 : (decA + 392#64) + 1#64 = decA + 393#64 := by bv_omega
  rw [show (16 : Nat) = 8 + (1 + 7) by rfl,
      ProofLib.memRegion_split (decA + 384#64) 8 (1 + 7) (by decide), h392,
      ProofLib.memRegion_split (decA + 392#64) 1 7 (by decide), h393]
  exact sepConj_mono (pointsTo64_entails_memRegion (decA + 384#64) ptsNeeded)
    (sepConj_mono_left (pointsTo8_entails_memRegion (decA + 392#64) isComplete))

theorem decA_rejoin_400 (decA : BitVec 64) :
    memRegion decA 384 ∗ memRegion (decA + 384#64) 16 = memRegion decA 400 := by
  rw [show (400 : Nat) = 384 + 16 by rfl,
      ProofLib.memRegion_split decA 384 16 (by decide)]

theorem stackAt_decoderIntoPb_split (sp : BitVec 64) :
    stackAt sp decoderIntoPbStack =
      stackAt (sp - 160#64) dropGluePoly16Stack ∗ cells (sp - 160#64) 20 :=
  LibsignalTripleRatchet.stackAt_split_cells sp dropGluePoly16Stack 20 (by decide)

theorem stackAt_dropGluePoly16_split_bottom (fsp : BitVec 64) :
    stackAt fsp dropGluePoly16Stack =
      memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack :=
  stackAt_split_bottom fsp allocHookStack 32 (by decide)

theorem cells20_fsp_eq (fsp : BitVec 64) :
    cells fsp 20 =
      (∃∗ v0 : BitVec 64, fsp ↦₆₄ v0) ∗ (∃∗ v1 : BitVec 64, (fsp + 8#64) ↦₆₄ v1) ∗
      (∃∗ v2 : BitVec 64, (fsp + 16#64) ↦₆₄ v2) ∗ (∃∗ v3 : BitVec 64, (fsp + 24#64) ↦₆₄ v3) ∗
      (∃∗ v4 : BitVec 64, (fsp + 32#64) ↦₆₄ v4) ∗ (∃∗ v5 : BitVec 64, (fsp + 40#64) ↦₆₄ v5) ∗
      (∃∗ v6 : BitVec 64, (fsp + 48#64) ↦₆₄ v6) ∗ (∃∗ v7 : BitVec 64, (fsp + 56#64) ↦₆₄ v7) ∗
      (∃∗ v8 : BitVec 64, (fsp + 64#64) ↦₆₄ v8) ∗ (∃∗ v9 : BitVec 64, (fsp + 72#64) ↦₆₄ v9) ∗
      (∃∗ v10 : BitVec 64, (fsp + 80#64) ↦₆₄ v10) ∗ (∃∗ v11 : BitVec 64, (fsp + 88#64) ↦₆₄ v11) ∗
      (∃∗ v12 : BitVec 64, (fsp + 96#64) ↦₆₄ v12) ∗ (∃∗ v13 : BitVec 64, (fsp + 104#64) ↦₆₄ v13) ∗
      (∃∗ v14 : BitVec 64, (fsp + 112#64) ↦₆₄ v14) ∗ (∃∗ v15 : BitVec 64, (fsp + 120#64) ↦₆₄ v15) ∗
      (∃∗ v16 : BitVec 64, (fsp + 128#64) ↦₆₄ v16) ∗ (∃∗ v17 : BitVec 64, (fsp + 136#64) ↦₆₄ v17) ∗
      (∃∗ v18 : BitVec 64, (fsp + 144#64) ↦₆₄ v18) ∗ (∃∗ v19 : BitVec 64, (fsp + 152#64) ↦₆₄ v19) := by
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    off_8_add_8, off_16_add_8, off_24_add_8, off_32_add_8, off_40_add_8,
    off_48_add_8, off_56_add_8, off_64_add_8, off_72_add_8, off_80_add_8,
    off_88_add_8, off_96_add_8, off_104_add_8, off_112_add_8, off_120_add_8,
    off_128_add_8, off_136_add_8, off_144_add_8, ← sepExists_sepConj_left]

theorem cells20_fsp_entails (fsp : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : BitVec 64) :
    (fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗
    ((fsp + 32#64) ↦₆₄ v4) ∗ ((fsp + 40#64) ↦₆₄ v5) ∗ ((fsp + 48#64) ↦₆₄ v6) ∗ ((fsp + 56#64) ↦₆₄ v7) ∗
    ((fsp + 64#64) ↦₆₄ v8) ∗ ((fsp + 72#64) ↦₆₄ v9) ∗ ((fsp + 80#64) ↦₆₄ v10) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
    ((fsp + 96#64) ↦₆₄ v12) ∗ ((fsp + 104#64) ↦₆₄ v13) ∗ ((fsp + 112#64) ↦₆₄ v14) ∗ ((fsp + 120#64) ↦₆₄ v15) ∗
    ((fsp + 128#64) ↦₆₄ v16) ∗ ((fsp + 136#64) ↦₆₄ v17) ∗ ((fsp + 144#64) ↦₆₄ v18) ∗ ((fsp + 152#64) ↦₆₄ v19) ⊢
    cells fsp 20 := by
  rw [cells20_fsp_eq fsp]
  exact sepConj_mono (Entails.sepExists_right v0 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v1 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v2 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v3 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v4 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v5 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v6 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v7 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v8 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v9 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v10 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v11 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v12 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v13 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v14 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v15 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v16 (Entails.refl _)) (sepConj_mono (Entails.sepExists_right v17 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right v18 (Entails.refl _)) (Entails.sepExists_right v19 (Entails.refl _))))))))))))))))))))

/-! ## `vecVecU8At` and `protoPolynomialDecoderAt` Construction Lemmas -/

theorem vecVecU8At_full_cap16 (A : RustAlloc) (v ptr : BitVec 64)
    (bss : List (List (BitVec 8))) (hlen : bss.length = 16) (hptr : ptr ≠ 0) :
    ((v ↦₆₄ 16#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 16#64) ∗
      arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr bss ∗ A.live ptr 384 8) ⊢
    vecVecU8At A v bss := by
  unfold vecVecU8At vecOf
  refine Entails.sepExists_right 16#64 (Entails.sepExists_right ptr ?_)
  unfold vecAt vecHeader vecBuf vecHeaderBytes
  have h16_ne : (16#64 : BitVec 64) ≠ 0#64 := by decide
  have h16_toNat : (16#64 : BitVec 64).toNat = 16 := rfl
  simp only [hlen, BitVec.ofNat_eq_ofNat, h16_ne, ↓reduceIte, h16_toNat,
    Nat.sub_self, Nat.zero_mul, memRegion_zero, sepConj_emp, emp_sepConj, Nat.reduceMul]
  have hp : 16 ≤ 16 ∧ 384 < 2 ^ 63 ∧ ptr ≠ 0#64 := ⟨by decide, by decide, hptr⟩
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono_right (Entails.pure_right hp (Entails.refl _)))

theorem protoPolynomialDecoderAt_entails (A : RustAlloc) (out ptr_pts : BitVec 64)
    (dec : PolyDecoder) (hlen : dec.pts.length = NUM_POLYS) (hptr : ptr_pts ≠ 0) :
    ((out ↦₆₄ 16#64) ∗ ((out + 8#64) ↦₆₄ ptr_pts) ∗ ((out + 16#64) ↦₆₄ 16#64) ∗
      ((out + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗
      ((out + 28#64) ↦₃₂ 16#32) ∗
      ((out + 32#64) ↦₈ boolByte dec.isComplete) ∗
      memRegion (out + 33#64) 7 ∗
      arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_pts
        ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗
      A.live ptr_pts 384 8) ⊢
    protoPolynomialDecoderAt A out dec.intoPb := by
  unfold protoPolynomialDecoderAt PolyDecoder.intoPb
  dsimp only [protoPolynomialDecoderPtsNeededOff, protoPolynomialDecoderPolysOff,
    protoPolynomialDecoderIsCompleteOff, protoPolynomialDecoderPadOff,
    protoPolynomialDecoderPadSize, NUM_POLYS, CHUNK_SIZE, BitVec.ofNat_eq_ofNat]
  rw [intoPb_pts]
  have hlen' : ((dec.pts.map SortedSetPt.vec).map serializePtList).length = 16 := by
    simp [hlen, NUM_POLYS, CHUNK_SIZE]
  have hpts := vecVecU8At_full_cap16 A out ptr_pts
    ((dec.pts.map SortedSetPt.vec).map serializePtList) hlen' hptr
  refine Entails.trans (Q :=
    ((out ↦₆₄ 16#64) ∗ ((out + 8#64) ↦₆₄ ptr_pts) ∗ ((out + 16#64) ↦₆₄ 16#64) ∗
      arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_pts
        ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗
      A.live ptr_pts 384 8) ∗
    (((out + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗
      ((out + 28#64) ↦₃₂ 16#32) ∗
      ((out + 32#64) ↦₈ boolByte dec.isComplete) ∗
      memRegion (out + 33#64) 7))
    (Entails.of_eq (by ac_rfl)) ?_
  exact sepConj_mono_left hpts

theorem drop_glue_sorted_set_pt16_ok_at_intoPb {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName +
        18446744073709456616#64)
      (dropGlueSortedSetPt16Spec A) := by
  have h := Drop.drop_glue_sorted_set_pt16_ok_ext hA.dealloc
  unfold dropProgAtExt at h
  have haddr : (tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName +
      18446744073709456616#64 =
      (tripleRatchetProgAtExt b ext).fnAddr dropSortedSetPt16Name := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase,
      libsignalSessionCode_fnOff_0x5dc38, dropSortedSetPt16_fnOff]
    bv_omega
  rw [haddr]
  exact h

/-! ## Epilogue (`+328 -> s0.lr`) -/

theorem into_pb_epilogue_post_entails (A : RustAlloc) (sp0 fsp out decA : BitVec 64)
    (hfsp : fsp = sp0 - 160#64)
    (ptsNeeded polys : BitVec 32)
    (v4 : BitVec 64) (isComplete : BitVec 8)
    (w0 w1 w2 w5 w6 w7 v11 : BitVec 64)
    (r29 r30 r27 r26 r25 r24 r23 r22 r21 r20 r19 : BitVec 64)
    (Frame : SepProp) :
    (fsp ↦₆₄ w0) ∗ ((fsp + 8#64) ↦₆₄ w1) ∗ ((fsp + 16#64) ↦₆₄ w2) ∗
      ((fsp + 24#64) ↦₆₄ (polys ++ ptsNeeded)) ∗
      ((fsp + 32#64) ↦₆₄ (v4.extractLsb' 8 56 ++ isComplete)) ∗
      ((fsp + 40#64) ↦₆₄ w5) ∗ ((fsp + 48#64) ↦₆₄ w6) ∗ ((fsp + 56#64) ↦₆₄ w7) ∗
      ((fsp + 64#64) ↦₆₄ r29) ∗ ((fsp + 72#64) ↦₆₄ r30) ∗ ((fsp + 80#64) ↦₆₄ r27) ∗
      ((fsp + 88#64) ↦₆₄ v11) ∗ ((fsp + 96#64) ↦₆₄ r26) ∗ ((fsp + 104#64) ↦₆₄ r25) ∗
      ((fsp + 112#64) ↦₆₄ r24) ∗ ((fsp + 120#64) ↦₆₄ r23) ∗ ((fsp + 128#64) ↦₆₄ r22) ∗
      ((fsp + 136#64) ↦₆₄ r21) ∗ ((fsp + 144#64) ↦₆₄ r20) ∗ ((fsp + 152#64) ↦₆₄ r19) ∗
      (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗
      ((out + 24#64) ↦₆₄ (polys ++ ptsNeeded)) ∗
      ((out + 32#64) ↦₆₄ (v4.extractLsb' 8 56 ++ isComplete)) ∗
      memRegion decA polyArrayBytes ∗ memRegion (decA + 384#64) 16 ∗
      A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame ⊢
    (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗
      ((out + 24#64) ↦₃₂ ptsNeeded) ∗ ((out + 28#64) ↦₃₂ polys) ∗
      ((out + 32#64) ↦₈ isComplete) ∗ memRegion (out + 33#64) 7 ∗
      memRegion decA 400 ∗
      A.pool ∗ stackAt sp0 decoderIntoPbStack ∗ Frame := by
  have hcells := cells20_fsp_entails fsp
    w0 w1 w2 (polys ++ ptsNeeded) (v4.extractLsb' 8 56 ++ isComplete) w5 w6 w7
    r29 r30 r27 v11 r26 r25 r24 r23 r22 r21 r20 r19
  have h24 : ((out + 24#64) ↦₆₄ (polys ++ ptsNeeded)) =
      (((out + 24#64) ↦₃₂ ptsNeeded) ∗ ((out + 28#64) ↦₃₂ polys)) :=
    (pointsTo32_off24_merge64 out ptsNeeded polys).symm
  have h32 := pointsTo64_off32_entails_isComplete_pad out v4 isComplete
  have hstk : stackAt sp0 decoderIntoPbStack = stackAt fsp dropGluePoly16Stack ∗ cells fsp 20 := by
    rw [hfsp, stackAt_decoderIntoPb_split sp0]
  dsimp only [polyArrayBytes]
  rw [hstk, ← decA_rejoin_400 decA, h24]
  refine Entails.trans (Q :=
    ((fsp ↦₆₄ w0) ∗ ((fsp + 8#64) ↦₆₄ w1) ∗ ((fsp + 16#64) ↦₆₄ w2) ∗
      ((fsp + 24#64) ↦₆₄ (polys ++ ptsNeeded)) ∗
      ((fsp + 32#64) ↦₆₄ (v4.extractLsb' 8 56 ++ isComplete)) ∗
      ((fsp + 40#64) ↦₆₄ w5) ∗ ((fsp + 48#64) ↦₆₄ w6) ∗ ((fsp + 56#64) ↦₆₄ w7) ∗
      ((fsp + 64#64) ↦₆₄ r29) ∗ ((fsp + 72#64) ↦₆₄ r30) ∗ ((fsp + 80#64) ↦₆₄ r27) ∗
      ((fsp + 88#64) ↦₆₄ v11) ∗ ((fsp + 96#64) ↦₆₄ r26) ∗ ((fsp + 104#64) ↦₆₄ r25) ∗
      ((fsp + 112#64) ↦₆₄ r24) ∗ ((fsp + 120#64) ↦₆₄ r23) ∗ ((fsp + 128#64) ↦₆₄ r22) ∗
      ((fsp + 136#64) ↦₆₄ r21) ∗ ((fsp + 144#64) ↦₆₄ r20) ∗ ((fsp + 152#64) ↦₆₄ r19)) ∗
    ((out + 32#64) ↦₆₄ (v4.extractLsb' 8 56 ++ isComplete)) ∗
    ((out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗
      ((out + 24#64) ↦₃₂ ptsNeeded) ∗ ((out + 28#64) ↦₃₂ polys) ∗
      memRegion decA 384 ∗ memRegion (decA + 384#64) 16 ∗
      A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame))
    (Entails.of_eq (by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hcells (sepConj_mono h32 (Entails.refl _))) ?_
  exact Entails.of_eq (by ac_rfl)

/-- Epilogue of `<PolyDecoder>::into_pb` (`+328` to `s0.lr`):
    copies the 40-byte `ProtoPolynomialDecoder` header from `[sp, #0x00..#0x28]` to `out` (`x20`),
    calls `drop_glue::<[SortedSet<Pt>; 16]>` (`0x4bd18`) on `decA` (`x19`), restores callee-saved
    registers and `sp`, and returns to `s0.lr`. -/
theorem into_pb_epilogue {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName +
        18446744073709456616#64)
      (dropGlueSortedSetPt16Spec A))
    (s0 : State) (fsp out decA : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 160#64))
    (ptsNeeded polys : BitVec 32)
    (v4 : BitVec 64) (isComplete : BitVec 8)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (vecs : List (List Pt)) (hvecs : vecs.length = NUM_POLYS)
    (w0 w1 w2 w5 w6 w7 v11 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName + 328#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 64#64)
    (hx19 : s.readReg64 .x19 = decA)
    (hx20 : s.readReg64 .x20 = out)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      ((fsp ↦₆₄ w0) ∗ ((fsp + 8#64) ↦₆₄ w1) ∗ ((fsp + 16#64) ↦₆₄ w2) ∗
        ((fsp + 24#64) ↦₃₂ ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ polys) ∗
        ((fsp + 32#64) ↦₈ isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
        ((fsp + 40#64) ↦₆₄ w5) ∗ ((fsp + 48#64) ↦₆₄ w6) ∗ ((fsp + 56#64) ↦₆₄ w7) ∗
        ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
        ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
        vecPtListOf A decA vecs ∗ memRegion (decA + 384#64) 16 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        (P' ⊢
          (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗
          ((out + 24#64) ↦₃₂ ptsNeeded) ∗ ((out + 28#64) ↦₃₂ polys) ∗
          ((out + 32#64) ↦₈ isComplete) ∗ memRegion (out + 33#64) 7 ∗
          memRegion decA 400 ∗
          A.pool ∗ stackAt s0.sp decoderIntoPbStack ∗ Frame) ∧
        sf.sp = s0.sp ∧
        sf.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 19#5) ∧
        sf.readReg64 (Reg.gpr 20#5) = s0.readReg64 (Reg.gpr 20#5) ∧
        sf.readReg64 (Reg.gpr 21#5) = s0.readReg64 (Reg.gpr 21#5) ∧
        sf.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) ∧
        sf.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
        sf.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
        sf.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
        sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
        sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
        sf.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sf.readReg64 (Reg.gpr 29#5) = s0.readReg64 (Reg.gpr 29#5) ∧
        sf.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5) ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0) := by
  simp only [dropGlueSortedSetPt16Spec] at hdrop
  into_pb_fetches_range b (Rust.withPanics ext) 328 56
  dsimp only [tripleRatchetProgAtExt, decoderIntoPbName, BitVec.ofNat_eq_ofNat] at hdrop hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::into_pb" = entry
  examples_hide_fetches
  conv => arg 4; rw [
    ← sepConj_assoc ((fsp + 24#64) ↦₃₂ ptsNeeded) ((fsp + 28#64) ↦₃₂ polys),
    pointsTo32_off24_merge64 fsp ptsNeeded polys,
    ← sepConj_assoc ((fsp + 32#64) ↦₈ isComplete) ((fsp + 33#64) ↦ₛ (unpack64 v4).tail),
    pointsTo64_off32_merge_low8 fsp v4 isComplete]
  wp_steps
  wp_call hdrop (⟨decA, vecs⟩ : DropGlueSortedSetPt16Ghost)
  wp_steps
  have hsp_ret : fsp + 160#64 = s0.sp := by rw [hfsp.eq]; bv_omega
  conv => arg 3; rw [hsp_ret]
  conv => arg 4; rw [hsp]
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (by ac_rfl))
      (into_pb_epilogue_post_entails A s0.sp fsp out decA hfsp.eq ptsNeeded polys v4 isComplete
        w0 w1 w2 w5 w6 w7 v11
        (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x27)
        (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)
        Frame)) ?_
  wp_done

/-! ## Prologue and Initialization (`+0 -> +148`, or OOM panic at `+396`) -/

@[local arm64_norm, local wp_norm]
theorem truncate_32_ofNat_64 (n : Nat) :
    (BitVec.ofNat 64 n).truncate 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

@[local arm64_norm, local wp_norm]
theorem setWidth_32_ofNat_64 (n : Nat) :
    BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n :=
  truncate_32_ofNat_64 n

@[local arm64_norm, local wp_norm]
theorem truncate_8_zeroExtend_64 (b : BitVec 8) :
    (b.zeroExtend 64).truncate 8 = b := by bv_omega

@[local arm64_norm, local wp_norm]
theorem setWidth_8_setWidth_64 (b : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 64 b) = b := by bv_omega

@[local arm64_norm, local wp_norm]
theorem setWidth_8_setWidth_32_setWidth_64 (b : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 b)) = b := by bv_omega

/-- Prologue and header initialization of `<PolyDecoder>::into_pb` (`+0 -> +148`, or OOM panic at `+396`). -/
theorem into_pb_prologue_and_init {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName +
        bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5dc38))
      sessionShimSpec)
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName +
        bv% (ls_off% "__rustc::__rust_alloc" - 0x5dc38))
      (rustAllocSpec A))
    {Q : State → SepProp → Prop} {R : SepProp}
    (s0 : State) (fsp out decA : BitVec 64)
    (hfsp : HiddenEq fsp (s0.sp - 160#64))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (ptsNeeded : Nat) (isComplete : Bool)
    (v0 v1 v2 v3 v4 v8 v9 v10 v12 v13 v14 v15 v16 v17 v18 v19 : BitVec 64)
    (Frame : SepProp)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = out)
    (hx1 : s0.readReg64 .x1 = decA)
    (hnext : ∀ (sm : State) (ptr_pts : BitVec 64),
      ptr_pts ≠ 0 →
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName + 148#64 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.readReg64 .x29 = fsp + 64#64 →
      sm.readReg64 .x19 = decA →
      sm.readReg64 .x20 = out →
      sm.readReg64 .x22 = 0#64 →
      sm.readReg64 .x23 = 24#64 →
      sm.readReg64 .x24 = 1#64 →
      sm.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
          ((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
          ((fsp + 32#64) ↦₈ boolByte isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
          ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
          memRegion (decA + 384#64) 16 ∗
          A.live ptr_pts 384 8 ∗ memRegion ptr_pts 384 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s0
      ((fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗
        ((fsp + 32#64) ↦₆₄ v4) ∗
        ((fsp + 64#64) ↦₆₄ v8) ∗ ((fsp + 72#64) ↦₆₄ v9) ∗ ((fsp + 80#64) ↦₆₄ v10) ∗
        ((fsp + 96#64) ↦₆₄ v12) ∗ ((fsp + 104#64) ↦₆₄ v13) ∗
        ((fsp + 112#64) ↦₆₄ v14) ∗ ((fsp + 120#64) ↦₆₄ v15) ∗
        ((fsp + 128#64) ↦₆₄ v16) ∗ ((fsp + 136#64) ↦₆₄ v17) ∗
        ((fsp + 144#64) ↦₆₄ v18) ∗ ((fsp + 152#64) ↦₆₄ v19) ∗
        ((decA + 384#64) ↦₆₄ BitVec.ofNat 64 ptsNeeded) ∗
        ((decA + 392#64) ↦₈ boolByte isComplete) ∗
        memRegion (decA + 393#64) 7 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  simp only [sessionShimSpec] at hshim
  simp only [rustAllocSpec] at halloc
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay384 : LayoutOk 384 8 := ⟨by decide, hpow8, by decide⟩
  into_pb_fetches_range b (Rust.withPanics ext) 0 104
  dsimp only [tripleRatchetProgAtExt, decoderIntoPbName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hnext ⊢
  have hentry_raw : HiddenEq ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder>::into_pb") (intoPbEntry b ext) :=
    ⟨intoPbEntry_raw_eq b ext⟩
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::into_pb" = entry
  have hentry : HiddenEq entry ((tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName) :=
    ⟨hentry_raw.eq.trans (intoPbEntry_eq b ext)⟩
  clear hentry_raw
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 64#64)
  wp_step
  conv => arg 3; simp only [← hfsp.eq]
  wp_steps
  wp_apply
  wp_steps
  conv => arg 4; simp only [← h_1]
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    refine sepWPp_pure_mid fun htr_oom => ?_
    refine SepWPp.seq_clean (mid := entry + 396#64)
      (P_mid :=
        A.pool ∗ stackAt sf.sp allocHookStack ∗
        (fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗
        ((fsp + 32#64) ↦₆₄ v4) ∗
        ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
        ((decA + 384#64) ↦₆₄ BitVec.ofNat 64 ptsNeeded) ∗
        ((decA + 392#64) ↦₈ boolByte isComplete) ∗
        memRegion (decA + 393#64) 7 ∗ Frame)
      (Q_mid := fun sm => sm.trace = s0.trace ++ [allocFailedEvent])
      ?_ ?_
    · wp_steps
      wp_done
    · intro sm hpcm hrunm htrm
      rw [hentry.eq] at hpcm
      exact into_pb_panic_396 s0 sm _ R hpcm hrunm htrm
  · have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hoom
    conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
    have hsp_sf1 : sf_1.sp = fsp := hsp_sf.trans h_1
    conv => arg 4; simp only [h_1, hsp_sf1]
    let ptr_pts := sf_1.readReg64 (Reg.gpr 0#5)
    conv => arg 4; rw [pointsTo64_off24_split32 fsp v3, pointsTo64_off32_split_low8 fsp v4]
    refine SepWPp.seq_clean (mid := entry + 148#64)
      (P_mid :=
        (fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
        ((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
        ((fsp + 32#64) ↦₈ boolByte isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
        ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
        memRegion (decA + 384#64) 16 ∗
        A.live ptr_pts 384 8 ∗ memRegion ptr_pts 384 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q_mid := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 64#64 ∧
        sm.readReg64 .x19 = decA ∧
        sm.readReg64 .x20 = out ∧
        sm.readReg64 .x22 = 0#64 ∧
        sm.readReg64 .x23 = 24#64 ∧
        sm.readReg64 .x24 = 1#64 ∧
        sm.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · wp_steps
      have htail := decA_tail_rejoin_16 decA (BitVec.ofNat 64 ptsNeeded) (boolByte isComplete)
      refine SepWP.weaken_pre (P' :=
        (((decA + 384#64) ↦₆₄ BitVec.ofNat 64 ptsNeeded) ∗
          ((decA + 392#64) ↦₈ boolByte isComplete) ∗
          memRegion (decA + 393#64) 7) ∗
        ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
          ((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
          ((fsp + 32#64) ↦₈ boolByte isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
          ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live ptr_pts 384 8 ∗ memRegion ptr_pts 384 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)) (Entails.of_eq (by ac_rfl)) ?_
      refine SepWP.weaken_pre (Entails.trans (sepConj_mono_left htail) (Entails.of_eq (by ac_rfl))) ?_
      wp_done
    · intro sm hpcm hrunm ⟨hspm, hx29m, hx19m, hx20m, hx22m, hx23m, hx24m, hx28m, htrm, hvregsm⟩
      exact hnext sm ptr_pts hoom hpcm hrunm hspm hx29m hx19m hx20m hx22m hx23m hx24m hx28m htrm hvregsm

/-! ## Main Theorems (`decoder_into_pb_ok_ext` and `decoder_into_pb_ok_x`) -/

def withSaved19_20 (s0 : State) (decA out : BitVec 64) : State :=
  (s0.writeReg64 .x19 decA).writeReg64 .x20 out

@[simp] theorem withSaved19_20_lr (s0 : State) (decA out : BitVec 64) :
    (withSaved19_20 s0 decA out).readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5) := by
  simp [withSaved19_20, wp_norm]

@[simp] theorem withSaved19_20_x19 (s0 : State) (decA out : BitVec 64) :
    (withSaved19_20 s0 decA out).readReg64 .x19 = decA := by
  simp [withSaved19_20, wp_norm]

@[simp] theorem withSaved19_20_x20 (s0 : State) (decA out : BitVec 64) :
    (withSaved19_20 s0 decA out).readReg64 .x20 = out := by
  simp [withSaved19_20, wp_norm]

@[simp] theorem withSaved19_20_x28 (s0 : State) (decA out : BitVec 64) :
    (withSaved19_20 s0 decA out).readReg64 .x28 = s0.readReg64 .x28 := by
  simp [withSaved19_20, wp_norm]

@[simp] theorem withSaved19_20_trace (s0 : State) (decA out : BitVec 64) :
    (withSaved19_20 s0 decA out).trace = s0.trace := rfl

@[simp] theorem withSaved19_20_vregs (s0 : State) (decA out : BitVec 64) :
    calleeSavedVRegs (withSaved19_20 s0 decA out) = calleeSavedVRegs s0 := rfl

@[simp] theorem withSaved19_20_onPanic (s0 sf : State) (decA out : BitVec 64) :
    intoPbOnPanic (withSaved19_20 s0 decA out) sf = intoPbOnPanic s0 sf := rfl

theorem sepWPp_elim_pure {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s Rest Q Qp) :
    SepWPp prog ret s (⌜φ⌝ ∗ Rest) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

theorem decoder_into_pb_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    DecoderIntoPbOkExt b A ext := by
  unfold DecoderIntoPbOkExt
  have hshim_raw := hA.shim_ok_at decoderIntoPbName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5dc38))
  have halloc_raw := hA.alloc_ok_at decoderIntoPbName
    (num% (ls_off% "__rustc::__rust_alloc" - 0x5dc38))
  have hdrop := drop_glue_sorted_set_pt16_ok_at_intoPb hA
  apply subroutine_ok_of_sepWPp
  intro ⟨out, decA, dec⟩ R s0 hpc hrun hpre hsp0
  simp only [decoderIntoPbSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  refine ⟨memRegion out protoPolynomialDecoderSize ∗
      polyDecoderAt A decA dec ∗
      A.pool ∗ stackAt s0.sp decoderIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  dsimp only [decoderIntoPbSpec, polyDecoderAt, polyDecoderPtsNeededOff, polyDecoderIsCompleteOff,
    polyDecoderPadOff, polyDecoderPadSize, protoPolynomialDecoderSize, polyDecoderSize,
    BitVec.ofNat_eq_ofNat] at *
  let fsp := s0.sp - 160#64
  have hfsp : HiddenEq fsp (s0.sp - 160#64) := ⟨rfl⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 160#64 hsp0 (by decide)
  conv => arg 4; rw [stackAt_decoderIntoPb_split s0.sp, ← hfsp.eq, stackAt_dropGluePoly16_split_bottom fsp]
  conv => arg 4; simp only [sepConj_assoc]
  refine SepWPp.weaken_pre (P' :=
      ⌜dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64⌝ ∗
      memRegion out 40 ∗ cells fsp 20 ∗
      sortedSetPtListOf A decA dec.pts ∗
      ((decA + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
      ((decA + 392#64) ↦₈ boolByte dec.isComplete) ∗
      memRegion (decA + 393#64) 7 ∗
      A.pool ∗ memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack)
    (Entails.of_eq (by ac_rfl)) ?_
  refine sepWPp_elim_pure fun ⟨hpts_len, _⟩ => ?_
  rw [sortedSetPtListOf_eq_vecPtListOf]
  conv => arg 4; simp only [memRegion_40_split out, cells20_fsp_eq fsp, sepConj_assoc, sepExists_sepConj_left]
  conv => arg 4; simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 => SepWPp.exists_elim fun d2 =>
    SepWPp.exists_elim fun d3 => SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun v0 =>
    SepWPp.exists_elim fun v1 => SepWPp.exists_elim fun v2 => SepWPp.exists_elim fun v3 =>
    SepWPp.exists_elim fun v4 => SepWPp.exists_elim fun v5 => SepWPp.exists_elim fun v6 =>
    SepWPp.exists_elim fun v7 => SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 =>
    SepWPp.exists_elim fun v10 => SepWPp.exists_elim fun v11 => SepWPp.exists_elim fun v12 =>
    SepWPp.exists_elim fun v13 => SepWPp.exists_elim fun v14 => SepWPp.exists_elim fun v15 =>
    SepWPp.exists_elim fun v16 => SepWPp.exists_elim fun v17 => SepWPp.exists_elim fun v18 =>
    SepWPp.exists_elim fun v19 => ?_
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (into_pb_prologue_and_init hshim_raw halloc_raw s0 fsp out decA hfsp hfsp_align
      dec.ptsNeeded dec.isComplete
      v0 v1 v2 v3 v4 v8 v9 v10 v12 v13 v14 v15 v16 v17 v18 v19
      (vecPtListOf A decA (dec.pts.map SortedSetPt.vec) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
        ((fsp + 40#64) ↦₆₄ v5) ∗ ((fsp + 48#64) ↦₆₄ v6) ∗ ((fsp + 56#64) ↦₆₄ v7) ∗
        ((fsp + 88#64) ↦₆₄ v11) ∗
        memRegion (fsp - 4128#64) 32)
      ‹_› ‹_› ‹_› ‹_› ?_)
  intro s1 ptr_pts hptr_pts hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1 hvregs1
  let s_ref := withSaved19_20 s0 decA out
  have hrem_len : (dec.pts.map SortedSetPt.vec).length = 16 := by
    simp [hpts_len, NUM_POLYS, CHUNK_SIZE]
  have hrem_ne : dec.pts.map SortedSetPt.vec ≠ [] := by
    intro h; simp [h] at hrem_len
  generalize hQ_goal : (fun (sf : State) (P_f : SepProp) => _ ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) = Q_goal
  have hloop := pts_outer_loop (R := R) (Q := Q_goal) hshim_raw halloc_raw s_ref fsp ptr_pts hfsp_align
    (dec.pts.map SortedSetPt.vec) hrem_ne 0 (by omega) v5 v6 v7 s1
    (((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
      ((fsp + 32#64) ↦₈ boolByte dec.isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
      ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
      ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
      (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
      ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
      memRegion (decA + 384#64) 16 ∗
      A.live ptr_pts 384 8 ∗
      memRegion (fsp - 4128#64) 32)
    hpc1 hrun1 hsp1 hx29_1
    (by simpa [s_ref] using hx19_1)
    (by simpa [s_ref] using hx20_1)
    hx22_1 hx23_1 hx24_1
    (by simpa [s_ref] using hx28_1)
    (by simpa [s_ref] using htr1)
    (by simpa [s_ref] using hvregs1)
  dsimp only [s_ref] at hloop
  simp only [withSaved19_20_lr, withSaved19_20_x19, withSaved19_20_x20, withSaved19_20_x28,
    withSaved19_20_trace, withSaved19_20_vregs, withSaved19_20_onPanic, Nat.mul_zero, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, hrem_len] at hloop
  change _ → SepWPp _ _ _ _ _ _ at hloop
  refine SepWPp.weaken_pre (by dsimp only [vecPtListOf]; exact Entails.of_eq (by ac_rfl)) (hloop ?_)
  intro s2 w40 w48 w56 hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx28_2 htr2 hvregs2
  have hep := into_pb_epilogue hdrop s0 fsp out decA hfsp
    (BitVec.ofNat 32 dec.ptsNeeded) 16#32 v4 (boolByte dec.isComplete)
    hfsp_align (dec.pts.map SortedSetPt.vec) (by simp [hpts_len])
    16#64 ptr_pts 16#64 w40 w48 w56 v11
    d0 d1 d2 d3 d4 s2
    (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_pts
        ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗
      A.live ptr_pts 384 8)
    hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 htr2 hvregs2
  have hpre2 :
      ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 16#64) ∗
        ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
        arrayAt (fun pts addr => vecPtOf A addr pts) 24 decA (dec.pts.map SortedSetPt.vec) ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_pts
          ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
          ((fsp + 32#64) ↦₈ boolByte dec.isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
          ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
          ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
          (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
          ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
          memRegion (decA + 384#64) 16 ∗
          A.live ptr_pts 384 8 ∗
          memRegion (fsp - 4128#64) 32)) ⊢
      ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 16#64) ∗
        ((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
        ((fsp + 32#64) ↦₈ boolByte dec.isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
        ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
        ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
        ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
        vecPtListOf A decA (dec.pts.map SortedSetPt.vec) ∗
        memRegion (decA + 384#64) 16 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_pts
            ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗
          A.live ptr_pts 384 8)) := by
    rw [stackAt_dropGluePoly16_split_bottom fsp]
    dsimp only [vecPtListOf]
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre2 (SepWPp.seq_clean hep ?_)
  intro sf hpcf hrunf ⟨hspf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hx30f, htrf, hvregsf⟩
  have hpost_dec := protoPolynomialDecoderAt_entails A out ptr_pts dec hpts_len hptr_pts
  subst hQ_goal
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f,
    hspf, ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f.trans hx28_2, hx29f, hvregsf⟩⟩
  exact Entails.pure_right htrf (Entails.trans (Entails.of_eq (by ac_rfl))
    (Entails.trans (sepConj_mono_left (Q := memRegion decA 400 ∗ A.pool ∗ stackAt s0.sp decoderIntoPbStack) hpost_dec)
      (Entails.of_eq (by ac_rfl))))

private theorem satisfies_anyHeap_frame {m : Memory} {P F R : SepProp}
    (h : m ⊨ (P ∗ anyHeap) ∗ F ∗ R) :
    m ⊨ (P ∗ anyHeap) ∗ R := by
  have h1 : (P ∗ anyHeap) ∗ F ∗ R ⊢ (P ∗ anyHeap) ∗ R := by
    rw [sepConj_assoc P anyHeap (F ∗ R), ← sepConj_assoc anyHeap F R, sepConj_assoc P anyHeap R]
    exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap (anyHeap ∗ F)))
  exact Satisfies.mono h1 h

/-- `decoderIntoPbSpec A` entails `decoderIntoPbSpecX A` by framing the unused bottom stack region. -/
theorem decoderIntoPbSpecX_of_decoderIntoPbSpec {P : Program} {addr : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok P addr (decoderIntoPbSpec A)) :
    subroutine_ok P addr (decoderIntoPbSpecX A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hle : decoderIntoPbStack ≤ decoderIntoPbStackX := by decide
  have hsplit : stackAt s0.sp decoderIntoPbStackX =
      memRegion (s0.sp - BitVec.ofNat 64 decoderIntoPbStackX)
        (decoderIntoPbStackX - decoderIntoPbStack) ∗
        stackAt s0.sp decoderIntoPbStack := by
    have h1 := stackAt_split_bottom s0.sp decoderIntoPbStack
      (decoderIntoPbStackX - decoderIntoPbStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 decoderIntoPbStackX)
      (decoderIntoPbStackX - decoderIntoPbStack) ∗ R
  have hpre' : s0.mem ⊨ (decoderIntoPbSpec A).pre x s0 ∗ R' := by
    dsimp only [decoderIntoPbSpecX, decoderIntoPbSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome x R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [decoderIntoPbSpecX, decoderIntoPbSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame hpost⟩)
  · dsimp only [decoderIntoPbSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact (not_satisfies_false_sepConj hoom).elim

theorem decoder_into_pb_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    DecoderIntoPbOkX img A ext :=
  subroutine_ok_inImage_of_subroutine_ok img
    (decoderIntoPbSpecX_of_decoderIntoPbSpec (decoder_into_pb_ok_ext hA))

end Legacy

/-! ## Relocatable (`[LibsignalPlacement]`) Proofs for Block `377` -/

attribute [local arm64_norm, local wp_norm]
  off_8_add_8 off_16_add_8 off_24_add_4 off_24_add_8 off_32_add_8 off_40_add_8
  off_48_add_8 off_56_add_8 off_64_add_8 off_72_add_8 off_80_add_8 off_88_add_8
  off_96_add_8 off_104_add_8 off_112_add_8 off_120_add_8 off_128_add_8
  off_136_add_8 off_144_add_8 sub_160_add_160
  truncate_32_ofNat_64 setWidth_32_ofNat_64 truncate_8_zeroExtend_64
  setWidth_8_setWidth_64 setWidth_8_setWidth_32_setWidth_64

theorem into_pb_epilogue_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdrop : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec A))
    (s0 : State) (fsp out decA : BitVec 64) (hfsp : HiddenEq fsp (s0.sp - 160#64))
    (ptsNeeded polys : BitVec 32) (v4 : BitVec 64) (isComplete : BitVec 8)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (vecs : List (List Pt)) (hvecs : vecs.length = NUM_POLYS)
    (w0 w1 w2 w5 w6 w7 v11 d0 d1 d2 d3 d4 : BitVec 64) (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_377).base + 328#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 64#64) (hx19 : s.readReg64 .x19 = decA) (hx20 : s.readReg64 .x20 = out)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      ((fsp ↦₆₄ w0) ∗ ((fsp + 8#64) ↦₆₄ w1) ∗ ((fsp + 16#64) ↦₆₄ w2) ∗
        ((fsp + 24#64) ↦₃₂ ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ polys) ∗
        ((fsp + 32#64) ↦₈ isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
        ((fsp + 40#64) ↦₆₄ w5) ∗ ((fsp + 48#64) ↦₆₄ w6) ∗ ((fsp + 56#64) ↦₆₄ w7) ∗
        ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
        ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
        vecPtListOf A decA vecs ∗ memRegion (decA + 384#64) 16 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        (P' ⊢
          (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗
          ((out + 24#64) ↦₃₂ ptsNeeded) ∗ ((out + 28#64) ↦₃₂ polys) ∗
          ((out + 32#64) ↦₈ isComplete) ∗ memRegion (out + 33#64) 7 ∗
          memRegion decA 400 ∗ A.pool ∗ stackAt s0.sp decoderIntoPbStack ∗ Frame) ∧
        sf.sp = s0.sp ∧
        sf.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 19#5) ∧
        sf.readReg64 (Reg.gpr 20#5) = s0.readReg64 (Reg.gpr 20#5) ∧
        sf.readReg64 (Reg.gpr 21#5) = s0.readReg64 (Reg.gpr 21#5) ∧
        sf.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) ∧
        sf.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
        sf.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
        sf.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
        sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
        sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
        sf.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sf.readReg64 (Reg.gpr 29#5) = s0.readReg64 (Reg.gpr 29#5) ∧
        sf.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5) ∧
        sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) := by
  simp only [dropGlueSortedSetPt16Spec, BitVec.ofNat_eq_ofNat] at hdrop
  conv => arg 4; rw [
    ← sepConj_assoc ((fsp + 24#64) ↦₃₂ ptsNeeded) ((fsp + 28#64) ↦₃₂ polys),
    pointsTo32_off24_merge64 fsp ptsNeeded polys,
    ← sepConj_assoc ((fsp + 32#64) ↦₈ isComplete) ((fsp + 33#64) ↦ₛ (unpack64 v4).tail),
    pointsTo64_off32_merge_low8 fsp v4 isComplete]
  wp_steps; wp_call hdrop (⟨decA, vecs⟩ : DropGlueSortedSetPt16Ghost); wp_steps
  have hsp_ret : fsp + 160#64 = s0.sp := by rw [hfsp.eq]; bv_omega
  conv => arg 3; rw [hsp_ret]
  conv => arg 4; rw [hsp]
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl))
    (into_pb_epilogue_post_entails A s0.sp fsp out decA hfsp.eq ptsNeeded polys v4 isComplete
      w0 w1 w2 w5 w6 w7 v11 (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x27)
      (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
      (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) Frame)) (by wp_done)

theorem into_pb_prologue_and_init_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    {Q : State → SepProp → Prop} {R : SepProp}
    (s0 : State) (fsp out decA : BitVec 64) (hfsp : HiddenEq fsp (s0.sp - 160#64))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (ptsNeeded : Nat) (isComplete : Bool)
    (v0 v1 v2 v3 v4 v8 v9 v10 v12 v13 v14 v15 v16 v17 v18 v19 : BitVec 64) (Frame : SepProp)
    (hpc : s0.pc = (blkPl_377).base) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = out) (hx1 : s0.readReg64 .x1 = decA)
    (hnext : ∀ (sm : State) (ptr_pts : BitVec 64),
      ptr_pts ≠ 0 → sm.pc = (blkPl_377).base + 148#64 → sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x29 = fsp + 64#64 → sm.readReg64 .x19 = decA → sm.readReg64 .x20 = out →
      sm.readReg64 .x22 = 0#64 → sm.readReg64 .x23 = 24#64 → sm.readReg64 .x24 = 1#64 →
      sm.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) →
      sm.trace = s0.trace → calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
        ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
          ((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
          ((fsp + 32#64) ↦₈ boolByte isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
          ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗
          ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗ ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗ ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗ ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗ memRegion (decA + 384#64) 16 ∗
          A.live ptr_pts 384 8 ∗ memRegion ptr_pts 384 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s0
      ((fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗
        ((fsp + 32#64) ↦₆₄ v4) ∗ ((fsp + 64#64) ↦₆₄ v8) ∗ ((fsp + 72#64) ↦₆₄ v9) ∗
        ((fsp + 80#64) ↦₆₄ v10) ∗ ((fsp + 96#64) ↦₆₄ v12) ∗ ((fsp + 104#64) ↦₆₄ v13) ∗
        ((fsp + 112#64) ↦₆₄ v14) ∗ ((fsp + 120#64) ↦₆₄ v15) ∗ ((fsp + 128#64) ↦₆₄ v16) ∗
        ((fsp + 136#64) ↦₆₄ v17) ∗ ((fsp + 144#64) ↦₆₄ v18) ∗ ((fsp + 152#64) ↦₆₄ v19) ∗
        ((decA + 384#64) ↦₆₄ BitVec.ofNat 64 ptsNeeded) ∗ ((decA + 392#64) ↦₈ boolByte isComplete) ∗
        memRegion (decA + 393#64) 7 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  have hshim : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimSpec := SpqrV1.Alloc.spqr_hook_ok_of_mem hshim_sat
  have halloc : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) := SpqrV1.Alloc.spqr_hook_ok_of_mem halloc_sat
  simp only [sessionShimSpec, BitVec.ofNat_eq_ofNat] at hshim
  simp only [rustAllocSpec, BitVec.ofNat_eq_ofNat] at halloc
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay384 : LayoutOk 384 8 := ⟨by decide, hpow8, by decide⟩
  apply SepWPp.of_sepWP (mid := (blkPl_377).base + 64#64)
  wp_step; (conv => arg 3; simp only [← hfsp.eq])
  wp_steps; wp_apply; wp_steps; (conv => arg 4; simp only [← h_1]); wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    refine sepWPp_pure_mid fun htr_oom => ?_
    refine SepWPp.seq_clean (mid := (blkPl_377).base + 396#64)
      (P_mid := A.pool ∗ stackAt sf.sp allocHookStack ∗ (fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗
        ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗ ((fsp + 32#64) ↦₆₄ v4) ∗
        ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗
        ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗ ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗
        ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗ ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗
        ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗ ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗ ((decA + 384#64) ↦₆₄ BitVec.ofNat 64 ptsNeeded) ∗
        ((decA + 392#64) ↦₈ boolByte isComplete) ∗ memRegion (decA + 393#64) 7 ∗ Frame)
      (Q_mid := fun sm => sm.trace = s0.trace ++ [allocFailedEvent])
      (by wp_steps; wp_done)
      (fun sm hpcm hrunm htrm => into_pb_panic_396_placed h_panic s0 sm _ R hpcm hrunm htrm)
  · have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
    have hsp_sf1 : sf_1.sp = fsp := hsp_sf.trans h_1
    conv => arg 4; simp only [h_1, hsp_sf1]
    let ptr_pts := sf_1.readReg64 (Reg.gpr 0#5)
    conv => arg 4; rw [pointsTo64_off24_split32 fsp v3, pointsTo64_off32_split_low8 fsp v4]
    refine SepWPp.seq_clean (mid := (blkPl_377).base + 148#64)
      (P_mid := (fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
        ((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
        ((fsp + 32#64) ↦₈ boolByte isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
        ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗
        ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗ ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗
        ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗ ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗
        ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗ ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗ memRegion (decA + 384#64) 16 ∗
        A.live ptr_pts 384 8 ∗ memRegion ptr_pts 384 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q_mid := fun sm =>
        sm.sp = fsp ∧ sm.readReg64 .x29 = fsp + 64#64 ∧ sm.readReg64 .x19 = decA ∧
        sm.readReg64 .x20 = out ∧ sm.readReg64 .x22 = 0#64 ∧ sm.readReg64 .x23 = 24#64 ∧
        sm.readReg64 .x24 = 1#64 ∧ sm.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
        sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · wp_steps
      have htail := decA_tail_rejoin_16 decA (BitVec.ofNat 64 ptsNeeded) (boolByte isComplete)
      refine SepWP.weaken_pre (P' :=
        (((decA + 384#64) ↦₆₄ BitVec.ofNat 64 ptsNeeded) ∗
          ((decA + 392#64) ↦₈ boolByte isComplete) ∗ memRegion (decA + 393#64) 7) ∗
        ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
          ((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
          ((fsp + 32#64) ↦₈ boolByte isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
          ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗
          ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗ ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗ ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗ ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗ A.live ptr_pts 384 8 ∗ memRegion ptr_pts 384 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)) (Entails.of_eq (by ac_rfl)) ?_
      exact SepWP.weaken_pre (Entails.trans (sepConj_mono_left htail) (Entails.of_eq (by ac_rfl))) (by wp_done)
    · intro sm hpcm hrunm ⟨hspm, hx29m, hx19m, hx20m, hx22m, hx23m, hx24m, hx28m, htrm, hvregsm⟩
      exact hnext sm ptr_pts hoom hpcm hrunm hspm hx29m hx19m hx20m hx22m hx23m hx24m hx28m htrm hvregsm

theorem decoder_into_pb_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdrop : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec A)) :
    DecoderIntoPbPlacedOkExt A ext := by
  unfold DecoderIntoPbPlacedOkExt
  apply subroutine_ok_of_sepWPp
  intro ⟨out, decA, dec⟩ R s0 hpc hrun hpre hsp0
  simp only [decoderIntoPbSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  refine ⟨memRegion out protoPolynomialDecoderSize ∗ polyDecoderAt A decA dec ∗
      A.pool ∗ stackAt s0.sp decoderIntoPbStack, R, by simpa [sepConj_assoc] using hmem, ?_⟩
  dsimp only [decoderIntoPbSpec, polyDecoderAt, polyDecoderPtsNeededOff, polyDecoderIsCompleteOff,
    polyDecoderPadOff, polyDecoderPadSize, protoPolynomialDecoderSize, polyDecoderSize,
    BitVec.ofNat_eq_ofNat] at *
  let fsp := s0.sp - 160#64
  have hfsp : HiddenEq fsp (s0.sp - 160#64) := ⟨rfl⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 160#64 hsp0 (by decide)
  conv => arg 4; rw [stackAt_decoderIntoPb_split s0.sp, ← hfsp.eq, stackAt_dropGluePoly16_split_bottom fsp]
  conv => arg 4; simp only [sepConj_assoc]
  refine SepWPp.weaken_pre (P' :=
      ⌜dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64⌝ ∗ memRegion out 40 ∗ cells fsp 20 ∗
      sortedSetPtListOf A decA dec.pts ∗ ((decA + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
      ((decA + 392#64) ↦₈ boolByte dec.isComplete) ∗ memRegion (decA + 393#64) 7 ∗
      A.pool ∗ memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack) (Entails.of_eq (by ac_rfl)) ?_
  refine sepWPp_elim_pure fun ⟨hpts_len, _⟩ => ?_
  rw [sortedSetPtListOf_eq_vecPtListOf]
  conv => arg 4; simp only [memRegion_40_split out, cells20_fsp_eq fsp, sepConj_assoc, sepExists_sepConj_left]
  conv => arg 4; simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 => SepWPp.exists_elim fun d2 =>
    SepWPp.exists_elim fun d3 => SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun v0 =>
    SepWPp.exists_elim fun v1 => SepWPp.exists_elim fun v2 => SepWPp.exists_elim fun v3 =>
    SepWPp.exists_elim fun v4 => SepWPp.exists_elim fun v5 => SepWPp.exists_elim fun v6 =>
    SepWPp.exists_elim fun v7 => SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 =>
    SepWPp.exists_elim fun v10 => SepWPp.exists_elim fun v11 => SepWPp.exists_elim fun v12 =>
    SepWPp.exists_elim fun v13 => SepWPp.exists_elim fun v14 => SepWPp.exists_elim fun v15 =>
    SepWPp.exists_elim fun v16 => SepWPp.exists_elim fun v17 => SepWPp.exists_elim fun v18 =>
    SepWPp.exists_elim fun v19 => ?_
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (into_pb_prologue_and_init_placed h_panic hshim_sat halloc_sat s0 fsp out decA hfsp hfsp_align
      dec.ptsNeeded dec.isComplete v0 v1 v2 v3 v4 v8 v9 v10 v12 v13 v14 v15 v16 v17 v18 v19
      (vecPtListOf A decA (dec.pts.map SortedSetPt.vec) ∗ (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗
        ((out + 16#64) ↦₆₄ d2) ∗ ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
        ((fsp + 40#64) ↦₆₄ v5) ∗ ((fsp + 48#64) ↦₆₄ v6) ∗ ((fsp + 56#64) ↦₆₄ v7) ∗
        ((fsp + 88#64) ↦₆₄ v11) ∗ memRegion (fsp - 4128#64) 32) ‹_› ‹_› ‹_› ‹_› ?_)
  intro s1 ptr_pts hptr_pts hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1 hvregs1
  let s_ref := withSaved19_20 s0 decA out
  have hrem_len : (dec.pts.map SortedSetPt.vec).length = 16 := by simp [hpts_len, NUM_POLYS, CHUNK_SIZE]
  have hrem_ne : dec.pts.map SortedSetPt.vec ≠ [] := by intro h; simp [h] at hrem_len
  generalize hQ_goal : (fun (sf : State) (P_f : SepProp) => _ ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) = Q_goal
  have hloop := pts_outer_loop_placed (R := R) (Q := Q_goal) h_panic hshim_sat halloc_sat s_ref fsp ptr_pts hfsp_align
    (dec.pts.map SortedSetPt.vec) hrem_ne 0 (by omega) v5 v6 v7 s1
    (((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
      ((fsp + 32#64) ↦₈ boolByte dec.isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
      ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
      ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
      (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
      ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
      memRegion (decA + 384#64) 16 ∗ A.live ptr_pts 384 8 ∗ memRegion (fsp - 4128#64) 32)
    hpc1 hrun1 hsp1 hx29_1 (by simpa [s_ref] using hx19_1) (by simpa [s_ref] using hx20_1)
    hx22_1 hx23_1 hx24_1 (by simpa [s_ref] using hx28_1) (by simpa [s_ref] using htr1) (by simpa [s_ref] using hvregs1)
  dsimp only [s_ref] at hloop
  simp only [withSaved19_20_lr, withSaved19_20_x19, withSaved19_20_x20, withSaved19_20_x28,
    withSaved19_20_trace, withSaved19_20_vregs, withSaved19_20_onPanic, Nat.mul_zero, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, hrem_len] at hloop
  change _ → SepWPp _ _ _ _ _ _ at hloop
  refine SepWPp.weaken_pre (by dsimp only [vecPtListOf]; exact Entails.of_eq (by ac_rfl)) (hloop ?_)
  intro s2 w40 w48 w56 hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx28_2 htr2 hvregs2
  have hep := into_pb_epilogue_placed hdrop s0 fsp out decA hfsp
    (BitVec.ofNat 32 dec.ptsNeeded) 16#32 v4 (boolByte dec.isComplete)
    hfsp_align (dec.pts.map SortedSetPt.vec) (by simp [hpts_len])
    16#64 ptr_pts 16#64 w40 w48 w56 v11 d0 d1 d2 d3 d4 s2
    (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_pts
        ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗ A.live ptr_pts 384 8)
    hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 htr2 hvregs2
  have hpre2 :
      ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 16#64) ∗
        ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
        arrayAt (fun pts addr => vecPtOf A addr pts) 24 decA (dec.pts.map SortedSetPt.vec) ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_pts
          ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
          ((fsp + 32#64) ↦₈ boolByte dec.isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
          ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
          ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
          (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
          ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
          memRegion (decA + 384#64) 16 ∗ A.live ptr_pts 384 8 ∗ memRegion (fsp - 4128#64) 32)) ⊢
      ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 16#64) ∗
        ((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
        ((fsp + 32#64) ↦₈ boolByte dec.isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
        ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
        ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
        ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
        vecPtListOf A decA (dec.pts.map SortedSetPt.vec) ∗ memRegion (decA + 384#64) 16 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_pts
            ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗ A.live ptr_pts 384 8)) := by
    rw [stackAt_dropGluePoly16_split_bottom fsp]; dsimp only [vecPtListOf]; exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre2 (SepWPp.seq_clean hep ?_)
  intro sf hpcf hrunf ⟨hspf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hx30f, htrf, hvregsf⟩
  have hpost_dec := protoPolynomialDecoderAt_entails A out ptr_pts dec hpts_len hptr_pts
  subst hQ_goal
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f,
    hspf, ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f.trans hx28_2, hx29f, hvregsf⟩⟩
  exact Entails.pure_right htrf (Entails.trans (Entails.of_eq (by ac_rfl))
    (Entails.trans (sepConj_mono_left (Q := memRegion decA 400 ∗ A.pool ∗ stackAt s0.sp decoderIntoPbStack) hpost_dec)
      (Entails.of_eq (by ac_rfl))))

theorem decoder_into_pb_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdrop : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsmpl.base 264) (dropGlueSortedSetPt16Spec A)) :
    DecoderIntoPbPlacedOkX A ext :=
  decoderIntoPbSpecX_of_decoderIntoPbSpec (decoder_into_pb_placed_ok_ext h_panic hshim_sat halloc_sat hdrop)

end CryptoVerification.SpqrV1.Poly.DecoderPb
