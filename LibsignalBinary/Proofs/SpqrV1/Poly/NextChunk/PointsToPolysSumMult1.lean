/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk`: `gf::parallel_mult` Shift Table and Odd Tail

**Checked by Lean.**

Pure `parallelMult` lemmas, stack shift-table representation (`fsp + 112..232`), bitvector
normalization rules, shift-table initialization (`+2752 -> +3384`), and odd trailing element
multiplication (`+3608 -> +3784`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_two_sm :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_eight_sm :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

/-! ## 1. Pure Lemmas for `parallelMult` -/

@[simp]
theorem parallelMult_nil (a : GF16) : parallelMult a [] = [] := rfl

@[simp]
theorem parallelMult_singleton (a x : GF16) :
    parallelMult a [x] = [⟨unaccelerated.mul x.value a.value⟩] := rfl

@[simp]
theorem parallelMult_pair_cons (a x1 x2 : GF16) (rest : List GF16) :
    parallelMult a (x1 :: x2 :: rest) =
      ⟨unaccelerated.mul a.value x1.value⟩ ::
      ⟨unaccelerated.mul a.value x2.value⟩ ::
      parallelMult a rest := rfl

theorem parallelMult_length (a : GF16) :
    ∀ cs : List GF16, (parallelMult a cs).length = cs.length
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: rest => by
    simp [parallelMult_pair_cons, parallelMult_length a rest]

theorem parallelMult_append_pair (a : GF16) :
    ∀ (pre : List GF16) (hpre_even : pre.length % 2 = 0) (rest : List GF16),
      parallelMult a (pre ++ rest) =
        pre.map (fun x => (⟨unaccelerated.mul a.value x.value⟩ : GF16)) ++
          parallelMult a rest
  | [], _, rest => rfl
  | [_], h, _ => by simp at h
  | x1 :: x2 :: pre', h, rest => by
    have h' : pre'.length % 2 = 0 := by
      simp only [List.length_cons] at h
      omega
    simp only [List.cons_append, parallelMult_pair_cons, List.map_cons,
      parallelMult_append_pair a pre' h' rest]

theorem parallelMult_even_eq_map (a : GF16) (cs : List GF16) (heven : cs.length % 2 = 0) :
    parallelMult a cs =
      cs.map (fun x => (⟨unaccelerated.mul a.value x.value⟩ : GF16)) := by
  have h := parallelMult_append_pair a cs heven []
  simpa using h

theorem parallelMult_odd_eq_map_snoc (a : GF16) (pre : List GF16) (heven : pre.length % 2 = 0)
    (last : GF16) :
    parallelMult a (pre ++ [last]) =
      pre.map (fun x => (⟨unaccelerated.mul a.value x.value⟩ : GF16)) ++
        [⟨unaccelerated.mul last.value a.value⟩] :=
  parallelMult_append_pair a pre heven [last]

/-! ## 2. PC-Relative `ADRP` Lemmas in `0x6ae54..0x6b1ac` -/

@[local arm64_norm, local wp_norm]
theorem fnAddr_adrp_6ae54 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr polyNextChunkName + 2768#64) &&&
      0xfffffffffffff000#64) + bv% (ls_bytes% "00000b1016201d302c402750" - 0x65000) =
      b + bv% (ls_xref% 0x5e970 0x5e974) := by
  rw [Program.fnAddr_rebase, polyNextChunk_fnOff]
  revert hb; bv_bits

@[local arm64_norm, local wp_norm]
theorem fnAddr_adrp_6b0c8 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr polyNextChunkName + 3396#64) &&&
      0xfffffffffffff000#64) + bv% (ls_xref% 0x5e628 0x5e62c - 0x65000) =
      b + bv% (ls_xref% 0x5e628 0x5e62c) := by
  rw [Program.fnAddr_rebase, polyNextChunk_fnOff]
  revert hb; bv_bits

@[local arm64_norm, local wp_norm]
theorem fnAddr_adrp_6b0e0 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr polyNextChunkName + 3420#64) &&&
      0xfffffffffffff000#64) + bv% (ls_xref% 0x5e638 0x5e63c - 0x65000) =
      b + bv% (ls_xref% 0x5e638 0x5e63c) := by
  rw [Program.fnAddr_rebase, polyNextChunk_fnOff]
  revert hb; bv_bits

@[local arm64_norm, local wp_norm]
theorem fnAddr_adrp_6b19c {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr polyNextChunkName + 3608#64) &&&
      0xfffffffffffff000#64) + bv% (ls_xref% 0x5e628 0x5e62c - 0x65000) =
      b + bv% (ls_xref% 0x5e628 0x5e62c) := by
  rw [Program.fnAddr_rebase, polyNextChunk_fnOff]
  revert hb; bv_bits

@[local arm64_norm, local wp_norm]
theorem fnAddr_adrp_6b1ac {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr polyNextChunkName + 3624#64) &&&
      0xfffffffffffff000#64) + bv% (ls_xref% 0x5e638 0x5e63c - 0x65000) =
      b + bv% (ls_xref% 0x5e638 0x5e63c) := by
  rw [Program.fnAddr_rebase, polyNextChunk_fnOff]
  revert hb; bv_bits

/-! ## 3. Stack-Slot Bundle for `parallel_mult` (`fsp + 112..232`) -/

/-- The 15 precomputed 32-bit shifts of `yv` stored on the stack at `fsp + 148..228` by
    `0x6ae44..0x6aebc` and read on every iteration of `0x6aec4..0x6b0b8`. -/
def shiftTableAt (fsp : BitVec 64) (yv : BitVec 16) : SepProp :=
  let y32 := BitVec.zeroExtend 32 yv
  ((fsp + 148#64) ↦₃₂ (y32 <<< 15)) ∗ ((fsp + 152#64) ↦₃₂ (y32 <<< 14)) ∗
  ((fsp + 156#64) ↦₃₂ (y32 <<< 13)) ∗ ((fsp + 160#64) ↦₃₂ (y32 <<< 12)) ∗
  ((fsp + 164#64) ↦₃₂ (y32 <<< 11)) ∗ ((fsp + 168#64) ↦₃₂ (y32 <<< 10)) ∗
  ((fsp + 172#64) ↦₃₂ (y32 <<< 9)) ∗ ((fsp + 176#64) ↦₃₂ (y32 <<< 8)) ∗
  ((fsp + 180#64) ↦₃₂ (y32 <<< 7)) ∗ ((fsp + 184#64) ↦₃₂ (y32 <<< 6)) ∗
  ((fsp + 192#64) ↦₃₂ (y32 <<< 5)) ∗ ((fsp + 200#64) ↦₃₂ (y32 <<< 4)) ∗
  ((fsp + 208#64) ↦₃₂ (y32 <<< 3)) ∗ ((fsp + 216#64) ↦₃₂ (y32 <<< 2)) ∗
  ((fsp + 224#64) ↦₃₂ (y32 <<< 1))

/-- Raw 32-bit stack slots at `fsp + 148..228`. -/
def shiftSlotsRawAt (fsp : BitVec 64) : SepProp :=
  ∃∗ d148 : BitVec 32, ∃∗ d152 : BitVec 32, ∃∗ d156 : BitVec 32, ∃∗ d160 : BitVec 32,
  ∃∗ d164 : BitVec 32, ∃∗ d168 : BitVec 32, ∃∗ d172 : BitVec 32, ∃∗ d176 : BitVec 32,
  ∃∗ d180 : BitVec 32, ∃∗ d184 : BitVec 32, ∃∗ d192 : BitVec 32, ∃∗ d200 : BitVec 32,
  ∃∗ d208 : BitVec 32, ∃∗ d216 : BitVec 32, ∃∗ d224 : BitVec 32,
    ((fsp + 148#64) ↦₃₂ d148) ∗ ((fsp + 152#64) ↦₃₂ d152) ∗ ((fsp + 156#64) ↦₃₂ d156) ∗
    ((fsp + 160#64) ↦₃₂ d160) ∗ ((fsp + 164#64) ↦₃₂ d164) ∗ ((fsp + 168#64) ↦₃₂ d168) ∗
    ((fsp + 172#64) ↦₃₂ d172) ∗ ((fsp + 176#64) ↦₃₂ d176) ∗ ((fsp + 180#64) ↦₃₂ d180) ∗
    ((fsp + 184#64) ↦₃₂ d184) ∗ ((fsp + 192#64) ↦₃₂ d192) ∗ ((fsp + 200#64) ↦₃₂ d200) ∗
    ((fsp + 208#64) ↦₃₂ d208) ∗ ((fsp + 216#64) ↦₃₂ d216) ∗ ((fsp + 224#64) ↦₃₂ d224)

theorem shiftTableAt_entails_raw (fsp : BitVec 64) (yv : BitVec 16) :
    shiftTableAt fsp yv ⊢ shiftSlotsRawAt fsp := by
  unfold shiftTableAt shiftSlotsRawAt; dsimp only
  iterate 15 apply Entails.sepExists_right
  exact Entails.refl _

/-- Unused 4-byte padding cells in `fsp + 144..232`. -/
def shiftTablePadAt (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 144#64) 4 ∗ memRegion (fsp + 188#64) 4 ∗ memRegion (fsp + 196#64) 4 ∗
  memRegion (fsp + 204#64) 4 ∗ memRegion (fsp + 212#64) 4 ∗ memRegion (fsp + 220#64) 4 ∗
  memRegion (fsp + 228#64) 4

theorem memRegion_112_split_sum (fsp : BitVec 64) :
    memRegion (fsp + 112#64) 120 ⊢
      ∃∗ u112 : BitVec 64, ∃∗ u120 : BitVec 64, ∃∗ u128 : BitVec 64, ∃∗ u136 : BitVec 64,
        ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 120#64) ↦₆₄ u120) ∗
        ((fsp + 128#64) ↦₆₄ u128) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
        shiftSlotsRawAt fsp ∗ shiftTablePadAt fsp := by
  unfold shiftSlotsRawAt shiftTablePadAt
  rw [ProofLib.memRegion_split' (b := fsp + 112#64) (n := 8) (k := 112) (b' := fsp + 120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 120#64) (n := 8) (k := 104) (b' := fsp + 128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 128#64) (n := 8) (k := 96) (b' := fsp + 136#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 136#64) (n := 8) (k := 88) (b' := fsp + 144#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 144#64) (n := 4) (k := 84) (b' := fsp + 148#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 148#64) (n := 4) (k := 80) (b' := fsp + 152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 152#64) (n := 4) (k := 76) (b' := fsp + 156#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 156#64) (n := 4) (k := 72) (b' := fsp + 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 160#64) (n := 4) (k := 68) (b' := fsp + 164#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 164#64) (n := 4) (k := 64) (b' := fsp + 168#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 168#64) (n := 4) (k := 60) (b' := fsp + 172#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 172#64) (n := 4) (k := 56) (b' := fsp + 176#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 176#64) (n := 4) (k := 52) (b' := fsp + 180#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 180#64) (n := 4) (k := 48) (b' := fsp + 184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 184#64) (n := 4) (k := 44) (b' := fsp + 188#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 188#64) (n := 4) (k := 40) (b' := fsp + 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 192#64) (n := 4) (k := 36) (b' := fsp + 196#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 196#64) (n := 4) (k := 32) (b' := fsp + 200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 200#64) (n := 4) (k := 28) (b' := fsp + 204#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 204#64) (n := 4) (k := 24) (b' := fsp + 208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 208#64) (n := 4) (k := 20) (b' := fsp + 212#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 212#64) (n := 4) (k := 16) (b' := fsp + 216#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 216#64) (n := 4) (k := 12) (b' := fsp + 220#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 220#64) (n := 4) (k := 8) (b' := fsp + 224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 224#64) (n := 4) (k := 4) (b' := fsp + 228#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 112#64), ProofLib.memRegion_eight (fsp + 120#64),
      ProofLib.memRegion_eight (fsp + 128#64), ProofLib.memRegion_eight (fsp + 136#64),
      ProofLib.memRegion_four (fsp + 148#64), ProofLib.memRegion_four (fsp + 152#64),
      ProofLib.memRegion_four (fsp + 156#64), ProofLib.memRegion_four (fsp + 160#64),
      ProofLib.memRegion_four (fsp + 164#64), ProofLib.memRegion_four (fsp + 168#64),
      ProofLib.memRegion_four (fsp + 172#64), ProofLib.memRegion_four (fsp + 176#64),
      ProofLib.memRegion_four (fsp + 180#64), ProofLib.memRegion_four (fsp + 184#64),
      ProofLib.memRegion_four (fsp + 192#64), ProofLib.memRegion_four (fsp + 200#64),
      ProofLib.memRegion_four (fsp + 208#64), ProofLib.memRegion_four (fsp + 216#64),
      ProofLib.memRegion_four (fsp + 224#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d224; apply Entails.sepExists_elim; intro d216
  apply Entails.sepExists_elim; intro d208; apply Entails.sepExists_elim; intro d200
  apply Entails.sepExists_elim; intro d192; apply Entails.sepExists_elim; intro d184
  apply Entails.sepExists_elim; intro d180; apply Entails.sepExists_elim; intro d176
  apply Entails.sepExists_elim; intro d172; apply Entails.sepExists_elim; intro d168
  apply Entails.sepExists_elim; intro d164; apply Entails.sepExists_elim; intro d160
  apply Entails.sepExists_elim; intro d156; apply Entails.sepExists_elim; intro d152
  apply Entails.sepExists_elim; intro d148; apply Entails.sepExists_elim; intro u136
  apply Entails.sepExists_elim; intro u128; apply Entails.sepExists_elim; intro u120
  apply Entails.sepExists_elim; intro u112
  apply Entails.sepExists_right u112; apply Entails.sepExists_right u120
  apply Entails.sepExists_right u128; apply Entails.sepExists_right u136
  apply Entails.sepExists_right d148; apply Entails.sepExists_right d152
  apply Entails.sepExists_right d156; apply Entails.sepExists_right d160
  apply Entails.sepExists_right d164; apply Entails.sepExists_right d168
  apply Entails.sepExists_right d172; apply Entails.sepExists_right d176
  apply Entails.sepExists_right d180; apply Entails.sepExists_right d184
  apply Entails.sepExists_right d192; apply Entails.sepExists_right d200
  apply Entails.sepExists_right d208; apply Entails.sepExists_right d216
  apply Entails.sepExists_right d224
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_112_fold_sum (fsp u112 u120 u128 u136 : BitVec 64) :
    ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 120#64) ↦₆₄ u120) ∗
    ((fsp + 128#64) ↦₆₄ u128) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
    shiftSlotsRawAt fsp ∗ shiftTablePadAt fsp ⊢
    memRegion (fsp + 112#64) 120 := by
  unfold shiftSlotsRawAt shiftTablePadAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d148; apply Entails.sepExists_elim; intro d152
  apply Entails.sepExists_elim; intro d156; apply Entails.sepExists_elim; intro d160
  apply Entails.sepExists_elim; intro d164; apply Entails.sepExists_elim; intro d168
  apply Entails.sepExists_elim; intro d172; apply Entails.sepExists_elim; intro d176
  apply Entails.sepExists_elim; intro d180; apply Entails.sepExists_elim; intro d184
  apply Entails.sepExists_elim; intro d192; apply Entails.sepExists_elim; intro d200
  apply Entails.sepExists_elim; intro d208; apply Entails.sepExists_elim; intro d216
  apply Entails.sepExists_elim; intro d224
  rw [ProofLib.memRegion_split' (b := fsp + 112#64) (n := 8) (k := 112) (b' := fsp + 120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 120#64) (n := 8) (k := 104) (b' := fsp + 128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 128#64) (n := 8) (k := 96) (b' := fsp + 136#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 136#64) (n := 8) (k := 88) (b' := fsp + 144#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 144#64) (n := 4) (k := 84) (b' := fsp + 148#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 148#64) (n := 4) (k := 80) (b' := fsp + 152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 152#64) (n := 4) (k := 76) (b' := fsp + 156#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 156#64) (n := 4) (k := 72) (b' := fsp + 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 160#64) (n := 4) (k := 68) (b' := fsp + 164#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 164#64) (n := 4) (k := 64) (b' := fsp + 168#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 168#64) (n := 4) (k := 60) (b' := fsp + 172#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 172#64) (n := 4) (k := 56) (b' := fsp + 176#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 176#64) (n := 4) (k := 52) (b' := fsp + 180#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 180#64) (n := 4) (k := 48) (b' := fsp + 184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 184#64) (n := 4) (k := 44) (b' := fsp + 188#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 188#64) (n := 4) (k := 40) (b' := fsp + 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 192#64) (n := 4) (k := 36) (b' := fsp + 196#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 196#64) (n := 4) (k := 32) (b' := fsp + 200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 200#64) (n := 4) (k := 28) (b' := fsp + 204#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 204#64) (n := 4) (k := 24) (b' := fsp + 208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 208#64) (n := 4) (k := 20) (b' := fsp + 212#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 212#64) (n := 4) (k := 16) (b' := fsp + 216#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 216#64) (n := 4) (k := 12) (b' := fsp + 220#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 220#64) (n := 4) (k := 8) (b' := fsp + 224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 224#64) (n := 4) (k := 4) (b' := fsp + 228#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 112#64), ProofLib.memRegion_eight (fsp + 120#64),
      ProofLib.memRegion_eight (fsp + 128#64), ProofLib.memRegion_eight (fsp + 136#64),
      ProofLib.memRegion_four (fsp + 148#64), ProofLib.memRegion_four (fsp + 152#64),
      ProofLib.memRegion_four (fsp + 156#64), ProofLib.memRegion_four (fsp + 160#64),
      ProofLib.memRegion_four (fsp + 164#64), ProofLib.memRegion_four (fsp + 168#64),
      ProofLib.memRegion_four (fsp + 172#64), ProofLib.memRegion_four (fsp + 176#64),
      ProofLib.memRegion_four (fsp + 180#64), ProofLib.memRegion_four (fsp + 184#64),
      ProofLib.memRegion_four (fsp + 192#64), ProofLib.memRegion_four (fsp + 200#64),
      ProofLib.memRegion_four (fsp + 208#64), ProofLib.memRegion_four (fsp + 216#64),
      ProofLib.memRegion_four (fsp + 224#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_right d224; apply Entails.sepExists_right d216
  apply Entails.sepExists_right d208; apply Entails.sepExists_right d200
  apply Entails.sepExists_right d192; apply Entails.sepExists_right d184
  apply Entails.sepExists_right d180; apply Entails.sepExists_right d176
  apply Entails.sepExists_right d172; apply Entails.sepExists_right d168
  apply Entails.sepExists_right d164; apply Entails.sepExists_right d160
  apply Entails.sepExists_right d156; apply Entails.sepExists_right d152
  apply Entails.sepExists_right d148; apply Entails.sepExists_right u136
  apply Entails.sepExists_right u128; apply Entails.sepExists_right u120
  apply Entails.sepExists_right u112
  exact Entails.of_eq (by ac_rfl)

/-! ## 4. Bitvector Normalization Rules for `0x6ae44..0x6b0b8` (`parallel_mult` Pair Loop) -/

def pmTerm_sm (cv yv : BitVec 16) (i : Nat) : BitVec 32 :=
  (BitVec.zeroExtend 32 cv <<< i) &&& (if yv.getLsbD i = true then 0xffff_ffff#32 else 0#32)

@[local arm64_norm ↓, local wp_norm ↓]
theorem truncate32_zext64_sm (v : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 v) = v := by bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem truncate32_zext64_16_sm (v : BitVec 16) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 v) = BitVec.zeroExtend 32 v := by bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem truncate32_shl_zext64_32_sm (v : BitVec 32) (k : Nat) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 v <<< k) = v <<< k := by
  ext i hi; simp [hi, show i - k < 32 by omega]

@[local arm64_norm ↓, local wp_norm ↓]
theorem truncate16_zext64_16_sm (v : BitVec 16) :
    BitVec.truncate 16 (BitVec.zeroExtend 64 v) = v := by bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem zext16_trunc32_zext64_16_sm (v : BitVec 16) :
    BitVec.zeroExtend 16 (BitVec.truncate 32 (BitVec.zeroExtend 64 v)) = v := by bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem truncate32_xor_zext64_sm (a b : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 a ^^^ BitVec.zeroExtend 64 b) = a ^^^ b := by bv_slice

@[local arm64_norm ↓, local wp_norm ↓]
theorem truncate32_and_zext64_sm (a b : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 a &&& BitVec.zeroExtend 64 b) = a &&& b := by bv_slice

@[local arm64_norm ↓, local wp_norm ↓]
theorem truncate64_sxth32_16_sm (x : BitVec 16) :
    BitVec.truncate 32 (BitVec.signExtend 64 x) = BitVec.signExtend 32 x := by bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem sbfx_bit0_sxth32_sm (x : BitVec 16) :
    BitVec.truncate 32
      (BitVec.zeroExtend 64 (BitVec.signExtend 32 x) >>> 0 &&& 1#64 |||
        (if (BitVec.zeroExtend 64 (BitVec.signExtend 32 x)).getLsbD 0 = true then
            18446744073709551615#64
          else 0#64) &&&
          18446744073709551614#64) =
      if x.getLsbD 0 = true then 0xffffffff#32 else 0#32 := by bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem pmTerm_bit0_sm (yv x : BitVec 16) :
    (if x.getLsbD 0 = true then 0xffffffff#32 else 0#32) &&& BitVec.zeroExtend 32 yv =
      pmTerm_sm yv x 0 := by
  dsimp only [pmTerm_sm]; rw [BitVec.shiftLeft_zero, BitVec.and_comm]

@[local arm64_norm ↓, local wp_norm ↓]
theorem pmTerm_bit0_zext64_sm (yv x : BitVec 16) :
    BitVec.truncate 32
      (BitVec.zeroExtend 64 (if x.getLsbD 0 = true then 0xffffffff#32 else 0#32) &&&
        BitVec.zeroExtend 64 yv) =
      pmTerm_sm yv x 0 := by
  dsimp only [pmTerm_sm]; generalize x.getLsbD 0 = b; cases b <;> bv_slice

@[local arm64_norm ↓, local wp_norm ↓]
theorem truncate16_truncate32_64_sm (x : BitVec 64) :
    BitVec.truncate 16 (BitVec.truncate 32 x) = BitVec.truncate 16 x := by bv_bits

private theorem getLsbD_ffff_sm (j : Fin 32) : (0xffffffff#32).getLsbD j.1 = true := by revert j; decide
private theorem getLsbD_zero_sm (j : Fin 32) : (0#32).getLsbD j.1 = false := by revert j; decide

theorem sshiftRight31_eq_ite_sm (w : BitVec 32) :
    w.sshiftRight 31 = if w.getLsbD 31 = true then 0xffffffff#32 else 0#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_sshiftRight, decide_eq_false (by omega : ¬32 ≤ j), Bool.not_false,
      Bool.true_and, BitVec.msb_eq_getLsbD_last]
  have h31 : (if 31 + j < 32 then w.getLsbD (31 + j) else w.getLsbD (32 - 1)) = w.getLsbD 31 := by
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rfl
    · simp [show ¬(31 + j < 32) by omega]
  rw [h31]
  cases w.getLsbD 31
  · exact (getLsbD_zero_sm ⟨j, hj⟩).symm
  · exact (getLsbD_ffff_sm ⟨j, hj⟩).symm

@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl30_asr31 (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 30).sshiftRight 31 = if x.getLsbD 1 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm]; have h : (BitVec.signExtend 32 x <<< 30).getLsbD 31 = x.getLsbD 1 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl29_asr31 (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 29).sshiftRight 31 = if x.getLsbD 2 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm]; have h : (BitVec.signExtend 32 x <<< 29).getLsbD 31 = x.getLsbD 2 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl28_asr31 (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 28).sshiftRight 31 = if x.getLsbD 3 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm]; have h : (BitVec.signExtend 32 x <<< 28).getLsbD 31 = x.getLsbD 3 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl27_asr31 (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 27).sshiftRight 31 = if x.getLsbD 4 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm]; have h : (BitVec.signExtend 32 x <<< 27).getLsbD 31 = x.getLsbD 4 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl26_asr31 (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 26).sshiftRight 31 = if x.getLsbD 5 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm]; have h : (BitVec.signExtend 32 x <<< 26).getLsbD 31 = x.getLsbD 5 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl25_asr31 (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 25).sshiftRight 31 = if x.getLsbD 6 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm]; have h : (BitVec.signExtend 32 x <<< 25).getLsbD 31 = x.getLsbD 6 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl24_asr31 (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 24).sshiftRight 31 = if x.getLsbD 7 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm]; have h : (BitVec.signExtend 32 x <<< 24).getLsbD 31 = x.getLsbD 7 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl23_asr31 (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 23).sshiftRight 31 = if x.getLsbD 8 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm]; have h : (BitVec.signExtend 32 x <<< 23).getLsbD 31 = x.getLsbD 8 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl22_asr31 (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 22).sshiftRight 31 = if x.getLsbD 9 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm]; have h : (BitVec.signExtend 32 x <<< 22).getLsbD 31 = x.getLsbD 9 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl21_asr31 (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 21).sshiftRight 31 = if x.getLsbD 10 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm]; have h : (BitVec.signExtend 32 x <<< 21).getLsbD 31 = x.getLsbD 10 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl20_asr31 (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 20).sshiftRight 31 = if x.getLsbD 11 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm]; have h : (BitVec.signExtend 32 x <<< 20).getLsbD 31 = x.getLsbD 11 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl19_asr31 (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 19).sshiftRight 31 = if x.getLsbD 12 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm]; have h : (BitVec.signExtend 32 x <<< 19).getLsbD 31 = x.getLsbD 12 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl18_asr31 (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 18).sshiftRight 31 = if x.getLsbD 13 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm]; have h : (BitVec.signExtend 32 x <<< 18).getLsbD 31 = x.getLsbD 13 := by bv_bits
  rw [h]
@[local arm64_norm ↓, local wp_norm ↓] theorem sxth32_shl17_asr31 (x : BitVec 16) :
    (BitVec.signExtend 32 x <<< 17).sshiftRight 31 = if x.getLsbD 14 = true then 0xffffffff#32 else 0#32 := by
  rw [sshiftRight31_eq_ite_sm]; have h : (BitVec.signExtend 32 x <<< 17).getLsbD 31 = x.getLsbD 14 := by bv_bits
  rw [h]

@[local arm64_norm ↓, local wp_norm ↓]
theorem pmTerm_mid_sm (yv x : BitVec 16) (i : Nat) :
    (BitVec.zeroExtend 32 yv <<< i) &&& (if x.getLsbD i = true then 0xffffffff#32 else 0#32) =
      pmTerm_sm yv x i := rfl

private theorem sxth32_trunc16_sm (yv : BitVec 16) :
    BitVec.truncate 16 (BitVec.signExtend 32 yv) = yv := by bv_bits
private theorem sxth32_shr16_sm (yv : BitVec 16) :
    (BitVec.signExtend 32 yv) >>> 16 = if yv.getLsbD 15 then 0xffff#32 else 0#32 := by bv_bits
private theorem sxth33_trunc16_sm (yv : BitVec 16) :
    BitVec.truncate 16 (BitVec.signExtend 33 (BitVec.signExtend 32 yv)) = yv := by bv_bits
private theorem sxth33_shr16_sm (yv : BitVec 16) :
    (BitVec.signExtend 33 (BitVec.signExtend 32 yv)) >>> 16 =
      if yv.getLsbD 15 then 0x1ffff#33 else 0#33 := by bv_bits
private theorem yv_shr15_sm (yv : BitVec 16) :
    yv >>> 15 = if yv.getLsbD 15 then 1#16 else 0#16 := by bv_bits
private theorem beq_bne_self_sm (a b : Bool) : (b == (a != b)) = !a := by
  cases a <;> cases b <;> rfl

theorem adds_sxth_one_gt_sm (yv : BitVec 16) :
    ConditionHolds CondCode.GT (addsPState32 (BitVec.signExtend 32 yv) 1#32) = !yv.getLsbD 15 := by
  have hlo32 := congrArg BitVec.toNat (sxth32_trunc16_sm yv)
  have hhi32 := congrArg BitVec.toNat (sxth32_shr16_sm yv)
  have hlo33 := congrArg BitVec.toNat (sxth33_trunc16_sm yv)
  have hhi33 := congrArg BitVec.toNat (sxth33_shr16_sm yv)
  have hb15 := congrArg BitVec.toNat (yv_shr15_sm yv)
  rw [BitVec.toNat_setWidth] at hlo32 hlo33
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hhi32 hhi33 hb15
  have hlt16 : yv.toNat < 2 ^ 16 := yv.isLt
  have hlt32 : (BitVec.signExtend 32 yv).toNat < 2 ^ 32 := (BitVec.signExtend 32 yv).isLt
  have hlt33 : (BitVec.signExtend 33 (BitVec.signExtend 32 yv)).toNat < 2 ^ 33 :=
    (BitVec.signExtend 33 (BitVec.signExtend 32 yv)).isLt
  unfold ConditionHolds addsPState32 AddWithCarry32; dsimp only; rw [beq_bne_self_sm]
  cases hb : yv.getLsbD 15 <;>
    simp only [hb, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true] at hhi32 hhi33 hb15 ⊢
  · rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true', beq_eq_false_iff_ne]
    change (BitVec.signExtend 32 yv).toNat / 65536 = 0 at hhi32
    change (BitVec.signExtend 33 (BitVec.signExtend 32 yv)).toNat / 65536 = 0 at hhi33
    change yv.toNat / 32768 = 0 at hb15
    refine ⟨fun h => ?_, ?_⟩
    · have ht := congrArg BitVec.toNat h
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat] at ht; omega
    · rw [BitVec.msb_eq_false_iff_two_mul_lt]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have hs1 : (BitVec.signExtend 33 1#32).toNat = 1 := rfl
      rw [hs1]; omega
  · rw [Bool.and_eq_false_iff, Bool.not_eq_false', Bool.not_eq_false', beq_iff_eq]
    change (BitVec.signExtend 32 yv).toNat / 65536 = 65535 at hhi32
    change (BitVec.signExtend 33 (BitVec.signExtend 32 yv)).toNat / 65536 = 131071 at hhi33
    change yv.toNat / 32768 = 1 at hb15
    by_cases hy : yv.toNat = 65535
    · left; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · right; rw [BitVec.msb_eq_true_iff_two_mul_ge]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have hs1 : (BitVec.signExtend 33 1#32).toNat = 1 := rfl
      rw [hs1]; omega

@[local arm64_norm ↓, local wp_norm ↓]
theorem csel_gt_cmn1_sxth32_sm (yv x : BitVec 16) :
    (if ConditionHolds CondCode.GT (addsPState32 (BitVec.signExtend 32 x) 1#32) = true then 0#64
     else BitVec.truncate 64 (BitVec.zeroExtend 32 yv <<< 15)) =
      BitVec.zeroExtend 64 (pmTerm_sm yv x 15) := by
  dsimp only [pmTerm_sm]; rw [adds_sxth_one_gt_sm]; generalize x.getLsbD 15 = b; cases b <;> bv_slice

@[local arm64_norm ↓, local wp_norm ↓]
theorem csel_gt_cmn1_sxth32_zext_sm (yv x : BitVec 16) :
    (if ConditionHolds CondCode.GT (addsPState32 (BitVec.signExtend 32 x) 1#32) = true then 0#64
     else BitVec.zeroExtend 64 (BitVec.zeroExtend 32 yv <<< 15)) =
      BitVec.zeroExtend 64 (pmTerm_sm yv x 15) := by
  dsimp only [pmTerm_sm]; rw [adds_sxth_one_gt_sm]; generalize x.getLsbD 15 = b; cases b <;> bv_slice

private theorem ite_xor_eq_xor_and_mask_sm (b : Bool) (acc x : BitVec 32) :
    (if b = true then acc ^^^ x else acc) =
      acc ^^^ (x &&& (if b = true then 0xffff_ffff#32 else 0#32)) := by
  cases b <;> bv_slice

private theorem test_bit16_eq_getLsbD_sm (yv : BitVec 16) (i : Nat) (hi : i < 16) :
    (0#16 != yv &&& (1#16 <<< i)) = yv.getLsbD i := by
  match i, hi with
  | 0, _ => bv_slice | 1, _ => bv_slice | 2, _ => bv_slice | 3, _ => bv_slice
  | 4, _ => bv_slice | 5, _ => bv_slice | 6, _ => bv_slice | 7, _ => bv_slice
  | 8, _ => bv_slice | 9, _ => bv_slice | 10, _ => bv_slice | 11, _ => bv_slice
  | 12, _ => bv_slice | 13, _ => bv_slice | 14, _ => bv_slice | 15, _ => bv_slice
  | n + 16, hi => omega

private theorem pmTerm_rhs_0_sm (cv yv : BitVec 16) :
    (if (0#16 != yv &&& (1#16 <<< 0)) = true then BitVec.zeroExtend 32 cv <<< 0 else 0#32) =
      pmTerm_sm cv yv 0 := by
  dsimp only [pmTerm_sm]; rw [test_bit16_eq_getLsbD_sm yv 0 (by decide)]
  generalize yv.getLsbD 0 = b; cases b <;> bv_slice

private theorem pmTerm_rhs_sm (cv yv : BitVec 16) (i : Nat) (hi : i < 16) :
    (BitVec.zeroExtend 32 cv <<< i) &&&
      (if (0#16 != yv &&& (1#16 <<< i)) = true then 0xffff_ffff#32 else 0#32) =
      pmTerm_sm cv yv i := by
  dsimp only [pmTerm_sm]; rw [test_bit16_eq_getLsbD_sm yv i hi]

attribute [local irreducible] pmTerm_sm in
theorem unaccelerated_polyMul_eq_pmTerms_sm (cv yv : BitVec 16) :
    unaccelerated.polyMul cv yv =
      pmTerm_sm cv yv 0 ^^^ pmTerm_sm cv yv 1 ^^^ pmTerm_sm cv yv 2 ^^^ pmTerm_sm cv yv 3 ^^^
      pmTerm_sm cv yv 4 ^^^ pmTerm_sm cv yv 5 ^^^ pmTerm_sm cv yv 6 ^^^ pmTerm_sm cv yv 7 ^^^
      pmTerm_sm cv yv 8 ^^^ pmTerm_sm cv yv 9 ^^^ pmTerm_sm cv yv 10 ^^^ pmTerm_sm cv yv 11 ^^^
      pmTerm_sm cv yv 12 ^^^ pmTerm_sm cv yv 13 ^^^ pmTerm_sm cv yv 14 ^^^ pmTerm_sm cv yv 15 := by
  simp only [unaccelerated.polyMul, unaccelerated.polyMulLoop,
    ite_xor_eq_xor_and_mask_sm, Nat.reduceAdd, BitVec.zero_xor,
    pmTerm_rhs_0_sm cv yv, pmTerm_rhs_sm cv yv 1 (by decide),
    pmTerm_rhs_sm cv yv 2 (by decide), pmTerm_rhs_sm cv yv 3 (by decide),
    pmTerm_rhs_sm cv yv 4 (by decide), pmTerm_rhs_sm cv yv 5 (by decide),
    pmTerm_rhs_sm cv yv 6 (by decide), pmTerm_rhs_sm cv yv 7 (by decide),
    pmTerm_rhs_sm cv yv 8 (by decide), pmTerm_rhs_sm cv yv 9 (by decide),
    pmTerm_rhs_sm cv yv 10 (by decide), pmTerm_rhs_sm cv yv 11 (by decide),
    pmTerm_rhs_sm cv yv 12 (by decide), pmTerm_rhs_sm cv yv 13 (by decide),
    pmTerm_rhs_sm cv yv 14 (by decide), pmTerm_rhs_sm cv yv 15 (by decide)]

attribute [irreducible] pmTerm_sm

@[local arm64_norm ↓, local wp_norm ↓]
theorem polyMul_pair_c1_eq (yv x : BitVec 16) :
    (((pmTerm_sm yv x 0 ^^^ pmTerm_sm yv x 15 ^^^ pmTerm_sm yv x 1 ^^^
        (pmTerm_sm yv x 2 ^^^ pmTerm_sm yv x 3)) ^^^
       (pmTerm_sm yv x 4 ^^^ pmTerm_sm yv x 5 ^^^ pmTerm_sm yv x 6)) ^^^
      ((pmTerm_sm yv x 7 ^^^ pmTerm_sm yv x 8 ^^^ pmTerm_sm yv x 9) ^^^
       pmTerm_sm yv x 10)) ^^^
     (((pmTerm_sm yv x 11 ^^^ pmTerm_sm yv x 12) ^^^ pmTerm_sm yv x 13) ^^^
      pmTerm_sm yv x 14) =
      unaccelerated.polyMul yv x := by
  rw [unaccelerated_polyMul_eq_pmTerms_sm]; ac_rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem polyMul_pair_c2_eq (yv x : BitVec 16) :
    ((((pmTerm_sm yv x 0 ^^^ pmTerm_sm yv x 15) ^^^ pmTerm_sm yv x 1) ^^^
       (pmTerm_sm yv x 2 ^^^ pmTerm_sm yv x 3)) ^^^
      ((pmTerm_sm yv x 4 ^^^ pmTerm_sm yv x 5) ^^^ pmTerm_sm yv x 6)) ^^^
     (((pmTerm_sm yv x 7 ^^^ pmTerm_sm yv x 8) ^^^ pmTerm_sm yv x 9) ^^^
      pmTerm_sm yv x 10) ^^^
     ((((pmTerm_sm yv x 11 ^^^ pmTerm_sm yv x 12) ^^^ pmTerm_sm yv x 13) ^^^
       pmTerm_sm yv x 14)) =
      unaccelerated.polyMul yv x := by
  rw [unaccelerated_polyMul_eq_pmTerms_sm]; ac_rfl

/-! ## 5. Precomputed Shift-Table Setup (`0x6ae44..0x6aec0`, `+2752 -> +3384`) -/

theorem shiftTableInit_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (hb : b &&& 0xfff#64 = 0#64) (n : Nat) (yv : BitVec 16)
    (s : State) (fsp clonePtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u112 u136 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2752#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 n)
    (hx21 : s.readReg64 .x21 = BitVec.zeroExtend 64 yv)
    (hx22 : s.readReg64 .x22 = clonePtr)
    (hcont : ∀ s1 : State,
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3384#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x18 = b + bv% (ls_xref% 0x5e970 0x5e974) →
      s1.readReg64 .x20 = BitVec.ofNat 64 n →
      s1.readReg64 .x21 = BitVec.zeroExtend 64 yv →
      s1.readReg64 .x22 = clonePtr →
      s1.readReg64 .x24 = clonePtr →
      s1.readReg64 .x26 = 2#64 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.readReg64 .x30 = s.readReg64 .x30 →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (shiftTableAt fsp yv ∗ ((fsp + 112#64) ↦₆₄ clonePtr) ∗
         ((fsp + 136#64) ↦₆₄ BitVec.ofNat 64 n) ∗ Frame) post) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (shiftSlotsRawAt fsp ∗ ((fsp + 112#64) ↦₆₄ u112) ∗
       ((fsp + 136#64) ↦₆₄ u136) ∗ Frame) post := by
  have hadrp := fnAddr_adrp_6ae54 (H := Rust.withPanics ext) hb
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xac0 128
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hadrp hpc hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  unfold shiftSlotsRawAt
  apply sepWP_exists_left_sep; intro d148; apply sepWP_exists_left_sep; intro d152
  apply sepWP_exists_left_sep; intro d156; apply sepWP_exists_left_sep; intro d160
  apply sepWP_exists_left_sep; intro d164; apply sepWP_exists_left_sep; intro d168
  apply sepWP_exists_left_sep; intro d172; apply sepWP_exists_left_sep; intro d176
  apply sepWP_exists_left_sep; intro d180; apply sepWP_exists_left_sep; intro d184
  apply sepWP_exists_left_sep; intro d192; apply sepWP_exists_left_sep; intro d200
  apply sepWP_exists_left_sep; intro d208; apply sepWP_exists_left_sep; intro d216
  apply sepWP_exists_left_sep; intro d224
  wp_steps
  unfold shiftTableAt at hcont; dsimp only at hcont
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont _ (by wp_norm_goal) (by wp_norm_lhs) (by simp only [wp_norm, hsp])
      (by simp only [arm64_norm, wp_norm]) rfl (by simp only [wp_norm, hadrp])
      (by simp only [wp_norm, hx20]) (by simp only [wp_norm, hx21])
      (by simp only [wp_norm, hx22]) (by simp only [wp_norm, hx22])
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs))

/-! ## 6. Odd Trailing Element (`0x6b19c..0x6b248`, `+3608 -> +3784`) -/

theorem nextChunk_unacceleratedMul_addr (b : BitVec 64) (H : String → Option (State → State)) :
    (libsignalSessionCode.rebase b H).fnAddr polyNextChunkName + 18446744073709525280#64 =
      (libsignalSessionCode.rebase b H).fnAddr unacceleratedMulName := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, polyNextChunk_fnOff, unacceleratedMul_fnOff]
  bv_omega

theorem parallelMultOddTail_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (hb : b &&& 0xfff#64 = 0#64)
    (idx : Nat) (yv : BitVec 16) (last : GF16) (hidx_lt : 2 * idx < 2 ^ 63)
    (s : State) (fsp clonePtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3608#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 idx)
    (hx21 : s.readReg64 .x21 = BitVec.zeroExtend 64 yv)
    (hx22 : s.readReg64 .x22 = clonePtr)
    (hcont : ∀ s1 : State,
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3784#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x22 = clonePtr →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (gf16At ⟨unaccelerated.mul last.value yv⟩ (clonePtr + BitVec.ofNat 64 (2 * idx)) ∗
         tokenInitAt b ∗ reduceTableAt b ∗ Frame) post) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (gf16At last (clonePtr + BitVec.ofNat 64 (2 * idx)) ∗
       tokenInitAt b ∗ reduceTableAt b ∗ Frame) post := by
  have hmul : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName +
        18446744073709525280#64)
      (unacceleratedMulSpec b) := by
    rw [nextChunk_unacceleratedMul_addr]; exact unacceleratedMul_ok b ext
  have hadrp1 := fnAddr_adrp_6b19c (H := Rust.withPanics ext) hb
  have hadrp2 := fnAddr_adrp_6b1ac (H := Rust.withPanics ext) hb
  have halign := GF.Mul2U16.aligned_86bd8 b hb
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xe18 176
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hmul hadrp1 hadrp2 hpc hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  have hlsl : BitVec.ofNat 64 idx <<< 1 = BitVec.ofNat 64 (2 * idx) := shl_one_ofNat_eq_nat idx
  unfold gf16At tokenInitAt
  wp_steps 2
  apply step_ldar32
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_assumption
  · wp_norm_lhs
  · wp_norm_lhs
  · exact halign
  · wp_sep_access
  · wp_norm_lhs
  wp_steps 8
  wp_apply
  wp_steps 1
  unfold gf16At tokenInitAt at hcont; dsimp only at hcont
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont _ (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [wp_norm, ‹sf.sp = _›, hsp])
      (by simp only [arm64_norm, wp_norm, hpost])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [wp_norm, h_1]) (by simp only [wp_norm, h_3, hx22])
      (by simp only [wp_norm, h_5]) (by simp only [wp_norm, h_6])
      (by simp only [wp_norm, h_7]) (by simp only [wp_norm, h_8])
      (by simp only [wp_norm, h_9]) (by simp only [wp_norm, hcs_sf]))

end CryptoVerification.SpqrV1.Poly.NextChunk
