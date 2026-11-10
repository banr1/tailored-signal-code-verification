/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDecodes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyDecoder>::from_pb`: Inner Binary-Search and Insertion Steps

**Checked by Lean.**

Proves the inner binary-search loop (`+456..+492`), `memmove` insertion (`+532..+296`),
`bsearchReplace` (`+432..+296`), and single-point `bsearchPush` (`+320..+296`) for
`<PolyDecoder>::from_pb` (`0x62b1c`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.L37a
open Lean Elab Tactic ProofLib ProofLib.ProgramReflection CryptoVerification.SpqrV1.Poly.DecoderPb in
elab "from_pb_fetches_range " b:term:max H:term:max k0:num len:num : tactic => do
  let off ← ProofLib.CodeLookup.lookupOff ``CryptoVerification.libsignalSessionCode "<spqr::encoding::polynomial::PolyDecoder>::from_pb"
  let offLit := Syntax.mkNumLit (toString off.val)
  evalTactic (← `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode spqrDecoderFromPbBin $b $H decoderFromPb_fnOff $offLit $k0 $len))
end CryptoVerification.SpqrV1.Layout.L37a

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L37a

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## BitVector and Frame-Pointer Address Normalization Helpers -/

@[simp, local arm64_norm, local wp_norm]
theorem fp_add_448_sub_32 (fsp : BitVec 64) :
    fsp + 448#64 + 18446744073709551584#64 = fsp + 416#64 := by bv_omega

@[simp, local arm64_norm, local wp_norm]
theorem fp_add_448_sub_32_int (fsp : BitVec 64) :
    fsp + 448#64 + BitVec.ofInt 64 (-32) = fsp + 416#64 := by bv_omega

@[simp, local arm64_norm, local wp_norm]
theorem fp_add_448_sub_24 (fsp : BitVec 64) :
    fsp + 448#64 + 18446744073709551592#64 = fsp + 416#64 + 8#64 := by bv_omega

@[simp, local arm64_norm, local wp_norm]
theorem fp_add_448_sub_24_int (fsp : BitVec 64) :
    fsp + 448#64 + BitVec.ofInt 64 (-24) = fsp + 416#64 + 8#64 := by bv_omega

@[simp, local arm64_norm, local wp_norm]
theorem fp_add_448_sub_16 (fsp : BitVec 64) :
    fsp + 448#64 + 18446744073709551600#64 = fsp + 416#64 + 16#64 := by bv_omega

@[simp, local arm64_norm, local wp_norm]
theorem fp_add_448_sub_16_int (fsp : BitVec 64) :
    fsp + 448#64 + BitVec.ofInt 64 (-16) = fsp + 416#64 + 16#64 := by bv_omega

@[simp, local arm64_norm, local wp_norm]
theorem truncate16_truncate32 (x : BitVec 64) :
    BitVec.truncate 16 (BitVec.truncate 32 x) = BitVec.truncate 16 x := by
  bv_bits

@[simp, local arm64_norm, local wp_norm]
theorem and_ffff_truncate32 (x : BitVec 64) :
    (BitVec.truncate 32 x) &&& 65535#32 = (BitVec.truncate 16 x).zeroExtend 32 := by
  bv_bits

@[simp, local arm64_norm, local wp_norm]
theorem and_ffff_zeroExtend64_truncate32 (x : BitVec 64) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x) &&& 65535#64) =
      (BitVec.truncate 16 x).zeroExtend 32 := by
  bv_bits

theorem uxth32_of_truncate16_64 {x : BitVec 64} {v : BitVec 16}
    (h : BitVec.truncate 16 x = v) :
    BitVec.zeroExtend 32 (BitVec.truncate 16 (BitVec.truncate 32 x)) = v.zeroExtend 32 := by
  rw [← h]
  bv_bits

theorem and_ffff_of_truncate16_64 {x : BitVec 64} {v : BitVec 16}
    (h : BitVec.truncate 16 x = v) :
    (BitVec.truncate 32 x) &&& 65535#32 = v.zeroExtend 32 := by
  rw [← h]
  bv_bits

theorem truncate16_32_of_truncate16_64 {x : BitVec 64} {v : BitVec 16}
    (h : BitVec.truncate 16 x = v) :
    BitVec.truncate 16 (BitVec.truncate 32 x) = v := by
  rw [← h]
  bv_bits

/-- Temporary `SortedSet<Pt>` at `fsp + 416` (`x29 - 32`) with fixed `cap` and `ptr`. -/
def tempVecPtAt (A : RustAlloc) (fsp cap ptr : BitVec 64) (s : SortedSetPt) : SepProp :=
  ((fsp + 416#64) ↦₆₄ cap) ∗
  ((fsp + 416#64 + 8#64) ↦₆₄ ptr) ∗
  ((fsp + 416#64 + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
  A.live ptr (cap.toNat * 4) 2 ∗
  ptSliceAt ptr s.vec ∗
  memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4)

theorem tempVecPtAt_prepare_memmove (A : RustAlloc) (fsp cap ptr : BitVec 64)
    (vec : List Pt) (insertIdx : Nat)
    (hins : insertIdx < vec.length) (hlt : vec.length < cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63) :
    tempVecPtAt A fsp cap ptr { vec := vec } ⊢
      ∃∗ slotBs : List (BitVec 8),
        ⌜slotBs.length = 4⌝ ∗
        ptSliceAt ptr (vec.take insertIdx) ∗
        ((ptr + BitVec.ofNat 64 (4 * insertIdx)) ↦ₛ (ptListBytes (vec.drop insertIdx) ++ slotBs)) ∗
        memRegion (ptr + BitVec.ofNat 64 ((vec.length + 1) * 4)) ((cap.toNat - (vec.length + 1)) * 4) ∗
        ((fsp + 416#64) ↦₆₄ cap) ∗ ((fsp + 416#64 + 8#64) ↦₆₄ ptr) ∗
        ((fsp + 416#64 + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
        A.live ptr (cap.toNat * 4) 2 := by
  unfold tempVecPtAt
  dsimp only
  have hprep := insert_suffix_prepare_memmove ptr vec insertIdx cap.toNat hins hlt hcap
  rw [show ((fsp + 416#64) ↦₆₄ cap) ∗ ((fsp + 416#64 + 8#64) ↦₆₄ ptr) ∗
      ((fsp + 416#64 + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
      A.live ptr (cap.toNat * 4) 2 ∗
      ptSliceAt ptr vec ∗
      memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4) =
    (ptSliceAt ptr vec ∗
      memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4)) ∗
    (((fsp + 416#64) ↦₆₄ cap) ∗ ((fsp + 416#64 + 8#64) ↦₆₄ ptr) ∗
      ((fsp + 416#64 + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
      A.live ptr (cap.toNat * 4) 2) by ac_rfl]
  refine Entails.trans (sepConj_mono_left hprep) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro slotBs
  refine Entails.sepExists_right slotBs (Entails.of_eq (by ac_rfl))

theorem reassemble_tempVecPtAt_insert (A : RustAlloc) (fsp cap ptr : BitVec 64)
    (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx ≤ vec.length) :
    (((ptr + BitVec.ofNat 64 (4 * insertIdx)) ↦₁₆ pt.x.value) ∗
      ((ptr + BitVec.ofNat 64 (4 * insertIdx) + 2#64) ↦₁₆ pt.y.value) ∗
      ptSliceAt (ptr + BitVec.ofNat 64 (4 * insertIdx) + 4#64) (vec.drop insertIdx) ∗
      ptSliceAt ptr (vec.take insertIdx) ∗
      memRegion (ptr + BitVec.ofNat 64 ((vec.length + 1) * 4)) ((cap.toNat - (vec.length + 1)) * 4) ∗
      ((fsp + 416#64) ↦₆₄ cap) ∗
      ((fsp + 416#64 + 8#64) ↦₆₄ ptr) ∗
      ((fsp + 416#64 + 16#64) ↦₆₄ BitVec.ofNat 64 (vec.length + 1)) ∗
      A.live ptr (cap.toNat * 4) 2) ⊢
      tempVecPtAt A fsp cap ptr { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } := by
  let vec' := vec.take insertIdx ++ (pt :: vec.drop insertIdx)
  have hlen' : vec'.length = vec.length + 1 := by
    dsimp [vec']
    rw [List.length_append, List.length_take_of_le hins, List.length_cons, List.length_drop]
    omega
  have hslice := ptSliceAt_reassemble_insert ptr vec insertIdx pt hins
  dsimp only at hslice
  unfold tempVecPtAt
  dsimp only
  rw [← hlen', ← hslice]
  exact Entails.of_eq (by ac_rfl)

theorem reassemble_tempVecPtAt_snoc (A : RustAlloc) (fsp cap ptr : BitVec 64)
    (vec : List Pt) (pt : Pt) :
    (ptSliceAt ptr vec ∗
      ((ptr + BitVec.ofNat 64 (4 * vec.length)) ↦₁₆ pt.x.value) ∗
      ((ptr + BitVec.ofNat 64 (4 * vec.length) + 2#64) ↦₁₆ pt.y.value) ∗
      memRegion (ptr + BitVec.ofNat 64 ((vec.length + 1) * 4)) ((cap.toNat - (vec.length + 1)) * 4) ∗
      ((fsp + 416#64) ↦₆₄ cap) ∗
      ((fsp + 416#64 + 8#64) ↦₆₄ ptr) ∗
      ((fsp + 416#64 + 16#64) ↦₆₄ BitVec.ofNat 64 (vec.length + 1)) ∗
      A.live ptr (cap.toNat * 4) 2) ⊢
      tempVecPtAt A fsp cap ptr { vec := vec ++ [pt] } := by
  let vec' := vec ++ [pt]
  have hlen' : vec'.length = vec.length + 1 := by simp [vec']
  have hslice : ptSliceAt ptr vec' =
      ptSliceAt ptr vec ∗
        (((ptr + BitVec.ofNat 64 (4 * vec.length)) ↦₁₆ pt.x.value) ∗
          ((ptr + BitVec.ofNat 64 (4 * vec.length) + 2#64) ↦₁₆ pt.y.value)) := by
    dsimp [vec']
    rw [ptSliceAt_append_singleton]
    rfl
  unfold tempVecPtAt
  dsimp only
  rw [← hlen', hslice]
  exact Entails.of_eq (by ac_rfl)

theorem reassemble_tempVecPtAt_set (A : RustAlloc) (fsp cap ptr : BitVec 64)
    (vec : List Pt) (idx : Nat) (pt : Pt) (hidx : idx < vec.length) :
    (ptSliceAt ptr (vec.take idx) ∗
      ((ptr + BitVec.ofNat 64 (4 * idx)) ↦₁₆ pt.x.value) ∗
      ((ptr + BitVec.ofNat 64 (4 * idx) + 2#64) ↦₁₆ pt.y.value) ∗
      ptSliceAt (ptr + BitVec.ofNat 64 (4 * (idx + 1))) (vec.drop (idx + 1)) ∗
      memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4) ∗
      ((fsp + 416#64) ↦₆₄ cap) ∗
      ((fsp + 416#64 + 8#64) ↦₆₄ ptr) ∗
      ((fsp + 416#64 + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
      A.live ptr (cap.toNat * 4) 2) ⊢
      tempVecPtAt A fsp cap ptr { vec := vec.set idx pt } := by
  let vec' := vec.set idx pt
  have hlen' : vec'.length = vec.length := List.length_set
  have hslice : ptSliceAt ptr vec' =
      ptSliceAt ptr (vec.take idx) ∗
        (((ptr + BitVec.ofNat 64 (4 * idx)) ↦₁₆ pt.x.value) ∗
          ((ptr + BitVec.ofNat 64 (4 * idx) + 2#64) ↦₁₆ pt.y.value)) ∗
        ptSliceAt (ptr + BitVec.ofNat 64 (4 * (idx + 1))) (vec.drop (idx + 1)) := by
    dsimp [vec']
    rw [ptSliceAt_set vec idx pt ptr hidx]
    rfl
  unfold tempVecPtAt
  dsimp only
  rw [← hlen', hslice]
  exact Entails.of_eq (by ac_rfl)

/-! ## Inner Binary Search Loop (`0x62ce4..0x62d08`, `+456 -> +492`) -/

/-- Symbolic execution of the binary search loop (`0x62ce4..0x62d08`, `entry + 456#64` to `entry + 492#64`). -/
theorem fromPb_bsearchLoop_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    {target_pc : BitVec 64}
    (vec : List Pt) (ptr : BitVec 64) (xVal : BitVec 16)
    (hlen_bound : 4 * vec.length < 2 ^ 64) :
    ∀ (size base : Nat) (s : State) (P : SepProp) (post : State → SepProp → Prop),
      1 < size →
      base + size ≤ vec.length →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 456#64 →
      s.status = .Running →
      s.readReg64 .x22 = ptr →
      s.readReg64 .x8 = BitVec.ofNat 64 base →
      s.readReg64 .x9 = BitVec.ofNat 64 size →
      BitVec.truncate 16 (s.readReg64 .x27) = xVal →
      (∀ (sf : State),
        sf.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 492#64 →
        sf.status = .Running →
        sf.sp = s.sp →
        sf.trace = s.trace →
        sf.readReg64 .x22 = ptr →
        sf.readReg64 .x8 = BitVec.ofNat 64 (bsearchLoop vec xVal base size) →
        sf.readReg64 .x19 = s.readReg64 .x19 →
        sf.readReg64 .x20 = s.readReg64 .x20 →
        sf.readReg64 .x21 = s.readReg64 .x21 →
        sf.readReg64 .x24 = s.readReg64 .x24 →
        sf.readReg64 .x25 = s.readReg64 .x25 →
        sf.readReg64 .x26 = s.readReg64 .x26 →
        sf.readReg64 .x27 = s.readReg64 .x27 →
        sf.readReg64 .x28 = s.readReg64 .x28 →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP (tripleRatchetProgAtExt b ext) target_pc sf (ptSliceAt ptr vec ∗ P) post) →
      SepWP (tripleRatchetProgAtExt b ext) target_pc s (ptSliceAt ptr vec ∗ P) post := by
  from_pb_fetches_range b (Rust.withPanics ext) 456 36
  dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat]
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro base s P post hgt hle hpc hstat hx22 hx8 hx9 hx27 hcont
    have hhalf_pos : 0 < size / 2 := Nat.div_pos (by omega) (by decide)
    have hmid_lt : base + size / 2 < vec.length := by omega
    have hsize_lt64 : size < 2 ^ 64 := by omega
    have hlsr : (BitVec.ofNat 64 size) >>> 1 = BitVec.ofNat 64 (size / 2) :=
      bv64_lsr1_ofNat hsize_lt64
    have hadd_mid : BitVec.ofNat 64 (size / 2) + BitVec.ofNat 64 base =
        BitVec.ofNat 64 (base + size / 2) := by
      rw [← BitVec.ofNat_add, Nat.add_comm]
    have hsub_size : BitVec.ofNat 64 size - BitVec.ofNat 64 (size / 2) =
        BitVec.ofNat 64 (size - size / 2) :=
      bv64_sub_ofNat (by omega) hsize_lt64
    have hlsl_mid : (BitVec.ofNat 64 (base + size / 2)) <<< 2 =
        BitVec.ofNat 64 (4 * (base + size / 2)) :=
      bv64_lsl2_ofNat (by omega)
    have hmid_get : vec[base + size / 2]?.getD default = vec[base + size / 2]'hmid_lt := by
      rw [List.getElem?_eq_getElem hmid_lt, Option.getD_some]
    let base' := if xVal.toNat < (vec[base + size / 2]'hmid_lt).x.value.toNat then base else base + size / 2
    have huxth : BitVec.zeroExtend 32 (BitVec.truncate 16 (s.readReg32 .x27)) = xVal.zeroExtend 32 := by
      unfold State.readReg32
      exact uxth32_of_truncate16_64 hx27
    have hcsel :
        (if (BitVec.zeroExtend 32 xVal).ult
            (BitVec.zeroExtend 32 (vec[base + size / 2]'hmid_lt).x.value) = true then
          BitVec.ofNat 64 base
        else BitVec.ofNat 64 (base + size / 2)) = BitVec.ofNat 64 base' := by
      rw [bv32_ult_zeroExtend16]
      by_cases hlt : xVal.toNat < (vec[base + size / 2]'hmid_lt).x.value.toNat <;> simp [base', hlt]
    have hfold_slice :
        ((ptSliceAt ptr (List.take (base + size / 2) vec) ∗
          ((ptr + BitVec.ofNat 64 (4 * (base + size / 2))) ↦₁₆ (vec[base + size / 2]'hmid_lt).x.value ∗
            (ptr + BitVec.ofNat 64 (4 * (base + size / 2)) + 2#64) ↦₁₆ (vec[base + size / 2]'hmid_lt).y.value) ∗
          ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + size / 2 + 1))) (List.drop (base + size / 2 + 1) vec)) ∗
          P) = (ptSliceAt ptr vec ∗ P) := by
      change ((ptSliceAt ptr (List.take (base + size / 2) vec) ∗
        ptAt (vec[base + size / 2]'hmid_lt) (ptr + BitVec.ofNat 64 (4 * (base + size / 2))) ∗
        ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + size / 2 + 1))) (List.drop (base + size / 2 + 1) vec)) ∗
        P) = (ptSliceAt ptr vec ∗ P)
      rw [← ptSliceAt_focus vec (base + size / 2) ptr hmid_lt]
    rw [ptSliceAt_focus vec (base + size / 2) ptr hmid_lt]
    unfold ptAt
    wp_steps
    rw [hfold_slice, bv64_ult_one_ofNat (by omega)]
    have hbs_step : bsearchLoop vec xVal base size = bsearchLoop vec xVal base' (size - size / 2) := by
      conv_lhs => rw [bsearchLoop]
      simp only [hgt, ↓reduceDIte, hmid_get]
      rfl
    by_cases hgt' : 1 < size - size / 2
    · simp only [hgt', decide_true, ↓reduceIte]
      refine ih (size - size / 2) (by omega) base' _ P post hgt' (by dsimp [base']; split_ifs <;> omega)
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hstat])
        (by simp [wp_norm, arm64_norm, hx22])
        (by simp [wp_norm, arm64_norm, huxth, hcsel])
        (by simp [wp_norm, arm64_norm])
        (by simpa [wp_norm, arm64_norm] using hx27)
        (fun sf hpc_f hstat_f hsp_f htr_f hx22_f hx8_f hx19_f hx20_f hx21_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hvregs_f => ?_)
      apply hcont sf hpc_f hstat_f
      · simpa [wp_norm, arm64_norm] using hsp_f
      · simpa [wp_norm, arm64_norm] using htr_f
      · exact hx22_f
      · rw [hbs_step]; exact hx8_f
      · simpa [wp_norm, arm64_norm] using hx19_f
      · simpa [wp_norm, arm64_norm] using hx20_f
      · simpa [wp_norm, arm64_norm] using hx21_f
      · simpa [wp_norm, arm64_norm] using hx24_f
      · simpa [wp_norm, arm64_norm] using hx25_f
      · simpa [wp_norm, arm64_norm] using hx26_f
      · simpa [wp_norm, arm64_norm] using hx27_f
      · simpa [wp_norm, arm64_norm] using hx28_f
      · simpa [wp_norm, arm64_norm] using hx29_f
      · simpa [wp_norm, arm64_norm] using hvregs_f
    · simp only [hgt', decide_false, Bool.false_eq_true, ↓reduceIte]
      have hbs_done : bsearchLoop vec xVal base size = base' := by
        rw [hbs_step, bsearchLoop]
        simp [hgt']
      apply hcont
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hstat]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hx22]
      · rw [hbs_done]; simp [wp_norm, arm64_norm, huxth, hcsel]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]

/-- Symbolic execution of `0x62ccc..0x62d08` (`entry + 432#64` to `entry + 492#64`):
    handles both `vec.length = 1` and `1 < vec.length`, producing
    `x8 = BitVec.ofNat 64 (bsearchLoop vec xVal 0 vec.length)`. -/
theorem fromPb_bsearch_to_492_sepWP {b : BitVec 64} {ext : String → Option (State → State)}
    {target_pc ptr : BitVec 64} {vec : List Pt} {xVal : BitVec 16}
    (h1 : 1 ≤ vec.length) (hlen : vec.length < 2 ^ 62)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 432#64)
    (hstat : s.status = .Running)
    (hx22 : s.readReg64 .x22 = ptr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 vec.length)
    (hx27 : BitVec.truncate 16 (s.readReg64 .x27) = xVal)
    (hcont : ∀ (sf : State),
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 492#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x22 = ptr →
      sf.readReg64 .x8 = BitVec.ofNat 64 (bsearchLoop vec xVal 0 vec.length) →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt b ext) target_pc sf (ptSliceAt ptr vec ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc s (ptSliceAt ptr vec ∗ P) post := by
  have hloop := @fromPb_bsearchLoop_sepWP b ext target_pc vec ptr xVal (by omega)
  from_pb_fetches_range b (Rust.withPanics ext) 432 24
  dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hloop hpc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  wp_steps 2
  rw [bv64_bne_one_ofNat (by omega)]
  by_cases heq1 : vec.length = 1
  · simp only [heq1, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_steps 2
    have hbs1 : bsearchLoop vec xVal 0 vec.length = 0 := by
      rw [heq1, bsearchLoop]; simp
    apply hcont
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hstat]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hx22]
    · simp [wp_norm, arm64_norm, hbs1]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
  · simp only [heq1, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    wp_steps 2
    refine hloop vec.length 0 _ P post (by omega) (by omega)
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hstat])
      (by simp [wp_norm, arm64_norm, hx22])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx26])
      (by simpa [wp_norm, arm64_norm] using hx27)
      (fun sf hpc_f hstat_f hsp_f htr_f hx22_f hx8_f hx19_f hx20_f hx21_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hvregs_f => ?_)
    apply hcont sf hpc_f hstat_f
    · simpa [wp_norm, arm64_norm] using hsp_f
    · simpa [wp_norm, arm64_norm] using htr_f
    · exact hx22_f
    · exact hx8_f
    · simpa [wp_norm, arm64_norm] using hx19_f
    · simpa [wp_norm, arm64_norm] using hx20_f
    · simpa [wp_norm, arm64_norm] using hx21_f
    · simpa [wp_norm, arm64_norm] using hx24_f
    · simpa [wp_norm, arm64_norm] using hx25_f
    · simpa [wp_norm, arm64_norm] using hx26_f
    · simpa [wp_norm, arm64_norm] using hx27_f
    · simpa [wp_norm, arm64_norm] using hx28_f
    · simpa [wp_norm, arm64_norm] using hx29_f
    · simpa [wp_norm, arm64_norm] using hvregs_f

/-! ## Binary Search Insertion (`0x62d30..0x62d60`, `+532 -> +296`) and `bsearchReplace` (`+432 -> +296`) -/

/-- Symbolic execution of `0x62d3c..0x62d60` (`entry + 544#64` to `entry + 296#64`):
    calls `memmove(x23 + 4, x23, 4 * (len - insertIdx))`, increments `x26`, stores `pt` at `x23`,
    restores `w19 = 1`, and stores `len + 1` at `[x29 - 16]`. -/
theorem fromPb_bsearch_memmove_insert_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64} (hA : AllocContracts b A ext)
    (fsp cap ptr : BitVec 64) (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx < vec.length) (hlt : vec.length < cap.toNat)
    (hcap : cap.toNat * 4 < 2 ^ 63)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 544#64)
    (hstat : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (vec.length - insertIdx))
    (hx20 : s.readReg64 .x20 = pt.y.value.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = ptr)
    (hx23 : s.readReg64 .x23 = ptr + BitVec.ofNat 64 (4 * insertIdx))
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 vec.length)
    (hx27 : BitVec.truncate 16 (s.readReg64 .x27) = pt.x.value)
    (hx29 : s.readReg64 .x29 = fsp + 448#64)
    (hcont : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 296#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x19 = 1#64 →
      sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x22 = ptr →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = BitVec.ofNat 64 (vec.length + 1) →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = fsp + 448#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt b ext) target_pc sf
        (tempVecPtAt A fsp cap ptr { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗
          stackAt s.sp 0 ∗ P)
        post) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc s
      (tempVecPtAt A fsp cap ptr { vec := vec } ∗ stackAt s.sp 0 ∗ P)
      post := by
  have hmemmove := hA.session_memmove_ok_at fromPbDecName (num% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder>::from_pb" "memmove")) 0
    (by rw [decoderFromPb_fnOff]; simp only [arm64_norm])
  from_pb_fetches_range b (Rust.withPanics ext) 544 40
  dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hmemmove hpc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  refine SepWP.weaken_pre (sepConj_mono_left (tempVecPtAt_prepare_memmove A fsp cap ptr vec insertIdx hins hlt hcap)) ?_
  rw [sepExists_sepConj_left]
  apply SepWP.exists_left; intro slotBs
  simp only [sepConj_assoc]
  apply SepWP.focus_pure (by sep_focus)
  intro hslot
  have hlsl_rem : (BitVec.ofNat 64 (vec.length - insertIdx)) <<< 2 =
      BitVec.ofNat 64 (4 * (vec.length - insertIdx)) :=
    bv64_lsl2_ofNat (by omega)
  have htoNat_rem : (BitVec.ofNat 64 (4 * (vec.length - insertIdx))).toNat =
      4 * (vec.length - insertIdx) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbuf_len : (ptListBytes (vec.drop insertIdx) ++ slotBs).length =
      4 * (vec.length - insertIdx) + 4 := by
    rw [List.length_append, ptListBytes_length, List.length_drop, hslot]
  wp_steps 4
  wp_call hmemmove (ptr + BitVec.ofNat 64 (4 * insertIdx),
    ptListBytes (vec.drop insertIdx) ++ slotBs, 4, 0, 4 * (vec.length - insertIdx))
  have hmove_pt := pointsToBytes_listMove_insert_pt (ptr + BitVec.ofNat 64 (4 * insertIdx))
    (vec.drop insertIdx) hslot
  rw [List.length_drop] at hmove_pt
  refine SepWP.weaken_pre (sepConj_mono_left hmove_pt) ?_
  wp_pull_exists
  wp_steps 6
  have hreasm := reassemble_tempVecPtAt_insert A fsp cap ptr vec insertIdx pt (by omega)
  refine SepWP.weaken_pre
    (P' := tempVecPtAt A fsp cap ptr { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗
      stackAt s.sp 0 ∗ P)
    (by refine Entails.trans ?_ (sepConj_mono_left hreasm)
        exact Entails.of_eq (by ac_rfl)) ?_
  have hbv_len' : BitVec.ofNat 64 vec.length + 1#64 = BitVec.ofNat 64 (vec.length + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  apply hcont <;> simp [wp_norm, arm64_norm, hbv_len', *]

/-- Symbolic execution of `0x62d4c..0x62d60` (`entry + 560#64` to `entry + 296#64`)
    when `insertIdx = vec.length`. -/
theorem fromPb_bsearch_end_insert_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (fsp cap ptr : BitVec 64) (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx = vec.length) (hlt : vec.length < cap.toNat)
    (hcap : cap.toNat * 4 < 2 ^ 63)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 560#64)
    (hstat : s.status = .Running)
    (hx20 : s.readReg64 .x20 = pt.y.value.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = ptr)
    (hx23 : s.readReg64 .x23 = ptr + BitVec.ofNat 64 (4 * insertIdx))
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 vec.length)
    (hx27 : BitVec.truncate 16 (s.readReg64 .x27) = pt.x.value)
    (hx29 : s.readReg64 .x29 = fsp + 448#64)
    (hcont : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 296#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x19 = 1#64 →
      sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x22 = ptr →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = BitVec.ofNat 64 (vec.length + 1) →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = fsp + 448#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt b ext) target_pc sf
        (tempVecPtAt A fsp cap ptr { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗ P)
        post) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc s
      (tempVecPtAt A fsp cap ptr { vec := vec } ∗ P)
      post := by
  subst hins
  from_pb_fetches_range b (Rust.withPanics ext) 560 24
  dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  unfold tempVecPtAt
  rw [memRegion_spare_split_one ptr hlt hcap]
  wp_pull_exists
  wp_steps 6
  have htake_drop : vec.take vec.length ++ (pt :: vec.drop vec.length) = vec ++ [pt] := by
    rw [List.take_length, List.drop_length]
  have hbv_len' : BitVec.ofNat 64 vec.length + 1#64 = BitVec.ofNat 64 (vec.length + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have hreasm := reassemble_tempVecPtAt_snoc A fsp cap ptr vec pt
  rw [← htake_drop] at hreasm
  refine SepWP.weaken_pre
    (P' := tempVecPtAt A fsp cap ptr { vec := vec.take vec.length ++ (pt :: vec.drop vec.length) } ∗ P)
    (by refine Entails.trans ?_ (sepConj_mono_left hreasm)
        exact Entails.of_eq (by ac_rfl)) ?_
  apply hcont <;> simp [wp_norm, arm64_norm, hbv_len', *]

/-- Symbolic execution of `0x62d30..0x62d60` (`entry + 532#64` to `entry + 296#64`)
    when `vec.length < cap.toNat` and `insertIdx ≤ vec.length`. -/
theorem fromPb_bsearch_insert_at_532_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64} (hA : AllocContracts b A ext)
    (fsp cap ptr : BitVec 64) (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx ≤ vec.length) (hlt : vec.length < cap.toNat)
    (hcap : cap.toNat * 4 < 2 ^ 63)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 532#64)
    (hstat : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 insertIdx)
    (hx20 : s.readReg64 .x20 = pt.y.value.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = ptr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 vec.length)
    (hx27 : BitVec.truncate 16 (s.readReg64 .x27) = pt.x.value)
    (hx29 : s.readReg64 .x29 = fsp + 448#64)
    (hcont : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 296#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x19 = 1#64 →
      sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x22 = ptr →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = BitVec.ofNat 64 (vec.length + 1) →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = fsp + 448#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt b ext) target_pc sf
        (tempVecPtAt A fsp cap ptr { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗
          stackAt s.sp 0 ∗ P)
        post) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc s
      (tempVecPtAt A fsp cap ptr { vec := vec } ∗ stackAt s.sp 0 ∗ P)
      post := by
  have hmem := @fromPb_bsearch_memmove_insert_sepWP b A ext target_pc hA fsp cap ptr vec insertIdx pt
  have hend := @fromPb_bsearch_end_insert_sepWP b A ext target_pc fsp cap ptr vec insertIdx pt
  from_pb_fetches_range b (Rust.withPanics ext) 532 12
  dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hmem hend hpc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  have hlsl_ins : (BitVec.ofNat 64 insertIdx) <<< 2 = BitVec.ofNat 64 (4 * insertIdx) :=
    bv64_lsl2_ofNat (by omega)
  have hsub_ins : BitVec.ofNat 64 vec.length - BitVec.ofNat 64 insertIdx =
      BitVec.ofNat 64 (vec.length - insertIdx) :=
    bv64_sub_ofNat hins (by omega)
  wp_steps 3
  rw [bv64_ule_ofNat (by omega) (by omega)]
  rcases Nat.eq_or_lt_of_le hins with hins_eq | hins_lt
  · have hle_t : vec.length ≤ insertIdx := by omega
    simp only [hle_t, decide_true, ↓reduceIte]
    refine hend hins_eq hlt hcap _ (stackAt s.sp 0 ∗ P) post
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hstat])
      (by simp [wp_norm, arm64_norm, hx20])
      (by simp [wp_norm, arm64_norm, hx22])
      (by simp [wp_norm, arm64_norm, hx22, hx19, hlsl_ins])
      (by simp [wp_norm, arm64_norm, hx26])
      (by simpa [wp_norm, arm64_norm] using hx27)
      (by simp [wp_norm, arm64_norm, hx29])
      (fun sf hpc_f hstat_f hsp_f htr_f hx19_f hx21_f hx22_f hx24_f hx25_f hx26_f hx28_f hx29_f hvregs_f => ?_)
    apply hcont sf hpc_f hstat_f
    · simpa [wp_norm, arm64_norm] using hsp_f
    · simpa [wp_norm, arm64_norm] using htr_f
    · exact hx19_f
    · simpa [wp_norm, arm64_norm] using hx21_f
    · exact hx22_f
    · simpa [wp_norm, arm64_norm] using hx24_f
    · simpa [wp_norm, arm64_norm] using hx25_f
    · exact hx26_f
    · simpa [wp_norm, arm64_norm] using hx28_f
    · exact hx29_f
    · simpa [wp_norm, arm64_norm] using hvregs_f
  · have hle_f : ¬ vec.length ≤ insertIdx := by omega
    simp only [hle_f, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine hmem hins_lt hlt hcap _ P post
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hstat])
      (by simpa [wp_norm, arm64_norm] using hsp_align)
      (by simp [wp_norm, arm64_norm, hx26, hx19, hsub_ins])
      (by simp [wp_norm, arm64_norm, hx20])
      (by simp [wp_norm, arm64_norm, hx22])
      (by simp [wp_norm, arm64_norm, hx22, hx19, hlsl_ins])
      (by simp [wp_norm, arm64_norm, hx26])
      (by simpa [wp_norm, arm64_norm] using hx27)
      (by simp [wp_norm, arm64_norm, hx29])
      (fun sf hpc_f hstat_f hsp_f htr_f hx19_f hx21_f hx22_f hx24_f hx25_f hx26_f hx28_f hx29_f hvregs_f => ?_)
    apply hcont sf hpc_f hstat_f
    · simpa [wp_norm, arm64_norm] using hsp_f
    · simpa [wp_norm, arm64_norm] using htr_f
    · exact hx19_f
    · simpa [wp_norm, arm64_norm] using hx21_f
    · exact hx22_f
    · simpa [wp_norm, arm64_norm] using hx24_f
    · simpa [wp_norm, arm64_norm] using hx25_f
    · exact hx26_f
    · simpa [wp_norm, arm64_norm] using hx28_f
    · exact hx29_f
    · simpa [wp_norm, arm64_norm] using hvregs_f

/-- Symbolic execution of `bsearchReplace` (`0x62ccc..0x62c44`, `entry + 432#64` to `entry + 296#64`)
    when `1 ≤ s.vec.length < cap.toNat`. -/
theorem fromPb_bsearchReplace_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64} (hA : AllocContracts b A ext)
    (fsp cap ptr : BitVec 64) (s : SortedSetPt) (pt : Pt)
    (h1 : 1 ≤ s.vec.length) (hlt_cap : s.vec.length < cap.toNat)
    (hcap : cap.toNat * 4 < 2 ^ 63)
    (st : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 432#64)
    (hrun : st.status = .Running)
    (hsp_al : st.spAligned = true)
    (hx19 : st.readReg64 .x19 = 1#64)
    (hx20 : st.readReg64 .x20 = pt.y.value.zeroExtend 64)
    (hx22 : st.readReg64 .x22 = ptr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 s.vec.length)
    (hx27 : BitVec.truncate 16 (st.readReg64 .x27) = pt.x.value)
    (hx29 : st.readReg64 .x29 = fsp + 448#64)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 296#64 →
      sf.status = .Running →
      sf.sp = st.sp →
      sf.trace = st.trace →
      sf.readReg64 .x19 = 1#64 →
      sf.readReg64 .x21 = st.readReg64 .x21 →
      sf.readReg64 .x22 = ptr →
      sf.readReg64 .x24 = st.readReg64 .x24 →
      sf.readReg64 .x25 = st.readReg64 .x25 →
      sf.readReg64 .x26 = BitVec.ofNat 64 (bsearchReplace s pt).vec.length →
      sf.readReg64 .x28 = st.readReg64 .x28 →
      sf.readReg64 .x29 = fsp + 448#64 →
      calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWP (tripleRatchetProgAtExt b ext) target_pc sf
        (tempVecPtAt A fsp cap ptr (bsearchReplace s pt) ∗ stackAt st.sp 0 ∗ P)
        post) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc st
      (tempVecPtAt A fsp cap ptr s ∗ stackAt st.sp 0 ∗ P)
      post := by
  unfold tempVecPtAt
  refine SepWP.weaken_pre
    (P' := ptSliceAt ptr s.vec ∗
      (((fsp + 416#64) ↦₆₄ cap) ∗ ((fsp + 416#64 + 8#64) ↦₆₄ ptr) ∗
        ((fsp + 416#64 + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
        A.live ptr (cap.toNat * 4) 2 ∗
        memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) ∗
        stackAt st.sp 0 ∗ P))
    (Entails.of_eq (by ac_rfl)) ?_
  refine fromPb_bsearch_to_492_sepWP h1 (by omega) st _ _ hpc hrun hx22 hx26 hx27
    (fun s1 hpc1 hrun1 hsp1 htr1 hx22_1 hx8_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 => ?_)
  have hsp1_al : s1.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢; rwa [hsp1]
  let base := bsearchLoop s.vec pt.x.value 0 s.vec.length
  change s1.readReg64 .x8 = BitVec.ofNat 64 base at hx8_1
  have ⟨_, hb_lt0⟩ := bsearchLoop_bounds s.vec pt.x.value 0 s.vec.length h1 (by omega)
  have hb_lt : base < s.vec.length := by omega
  have hb_get : s.vec[base]?.getD default = s.vec[base]'hb_lt := by
    rw [List.getElem?_eq_getElem hb_lt, Option.getD_some]
  let baseX := (s.vec[base]'hb_lt).x.value
  have hlsl_base : (BitVec.ofNat 64 base) <<< 2 = BitVec.ofNat 64 (4 * base) :=
    bv64_lsl2_ofNat (by omega)
  have huxth_1 : BitVec.zeroExtend 32 (BitVec.truncate 16 (s1.readReg64 .x27)) = pt.x.value.zeroExtend 32 := by
    rw [hx27_1, hx27]
  unfold bsearchReplace at hnext
  dsimp only at hnext
  rw [hb_get] at hnext
  by_cases heq : ((s.vec[base]'hb_lt).x.value == pt.x.value) = true
  · simp only [heq, ↓reduceIte] at hnext
    have hbaseX_eq : (s.vec[base]'hb_lt).x.value = pt.x.value := beq_iff_eq.mp heq
    from_pb_fetches_range b (Rust.withPanics ext) 492 24
    dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpc1 hnext ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
    examples_hide_fetches
    rw [ptSliceAt_focus s.vec base ptr hb_lt]
    unfold ptAt
    wp_steps 6
    have hreasm := reassemble_tempVecPtAt_set A fsp cap ptr s.vec base pt hb_lt
    refine SepWP.weaken_pre
      (P' := tempVecPtAt A fsp cap ptr { vec := s.vec.set base pt } ∗ stackAt st.sp 0 ∗ P)
      (by rw [hbaseX_eq]
          refine Entails.trans ?_ (sepConj_mono_left hreasm)
          exact Entails.of_eq (by ac_rfl)) ?_
    have hlen_set : (s.vec.set base pt).length = s.vec.length := List.length_set
    apply hnext
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hrun1]
    · simpa [wp_norm, arm64_norm] using hsp1
    · simpa [wp_norm, arm64_norm] using htr1
    · simpa [wp_norm, arm64_norm, hx19] using hx19_1
    · simpa [wp_norm, arm64_norm] using hx21_1
    · simpa [wp_norm, arm64_norm, hx22] using hx22_1
    · simpa [wp_norm, arm64_norm] using hx24_1
    · simpa [wp_norm, arm64_norm] using hx25_1
    · rw [hlen_set]; simpa [wp_norm, arm64_norm, hx26] using hx26_1
    · simpa [wp_norm, arm64_norm] using hx28_1
    · simpa [wp_norm, arm64_norm, hx29] using hx29_1
    · simpa [wp_norm, arm64_norm] using hvregs_1
  · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hnext
    let insertIdx := if baseX.toNat < pt.x.value.toNat then base + 1 else base
    have hins_le : insertIdx ≤ s.vec.length := by dsimp [insertIdx]; split_ifs <;> omega
    have hcap_ne : ¬ s.vec.length = cap.toNat := by omega
    have hfold_slice :
        ((ptSliceAt ptr (List.take base s.vec) ∗
          ((ptr + BitVec.ofNat 64 (4 * base)) ↦₁₆ (s.vec[base]'hb_lt).x.value ∗
            (ptr + BitVec.ofNat 64 (4 * base) + 2#64) ↦₁₆ (s.vec[base]'hb_lt).y.value) ∗
          ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + 1))) (List.drop (base + 1) s.vec)) ∗
          (((fsp + 416#64) ↦₆₄ cap) ∗ ((fsp + 416#64 + 8#64) ↦₆₄ ptr) ∗
            ((fsp + 416#64 + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
            A.live ptr (cap.toNat * 4) 2 ∗
            memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4) ∗
            stackAt st.sp 0 ∗ P)) =
        (tempVecPtAt A fsp cap ptr { vec := s.vec } ∗ stackAt st.sp 0 ∗ P) := by
      unfold tempVecPtAt
      change ((ptSliceAt ptr (List.take base s.vec) ∗
        ptAt (s.vec[base]'hb_lt) (ptr + BitVec.ofNat 64 (4 * base)) ∗
        ptSliceAt (ptr + BitVec.ofNat 64 (4 * (base + 1))) (List.drop (base + 1) s.vec)) ∗ _) = _
      rw [← ptSliceAt_focus s.vec base ptr hb_lt]
      ac_rfl
    have hins532 := @fromPb_bsearch_insert_at_532_sepWP b A ext target_pc hA fsp cap ptr
      s.vec insertIdx pt hins_le hlt_cap hcap
    from_pb_fetches_range b (Rust.withPanics ext) 492 40
    dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hins532 hpc1 hnext ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
    examples_hide_fetches
    rw [ptSliceAt_focus s.vec base ptr hb_lt]
    unfold ptAt
    wp_steps 4
    rw [bv32_bne_zeroExtend16, show ((s.vec[base]'hb_lt).x.value == pt.x.value) = false from
      Bool.eq_false_iff.mpr heq]
    simp only [Bool.not_false, ↓reduceIte]
    wp_steps 4
    rw [hfold_slice, bv64_beq_cap_ofNat (by omega)]
    simp only [hcap_ne, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [← hsp1]
    refine hins532 _ P _
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun1])
      (by simpa [wp_norm, arm64_norm] using hsp1_al)
      (by simp only [wp_norm, arm64_norm, hx27_1, hx27]
          exact cinc_insertIdx_eq baseX pt.x.value base)
      (by simp [wp_norm, arm64_norm, hx20_1, hx20])
      (by simp [wp_norm, arm64_norm, hx22_1, hx22])
      (by simp [wp_norm, arm64_norm, hx26_1, hx26])
      (by simpa [wp_norm, arm64_norm, hx27_1] using hx27)
      (by simp [wp_norm, arm64_norm, hx29_1, hx29])
      (fun sf hpc_f hrun_f hsp_f htr_f hx19_f hx21_f hx22_f hx24_f hx25_f hx26_f hx28_f hx29_f hvregs_f => ?_)
    have hsp_f' : sf.sp = st.sp := by
      simpa [wp_norm, arm64_norm, hsp1] using hsp_f
    rw [← hsp_f, hsp_f']
    have hlen_ins : (s.vec.take insertIdx ++ (pt :: s.vec.drop insertIdx)).length = s.vec.length + 1 := by
      rw [List.length_append, List.length_take_of_le hins_le, List.length_cons, List.length_drop]
      omega
    apply hnext sf hpc_f hrun_f hsp_f' (htr_f.trans htr1) hx19_f
    · rw [hx21_f]; simpa [wp_norm, arm64_norm] using hx21_1
    · exact hx22_f
    · rw [hx24_f]; simpa [wp_norm, arm64_norm] using hx24_1
    · rw [hx25_f]; simpa [wp_norm, arm64_norm] using hx25_1
    · change sf.readReg64 .x26 = BitVec.ofNat 64 (s.vec.take insertIdx ++ (pt :: s.vec.drop insertIdx)).length
      rw [hlen_ins]; exact hx26_f
    · rw [hx28_f]; simpa [wp_norm, arm64_norm] using hx28_1
    · exact hx29_f
    · rw [hvregs_f]; simpa [wp_norm, arm64_norm] using hvregs_1

/-! ## Single-Point `bsearchPush` (`0x62c5c..0x62c44`, `+320 -> +296`) -/

/-- Symbolic execution of `0x62cac..0x62cc8` (`entry + 400#64` to `entry + 296#64`)
    when `vec = []` and `0 < cap.toNat`. -/
theorem fromPb_bsearch_push_empty_at_400_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (fsp cap ptr : BitVec 64) (pt : Pt)
    (hlt0 : 0 < cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 400#64)
    (hstat : s.status = .Running)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx20 : s.readReg64 .x20 = pt.y.value.zeroExtend 64)
    (hx27 : BitVec.truncate 16 (s.readReg64 .x27) = pt.x.value)
    (hx29 : s.readReg64 .x29 = fsp + 448#64)
    (hcont : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 296#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x19 = 1#64 →
      sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x22 = ptr →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = 1#64 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = fsp + 448#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt b ext) target_pc sf
        (tempVecPtAt A fsp cap ptr { vec := [pt] } ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc s
      (tempVecPtAt A fsp cap ptr { vec := [] } ∗ P) post := by
  have hcap_ne : cap ≠ 0#64 := by
    intro hc; subst hc
    have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
    omega
  have hbeq0 : (cap == 0#64) = false := beq_false_of_ne hcap_ne
  from_pb_fetches_range b (Rust.withPanics ext) 400 32
  dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
  examples_hide_fetches
  unfold tempVecPtAt
  dsimp only [List.length_nil]
  have hsplit := memRegion_spare_split_one (len := 0) ptr hlt0 hcap
  rw [hsplit]
  wp_pull_exists
  wp_steps 8
  have hreasm := reassemble_tempVecPtAt_snoc A fsp cap ptr [] pt
  dsimp only [List.length_nil, List.nil_append, Nat.zero_add, Nat.mul_zero] at hreasm
  refine SepWP.weaken_pre
    (P' := tempVecPtAt A fsp cap ptr { vec := [pt] } ∗ P)
    (by refine Entails.trans ?_ (sepConj_mono_left hreasm)
        exact Entails.of_eq (by ac_rfl)) ?_
  apply hcont <;> simp [wp_norm, arm64_norm, *]

/-- Symbolic execution of `bsearchPush` (`0x62c5c..0x62c44`, `entry + 320#64` to `entry + 296#64`)
    when `s.vec.length < cap.toNat`. -/
theorem fromPb_bsearchPush_at_320_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64} (hA : AllocContracts b A ext)
    (fsp cap ptr : BitVec 64) (s : SortedSetPt) (pt : Pt)
    (hlt_cap : s.vec.length < cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63)
    (hlen : s.vec.length ≤ 65536)
    (st : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 320#64)
    (hrun : st.status = .Running)
    (hsp_al : st.spAligned = true)
    (hx19 : st.readReg64 .x19 = 1#64)
    (hx20 : st.readReg64 .x20 = pt.y.value.zeroExtend 64)
    (hx22 : st.readReg64 .x22 = ptr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 s.vec.length)
    (hx27 : BitVec.truncate 16 (st.readReg64 .x27) = pt.x.value)
    (hx29 : st.readReg64 .x29 = fsp + 448#64)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr fromPbDecName + 296#64 →
      sf.status = .Running →
      sf.sp = st.sp →
      sf.trace = st.trace →
      sf.readReg64 .x19 = 1#64 →
      sf.readReg64 .x21 = st.readReg64 .x21 →
      sf.readReg64 .x22 = ptr →
      sf.readReg64 .x24 = st.readReg64 .x24 →
      sf.readReg64 .x25 = st.readReg64 .x25 →
      sf.readReg64 .x26 = BitVec.ofNat 64 (bsearchPush s pt).vec.length →
      sf.readReg64 .x28 = st.readReg64 .x28 →
      sf.readReg64 .x29 = fsp + 448#64 →
      calleeSavedVRegs sf = calleeSavedVRegs st →
      SepWP (tripleRatchetProgAtExt b ext) target_pc sf
        (tempVecPtAt A fsp cap ptr (bsearchPush s pt) ∗ stackAt st.sp 0 ∗ P)
        post) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc st
      (tempVecPtAt A fsp cap ptr s ∗ stackAt st.sp 0 ∗ P)
      post := by
  by_cases h1 : 1 ≤ s.vec.length
  · -- Non-empty vector (`1 ≤ s.vec.length`)
    let lastIdx := s.vec.length - 1
    have hlast_lt : lastIdx < s.vec.length := by omega
    let lastPt := s.vec[lastIdx]'hlast_lt
    have hlast_eq : s.vec.getLast? = some lastPt := by
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlast_lt]
    have hne0 : (BitVec.ofNat 64 s.vec.length == 0#64) = false := bv64_ne_zero_of_pos h1 hlen
    have hlsl_len : (BitVec.ofNat 64 s.vec.length) <<< 2 = BitVec.ofNat 64 (4 * s.vec.length) :=
      bv64_lsl2_ofNat (by omega)
    have hsub4 : ptr + BitVec.ofNat 64 (4 * s.vec.length) + 18446744073709551612#64 =
        ptr + BitVec.ofNat 64 (4 * lastIdx) := ptr_add_len_sub4 ptr h1 hlen
    have hsub2 : ptr + BitVec.ofNat 64 (4 * s.vec.length) + 18446744073709551614#64 =
        ptr + BitVec.ofNat 64 (4 * lastIdx) + 2#64 := ptr_add_len_sub2 ptr h1 hlen
    unfold bsearchPush at hnext
    rw [hlast_eq] at hnext
    dsimp only at hnext
    cases hcmp : Pt.cmp pt lastPt with
    | eq =>
      rw [hcmp] at hnext
      dsimp only at hnext
      have hset_eq : s.vec.dropLast ++ [pt] = s.vec.set lastIdx pt :=
        dropLast_append_singleton_eq_set s.vec pt h1
      rw [hset_eq] at hnext
      have hcmp' : pt.x.value.toNat = (s.vec[lastIdx]'hlast_lt).x.value.toNat :=
        compare_eq_iff_eq.mp hcmp
      have hule1 :
          (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value).ule
            (BitVec.zeroExtend 32 pt.x.value) = true := by
        rw [bv32_ule_zeroExtend16, decide_eq_true_eq]; omega
      have hule2 :
          (BitVec.zeroExtend 32 pt.x.value).ule
            (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value) = true := by
        rw [bv32_ule_zeroExtend16, decide_eq_true_eq]; omega
      from_pb_fetches_range b (Rust.withPanics ext) 288 8
      from_pb_fetches_range b (Rust.withPanics ext) 320 36
      dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
      examples_hide_fetches
      unfold tempVecPtAt
      rw [AddChunk.ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
      unfold ptAt
      rw [← hsub2, ← hsub4]
      wp_steps 11
      rw [hsub4, hsub2]
      have hreasm := reassemble_tempVecPtAt_set A fsp cap ptr s.vec lastIdx pt hlast_lt
      refine SepWP.weaken_pre
        (P' := tempVecPtAt A fsp cap ptr { vec := s.vec.set lastIdx pt } ∗ stackAt st.sp 0 ∗ P)
        (by refine Entails.trans ?_ (sepConj_mono_left hreasm)
            exact Entails.of_eq (by ac_rfl)) ?_
      have hlen_set : (s.vec.set lastIdx pt).length = s.vec.length := List.length_set
      apply hnext <;> simp [wp_norm, arm64_norm, hlen_set, *]
    | lt =>
      rw [hcmp] at hnext
      dsimp only at hnext
      have hcmp' : pt.x.value.toNat < (s.vec[lastIdx]'hlast_lt).x.value.toNat :=
        compare_lt_iff_lt.mp hcmp
      have hule1 :
          (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value).ule
            (BitVec.zeroExtend 32 pt.x.value) = false := by
        rw [bv32_ule_zeroExtend16, decide_eq_false_iff_not]; omega
      have hrep := @fromPb_bsearchReplace_sepWP b A ext target_pc hA fsp cap ptr s pt h1 hlt_cap hcap
      from_pb_fetches_range b (Rust.withPanics ext) 320 44
      dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hrep hpc hnext ⊢
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
      examples_hide_fetches
      unfold tempVecPtAt
      rw [AddChunk.ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
      unfold ptAt
      rw [← hsub2, ← hsub4]
      wp_steps 11
      rw [hsub4, hsub2]
      have hfold_slice :
          ptSliceAt ptr (s.vec.take lastIdx) ∗
            (((ptr + BitVec.ofNat 64 (4 * lastIdx)) ↦₁₆ (s.vec[lastIdx]'hlast_lt).x.value) ∗
              ((ptr + BitVec.ofNat 64 (4 * lastIdx) + 2#64) ↦₁₆ (s.vec[lastIdx]'hlast_lt).y.value)) ∗
            ptSliceAt (ptr + BitVec.ofNat 64 (4 * (lastIdx + 1))) (s.vec.drop (lastIdx + 1)) =
          ptSliceAt ptr s.vec := by
        rw [AddChunk.ptSliceAt_focus s.vec lastIdx ptr hlast_lt]; rfl
      rw [hfold_slice]
      refine SepWP.weaken_pre (Entails.of_eq (by unfold tempVecPtAt; ac_rfl))
        (hrep _ P _
          (by simp [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hrun])
          (by simpa [wp_norm, arm64_norm] using hsp_al)
          (by simp [wp_norm, arm64_norm, hx19])
          (by simp [wp_norm, arm64_norm, hx20])
          (by simp [wp_norm, arm64_norm, hx22])
          (by simp [wp_norm, arm64_norm, hx26])
          (by simpa [wp_norm, arm64_norm] using hx27)
          (by simp [wp_norm, arm64_norm, hx29])
          (fun sf hpc_f hrun_f hsp_f htr_f hx19_f hx21_f hx22_f hx24_f hx25_f hx26_f hx28_f hx29_f hvregs_f => ?_))
      apply hnext sf hpc_f hrun_f
      · simpa [wp_norm, arm64_norm] using hsp_f
      · simpa [wp_norm, arm64_norm] using htr_f
      · exact hx19_f
      · simpa [wp_norm, arm64_norm] using hx21_f
      · exact hx22_f
      · simpa [wp_norm, arm64_norm] using hx24_f
      · simpa [wp_norm, arm64_norm] using hx25_f
      · exact hx26_f
      · simpa [wp_norm, arm64_norm] using hx28_f
      · exact hx29_f
      · simpa [wp_norm, arm64_norm] using hvregs_f
    | gt =>
      rw [hcmp] at hnext
      dsimp only at hnext
      have hcmp' : (s.vec[lastIdx]'hlast_lt).x.value.toNat < pt.x.value.toNat :=
        compare_gt_iff_gt.mp hcmp
      have hule1 :
          (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value).ule
            (BitVec.zeroExtend 32 pt.x.value) = true := by
        rw [bv32_ule_zeroExtend16, decide_eq_true_eq]; omega
      have hule2 :
          (BitVec.zeroExtend 32 pt.x.value).ule
            (BitVec.zeroExtend 32 (s.vec[lastIdx]'hlast_lt).x.value) = false := by
        rw [bv32_ule_zeroExtend16, decide_eq_false_iff_not]; omega
      have hbeq_cap : (BitVec.ofNat 64 s.vec.length == cap) = false := by
        rw [bv64_beq_cap_ofNat (by omega), decide_eq_false_iff_not]; omega
      have hule_succ :
          (BitVec.ofNat 64 s.vec.length).ule (BitVec.ofNat 64 (s.vec.length + 1)) = true :=
        bv64_ule_succ (by omega)
      from_pb_fetches_range b (Rust.withPanics ext) 320 76
      dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
      examples_hide_fetches
      unfold tempVecPtAt
      rw [AddChunk.ptSliceAt_focus s.vec lastIdx ptr hlast_lt]
      unfold ptAt
      rw [← hsub2, ← hsub4]
      rw [memRegion_spare_split_one ptr hlt_cap hcap]
      wp_pull_exists
      wp_steps 19
      rw [hsub4, hsub2]
      have hfold_slice :
          ptSliceAt ptr (s.vec.take lastIdx) ∗
            (((ptr + BitVec.ofNat 64 (4 * lastIdx)) ↦₁₆ (s.vec[lastIdx]'hlast_lt).x.value) ∗
              ((ptr + BitVec.ofNat 64 (4 * lastIdx) + 2#64) ↦₁₆ (s.vec[lastIdx]'hlast_lt).y.value)) ∗
            ptSliceAt (ptr + BitVec.ofNat 64 (4 * (lastIdx + 1))) (s.vec.drop (lastIdx + 1)) =
          ptSliceAt ptr s.vec := by
        rw [AddChunk.ptSliceAt_focus s.vec lastIdx ptr hlast_lt]; rfl
      have hreasm := reassemble_tempVecPtAt_snoc A fsp cap ptr s.vec pt
      rw [← hfold_slice] at hreasm
      refine SepWP.weaken_pre
        (P' := tempVecPtAt A fsp cap ptr { vec := s.vec ++ [pt] } ∗ stackAt st.sp 0 ∗ P)
        (by refine Entails.trans ?_ (sepConj_mono_left hreasm)
            exact Entails.of_eq (by ac_rfl)) ?_
      have hlen_snoc : (s.vec ++ [pt]).length = s.vec.length + 1 := by simp
      apply hnext <;> simp [wp_norm, arm64_norm, hlen_snoc, *]
  · -- Empty vector (`s.vec = []`)
    have hnil : s.vec = [] := List.eq_nil_iff_length_eq_zero.mpr (by omega)
    have hs_eq : s = { vec := [] } := by cases s; subst hnil; rfl
    subst hs_eq
    have hpush_nil : bsearchPush { vec := [] } pt = { vec := [pt] } := rfl
    rw [hpush_nil] at hnext
    have hpush400 := @fromPb_bsearch_push_empty_at_400_sepWP b A ext target_pc fsp cap ptr pt
      (by simpa using hlt_cap) hcap
    from_pb_fetches_range b (Rust.withPanics ext) 320 4
    dsimp only [tripleRatchetProgAtExt, fromPbDecName, BitVec.ofNat_eq_ofNat] at hpush400 hpc hnext ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder>::from_pb" = entry
    examples_hide_fetches
    dsimp only [List.length_nil] at hx26
    wp_steps 1
    refine hpush400 _ (stackAt st.sp 0 ∗ P) _
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm, hx19])
      (by simp [wp_norm, arm64_norm, hx20])
      (by simpa [wp_norm, arm64_norm] using hx27)
      (by simp [wp_norm, arm64_norm, hx29])
      (fun sf hpc_f hrun_f hsp_f htr_f hx19_f hx21_f hx22_f hx24_f hx25_f hx26_f hx28_f hx29_f hvregs_f => ?_)
    apply hnext sf hpc_f hrun_f
    · simpa [wp_norm, arm64_norm] using hsp_f
    · simpa [wp_norm, arm64_norm] using htr_f
    · exact hx19_f
    · simpa [wp_norm, arm64_norm] using hx21_f
    · exact hx22_f
    · simpa [wp_norm, arm64_norm] using hx24_f
    · simpa [wp_norm, arm64_norm] using hx25_f
    · exact hx26_f
    · simpa [wp_norm, arm64_norm] using hx28_f
    · exact hx29_f
    · simpa [wp_norm, arm64_norm] using hvregs_f

end CryptoVerification.SpqrV1.Poly.DecoderPb
