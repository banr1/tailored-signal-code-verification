/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk`: Relocatable Loop Proofs

Relocatable `[LibsignalPlacement]` proofs of the inner binary-search loop (`+260 → +296`),
`memmove` insertion, and `RawVec<Pt>::grow_one` calls on Block `419`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.AddChunk

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout AddChunkNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓] (ls_stub% "memmove")

/-! ## Placed Inner Binary Search Loop (`+260 -> +296`) -/

theorem bsearchLoop_placed_sepWP [LibsignalPlacement] {ext : String → Option (State → State)}
    (vec : List Pt) (ptr : BitVec 64) (xVal : BitVec 16)
    (hlen_bound : 4 * vec.length < 2 ^ 64) :
    ∀ (size base : Nat) (s : State) (P : SepProp) (post : State → SepProp → Prop),
      1 < size →
      base + size ≤ vec.length →
      s.pc = (blkPl_419).base + 260#64 →
      s.status = .Running →
      s.readReg64 .x8 = ptr →
      s.readReg64 .x9 = BitVec.ofNat 64 base →
      s.readReg64 .x10 = BitVec.ofNat 64 size →
      s.readReg64 .x24 = xVal.zeroExtend 64 →
      (∀ (sf : State),
        sf.pc = (blkPl_419).base + 296#64 →
        sf.status = .Running →
        sf.sp = s.sp →
        sf.trace = s.trace →
        sf.readReg64 .x8 = ptr →
        sf.readReg64 .x9 = BitVec.ofNat 64 (bsearchLoop vec xVal base size) →
        sf.readReg64 .x14 = s.readReg64 .x14 →
        sf.readReg64 .x19 = s.readReg64 .x19 →
        sf.readReg64 .x20 = s.readReg64 .x20 →
        sf.readReg64 .x21 = s.readReg64 .x21 →
        sf.readReg64 .x23 = s.readReg64 .x23 →
        sf.readReg64 .x24 = s.readReg64 .x24 →
        sf.readReg64 .x25 = s.readReg64 .x25 →
        sf.readReg64 .x27 = s.readReg64 .x27 →
        sf.readReg64 .x28 = s.readReg64 .x28 →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        sf.readReg64 .x30 = s.readReg64 .x30 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
          ((blkPl_419).base + 296#64)
          sf (ptSliceAt ptr vec ∗ P) post) →
      SepWP ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
        ((blkPl_419).base + 296#64)
        s (ptSliceAt ptr vec ∗ P) post := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro base s P post hgt hle hpc hstat hx8 hx9 hx10 hx24 hcont
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
        (by simp [wp_norm, arm64_norm, hx8])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hx24])
        (fun sf hpc_f hstat_f hsp_f htr_f hx8_f hx9_f hx14_f hx19_f hx20_f hx21_f hx23_f hx24_f hx25_f hx27_f hx28_f hx29_f hx30_f hvregs_f => ?_)
      apply hcont sf hpc_f hstat_f
      · simpa [wp_norm, arm64_norm] using hsp_f
      · simpa [wp_norm, arm64_norm] using htr_f
      · exact hx8_f
      · rw [hbs_step]; exact hx9_f
      · simpa [wp_norm, arm64_norm] using hx14_f
      · simpa [wp_norm, arm64_norm] using hx19_f
      · simpa [wp_norm, arm64_norm] using hx20_f
      · simpa [wp_norm, arm64_norm] using hx21_f
      · simpa [wp_norm, arm64_norm] using hx23_f
      · simpa [wp_norm, arm64_norm] using hx24_f
      · simpa [wp_norm, arm64_norm] using hx25_f
      · simpa [wp_norm, arm64_norm] using hx27_f
      · simpa [wp_norm, arm64_norm] using hx28_f
      · simpa [wp_norm, arm64_norm] using hx29_f
      · simpa [wp_norm, arm64_norm] using hx30_f
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
      · simp [wp_norm, arm64_norm, hx8]
      · rw [hbs_done]; simp [wp_norm, arm64_norm]
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
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]

/-! ## Placed `memmove` Insertion & `grow_one` Calls -/

theorem bsearch_memmove_insert_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack))
    (v cap ptr lenOld : BitVec 64) (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx < vec.length) (hlt : vec.length < cap.toNat)
    (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_419).base + 348#64)
    (hstat : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (vec.length - insertIdx))
    (hx21 : s.readReg64 .x21 = v)
    (hx22 : s.readReg64 .x22 = ptr + BitVec.ofNat 64 (4 * insertIdx))
    (hx24 : s.readReg64 .x24 = pt.x.value.zeroExtend 64)
    (hx27 : s.readReg64 .x27 = pt.y.value.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 vec.length)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_419).base + 64#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x14 = 1#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
        ((blkPl_419).base + 64#64)
        sf
        (sortedSetPtOf A v { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗
          stackAt s.sp growOneStack ∗ P)
        post) :
    SepWP ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      ((blkPl_419).base + 64#64)
      s
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
        A.live ptr (cap.toNat * 4) 2 ∗
        ptSliceAt ptr vec ∗
        memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4) ∗
        stackAt s.sp growOneStack ∗ P)
      post := by
  have hmemmove : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsρ spqrMemmoveSym) (sessionMemmoveSpec growOneStack) :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem hmemmove_sat
  have hprep := insert_suffix_prepare_memmove ptr vec insertIdx cap.toNat hins hlt hcap
  refine SepWP.weaken_pre
    (show ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
        A.live ptr (cap.toNat * 4) 2 ∗
        ptSliceAt ptr vec ∗
        memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4) ∗
        stackAt s.sp growOneStack ∗ P) ⊢
      ∃∗ slotBs : List (BitVec 8),
        ⌜slotBs.length = 4⌝ ∗
        ptSliceAt ptr (vec.take insertIdx) ∗
        ((ptr + BitVec.ofNat 64 (4 * insertIdx)) ↦ₛ (ptListBytes (vec.drop insertIdx) ++ slotBs)) ∗
        memRegion (ptr + BitVec.ofNat 64 ((vec.length + 1) * 4)) ((cap.toNat - (vec.length + 1)) * 4) ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
        A.live ptr (cap.toNat * 4) 2 ∗ stackAt s.sp growOneStack ∗ P by
      rw [show ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
          A.live ptr (cap.toNat * 4) 2 ∗
          ptSliceAt ptr vec ∗
          memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4) ∗
          stackAt s.sp growOneStack ∗ P) =
        (ptSliceAt ptr vec ∗
          memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4)) ∗
        ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
          A.live ptr (cap.toNat * 4) 2 ∗ stackAt s.sp growOneStack ∗ P) by ac_rfl]
      refine Entails.trans (sepConj_mono_left hprep) ?_
      rw [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro slotBs
      refine Entails.sepExists_right slotBs (Entails.of_eq (by ac_rfl))) ?_
  apply SepWP.exists_left; intro slotBs
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
  have hbv_len' : BitVec.ofNat 64 vec.length + 1#64 = BitVec.ofNat 64 (vec.length + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have hreasm := reassemble_sortedSetPtOf_insert A v cap ptr vec insertIdx pt (by omega) hlt hcap hptr
  rw [hbv_len'] at hreasm
  refine SepWP.weaken_pre
    (show ((ptr + BitVec.ofNat 64 (4 * insertIdx)) ↦₁₆ pt.x.value ∗
        (ptr + BitVec.ofNat 64 (4 * insertIdx) + 2#64) ↦₁₆ pt.y.value ∗
        ptSliceAt (ptr + BitVec.ofNat 64 (4 * insertIdx) + 4#64) (vec.drop insertIdx) ∗
        stackAt s.sp growOneStack ∗
        ptSliceAt ptr (vec.take insertIdx) ∗
        memRegion (ptr + BitVec.ofNat 64 ((vec.length + 1) * 4)) ((cap.toNat - (vec.length + 1)) * 4) ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (vec.length + 1)) ∗
        A.live ptr (cap.toNat * 4) 2 ∗ P) ⊢
      sortedSetPtOf A v { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗
        stackAt s.sp growOneStack ∗ P by
      rw [show ((ptr + BitVec.ofNat 64 (4 * insertIdx)) ↦₁₆ pt.x.value ∗
          (ptr + BitVec.ofNat 64 (4 * insertIdx) + 2#64) ↦₁₆ pt.y.value ∗
          ptSliceAt (ptr + BitVec.ofNat 64 (4 * insertIdx) + 4#64) (vec.drop insertIdx) ∗
          stackAt s.sp growOneStack ∗
          ptSliceAt ptr (vec.take insertIdx) ∗
          memRegion (ptr + BitVec.ofNat 64 ((vec.length + 1) * 4)) ((cap.toNat - (vec.length + 1)) * 4) ∗
          (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (vec.length + 1)) ∗
          A.live ptr (cap.toNat * 4) 2 ∗ P) =
        (((ptr + BitVec.ofNat 64 (4 * insertIdx)) ↦₁₆ pt.x.value ∗
          (ptr + BitVec.ofNat 64 (4 * insertIdx) + 2#64) ↦₁₆ pt.y.value ∗
          ptSliceAt (ptr + BitVec.ofNat 64 (4 * insertIdx) + 4#64) (vec.drop insertIdx) ∗
          ptSliceAt ptr (vec.take insertIdx) ∗
          memRegion (ptr + BitVec.ofNat 64 ((vec.length + 1) * 4)) ((cap.toNat - (vec.length + 1)) * 4) ∗
          (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (vec.length + 1)) ∗
          A.live ptr (cap.toNat * 4) 2) ∗
          (stackAt s.sp growOneStack ∗ P)) by ac_rfl]
      exact sepConj_mono_left hreasm) ?_
  apply hcont <;> simp [wp_norm, arm64_norm, *]

theorem bsearch_end_insert_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (v cap ptr lenOld : BitVec 64) (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx = vec.length) (hlt : vec.length < cap.toNat)
    (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_419).base + 368#64)
    (hstat : s.status = .Running)
    (hx14 : s.readReg64 .x14 = 1#64)
    (hx21 : s.readReg64 .x21 = v)
    (hx22 : s.readReg64 .x22 = ptr + BitVec.ofNat 64 (4 * insertIdx))
    (hx24 : s.readReg64 .x24 = pt.x.value.zeroExtend 64)
    (hx27 : s.readReg64 .x27 = pt.y.value.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 vec.length)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_419).base + 64#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x14 = 1#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
        ((blkPl_419).base + 64#64)
        sf
        (sortedSetPtOf A v { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗ P)
        post) :
    SepWP ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      ((blkPl_419).base + 64#64)
      s
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
        A.live ptr (cap.toNat * 4) 2 ∗
        ptSliceAt ptr vec ∗
        memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4) ∗ P)
      post := by
  subst hins
  rw [memRegion_spare_split_one ptr hlt hcap]
  wp_pull_exists
  wp_steps 5
  have htake_drop : vec.take vec.length ++ (pt :: vec.drop vec.length) = vec ++ [pt] := by
    rw [List.take_length, List.drop_length]
  have hreasm := reassemble_sortedSetPtOf_snoc A v cap ptr vec pt hlt hcap hptr
  rw [← htake_drop] at hreasm
  refine SepWP.weaken_pre
    (show ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (vec.length + 1)) ∗
        A.live ptr (cap.toNat * 4) 2 ∗
        ptSliceAt ptr vec ∗
        ((ptr + BitVec.ofNat 64 (4 * vec.length)) ↦₁₆ pt.x.value) ∗
        ((ptr + BitVec.ofNat 64 (4 * vec.length) + 2#64) ↦₁₆ pt.y.value) ∗
        memRegion (ptr + BitVec.ofNat 64 ((vec.length + 1) * 4)) ((cap.toNat - (vec.length + 1)) * 4) ∗ P) ⊢
      sortedSetPtOf A v { vec := vec.take vec.length ++ (pt :: vec.drop vec.length) } ∗ P by
      refine Entails.trans ?_ (sepConj_mono_left hreasm)
      exact Entails.of_eq (by ac_rfl)) ?_
  apply hcont <;> simp [wp_norm, arm64_norm, *]

theorem bsearch_to_296_placed_sepWP [LibsignalPlacement] {ext : String → Option (State → State)}
    {ptr : BitVec 64} {vec : List Pt} {xVal : BitVec 16}
    (h1 : 1 ≤ vec.length) (hlen : vec.length < 2 ^ 62)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_419).base + 236#64)
    (hstat : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx24 : s.readReg64 .x24 = xVal.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 vec.length)
    (hcont : ∀ (sf : State),
      sf.pc = (blkPl_419).base + 296#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x8 = ptr →
      sf.readReg64 .x9 = BitVec.ofNat 64 (bsearchLoop vec xVal 0 vec.length) →
      sf.readReg64 .x14 = s.readReg64 .x14 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      sf.readReg64 .x30 = s.readReg64 .x30 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
        ((blkPl_419).base + 296#64)
        sf (ptSliceAt ptr vec ∗ P) post) :
    SepWP ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      ((blkPl_419).base + 296#64)
      s (ptSliceAt ptr vec ∗ P) post := by
  have hloop := @bsearchLoop_placed_sepWP _ ext vec ptr xVal (by omega)
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
    · simp [wp_norm, arm64_norm, hx8]
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
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
  · simp only [heq1, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    wp_steps 2
    refine hloop vec.length 0 _ P post (by omega) (by omega)
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hstat])
      (by simp [wp_norm, arm64_norm, hx8])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx28])
      (by simp [wp_norm, arm64_norm, hx24])
      (fun sf hpc_f hstat_f hsp_f htr_f hx8_f hx9_f hx14_f hx19_f hx20_f hx21_f hx23_f hx24_f hx25_f hx27_f hx28_f hx29_f hx30_f hvregs_f => ?_)
    apply hcont sf hpc_f hstat_f
    · simpa [wp_norm, arm64_norm] using hsp_f
    · simpa [wp_norm, arm64_norm] using htr_f
    · exact hx8_f
    · exact hx9_f
    · simpa [wp_norm, arm64_norm] using hx14_f
    · simpa [wp_norm, arm64_norm] using hx19_f
    · simpa [wp_norm, arm64_norm] using hx20_f
    · simpa [wp_norm, arm64_norm] using hx21_f
    · simpa [wp_norm, arm64_norm] using hx23_f
    · simpa [wp_norm, arm64_norm] using hx24_f
    · simpa [wp_norm, arm64_norm] using hx25_f
    · simpa [wp_norm, arm64_norm] using hx27_f
    · simpa [wp_norm, arm64_norm] using hx28_f
    · simpa [wp_norm, arm64_norm] using hx29_f
    · simpa [wp_norm, arm64_norm] using hx30_f
    · simpa [wp_norm, arm64_norm] using hvregs_f

theorem bsearch_insert_at_336_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack))
    (v cap ptr lenOld : BitVec 64) (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx ≤ vec.length) (hlt : vec.length < cap.toNat)
    (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_419).base + 336#64)
    (hstat : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx14 : s.readReg64 .x14 = 1#64)
    (hx21 : s.readReg64 .x21 = v)
    (hx24 : s.readReg64 .x24 = pt.x.value.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 insertIdx)
    (hx27 : s.readReg64 .x27 = pt.y.value.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 vec.length)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_419).base + 64#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x14 = 1#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
        ((blkPl_419).base + 64#64)
        sf
        (sortedSetPtOf A v { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗
          stackAt s.sp growOneStack ∗ P)
        post) :
    SepWP ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      ((blkPl_419).base + 64#64)
      s
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
        A.live ptr (cap.toNat * 4) 2 ∗
        ptSliceAt ptr vec ∗
        memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4) ∗
        stackAt s.sp growOneStack ∗ P)
      post := by
  have hmem := @bsearch_memmove_insert_placed_sepWP _ A ext hmemmove_sat v cap ptr lenOld vec insertIdx pt
  have hend := @bsearch_end_insert_placed_sepWP _ A ext v cap ptr lenOld vec insertIdx pt
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
    refine hend hins_eq hlt hcap hptr _ (stackAt s.sp growOneStack ∗ P) post
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hstat])
      (by simp [wp_norm, arm64_norm, hx14])
      (by simp [wp_norm, arm64_norm, hx21])
      (by simp [wp_norm, arm64_norm, hx8, hx26, hlsl_ins])
      (by simp [wp_norm, arm64_norm, hx24])
      (by simp [wp_norm, arm64_norm, hx27])
      (by simp [wp_norm, arm64_norm, hx28])
      (fun sf hpc_f hstat_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_)
    apply hcont sf hpc_f hstat_f
    · simpa [wp_norm, arm64_norm] using hsp_f
    · simpa [wp_norm, arm64_norm] using htr_f
    · exact hx14_f
    · simpa [wp_norm, arm64_norm] using hx19_f
    · simpa [wp_norm, arm64_norm] using hx20_f
    · simpa [wp_norm, arm64_norm] using hx23_f
    · simpa [wp_norm, arm64_norm] using hx24_f
    · simpa [wp_norm, arm64_norm] using hx25_f
    · simpa [wp_norm, arm64_norm] using hx29_f
    · simpa [wp_norm, arm64_norm] using hvregs_f
  · have hle_f : ¬ vec.length ≤ insertIdx := by omega
    simp only [hle_f, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine hmem hins_lt hlt hcap hptr _ P post
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hstat])
      (by simpa [wp_norm, arm64_norm] using hsp_align)
      (by simp [wp_norm, arm64_norm, hx28, hx26, hsub_ins])
      (by simp [wp_norm, arm64_norm, hx21])
      (by simp [wp_norm, arm64_norm, hx8, hx26, hlsl_ins])
      (by simp [wp_norm, arm64_norm, hx24])
      (by simp [wp_norm, arm64_norm, hx27])
      (by simp [wp_norm, arm64_norm, hx28])
      (fun sf hpc_f hstat_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_)
    apply hcont sf hpc_f hstat_f
    · simpa [wp_norm, arm64_norm] using hsp_f
    · simpa [wp_norm, arm64_norm] using htr_f
    · exact hx14_f
    · simpa [wp_norm, arm64_norm] using hx19_f
    · simpa [wp_norm, arm64_norm] using hx20_f
    · simpa [wp_norm, arm64_norm] using hx23_f
    · simpa [wp_norm, arm64_norm] using hx24_f
    · simpa [wp_norm, arm64_norm] using hx25_f
    · simpa [wp_norm, arm64_norm] using hx29_f
    · simpa [wp_norm, arm64_norm] using hvregs_f

theorem bsearch_insert_at_452_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack))
    (v : BitVec 64) (vec : List Pt) (insertIdx : Nat) (pt : Pt)
    (hins : insertIdx ≤ vec.length)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_419).base + 452#64)
    (hstat : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = v)
    (hx24 : s.readReg64 .x24 = pt.x.value.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 insertIdx)
    (hx27 : s.readReg64 .x27 = pt.y.value.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 vec.length)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_419).base + 64#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x14 = 1#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
        ((blkPl_419).base + 64#64)
        sf
        (sortedSetPtOf A v { vec := vec.take insertIdx ++ (pt :: vec.drop insertIdx) } ∗
          stackAt s.sp growOneStack ∗ P)
        post) :
    SepWP ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      ((blkPl_419).base + 64#64)
      s
      (sortedSetPtGrownAt A v vec ∗ stackAt s.sp growOneStack ∗ P)
      post := by
  unfold sortedSetPtGrownAt
  wp_pull_exists
  rename_i cap ptr
  apply SepWP.focus_pure (by sep_focus)
  rintro ⟨hlt, hptr, hcap⟩
  have hmem := @bsearch_memmove_insert_placed_sepWP _ A ext hmemmove_sat v cap ptr (BitVec.ofNat 64 vec.length) vec insertIdx pt
  have hend := @bsearch_end_insert_placed_sepWP _ A ext v cap ptr (BitVec.ofNat 64 vec.length) vec insertIdx pt
  have hlsl_ins : (BitVec.ofNat 64 insertIdx) <<< 2 = BitVec.ofNat 64 (4 * insertIdx) :=
    bv64_lsl2_ofNat (by omega)
  have hsub_ins : BitVec.ofNat 64 vec.length - BitVec.ofNat 64 insertIdx =
      BitVec.ofNat 64 (vec.length - insertIdx) :=
    bv64_sub_ofNat hins (by omega)
  wp_steps 5
  rw [bv64_ult_ofNat (by omega) (by omega)]
  rcases Nat.eq_or_lt_of_le hins with hins_eq | hins_lt
  · have hlt_f : ¬ insertIdx < vec.length := by omega
    simp only [hlt_f, decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_steps 1
    refine hend hins_eq hlt hcap hptr _ (stackAt s.sp growOneStack ∗ P) post
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hstat])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hx21])
      (by simp [wp_norm, arm64_norm, hx26, hlsl_ins, hins_eq])
      (by simp [wp_norm, arm64_norm, hx24])
      (by simp [wp_norm, arm64_norm, hx27])
      (by simp [wp_norm, arm64_norm, hx28])
      (fun sf hpc_f hstat_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_)
    apply hcont sf hpc_f hstat_f
    · simpa [wp_norm, arm64_norm] using hsp_f
    · simpa [wp_norm, arm64_norm] using htr_f
    · exact hx14_f
    · simpa [wp_norm, arm64_norm] using hx19_f
    · simpa [wp_norm, arm64_norm] using hx20_f
    · simpa [wp_norm, arm64_norm] using hx23_f
    · simpa [wp_norm, arm64_norm] using hx24_f
    · simpa [wp_norm, arm64_norm] using hx25_f
    · simpa [wp_norm, arm64_norm] using hx29_f
    · simpa [wp_norm, arm64_norm] using hvregs_f
  · simp only [hins_lt, decide_true, ↓reduceIte]
    refine hmem hins_lt hlt hcap hptr _ P post
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hstat])
      (by simpa [wp_norm, arm64_norm] using hsp_align)
      (by simp [wp_norm, arm64_norm, hx28, hx26, hsub_ins])
      (by simp [wp_norm, arm64_norm, hx21])
      (by simp [wp_norm, arm64_norm, hx26, hlsl_ins])
      (by simp [wp_norm, arm64_norm, hx24])
      (by simp [wp_norm, arm64_norm, hx27])
      (by simp [wp_norm, arm64_norm, hx28])
      (fun sf hpc_f hstat_f hsp_f htr_f hx14_f hx19_f hx20_f hx23_f hx24_f hx25_f hx29_f hvregs_f => ?_)
    apply hcont sf hpc_f hstat_f
    · simpa [wp_norm, arm64_norm] using hsp_f
    · simpa [wp_norm, arm64_norm] using htr_f
    · exact hx14_f
    · simpa [wp_norm, arm64_norm] using hx19_f
    · simpa [wp_norm, arm64_norm] using hx20_f
    · simpa [wp_norm, arm64_norm] using hx23_f
    · simpa [wp_norm, arm64_norm] using hx24_f
    · simpa [wp_norm, arm64_norm] using hx25_f
    · simpa [wp_norm, arm64_norm] using hx29_f
    · simpa [wp_norm, arm64_norm] using hvregs_f

theorem call_grow_one_pt_full_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hgrow_full : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (growOnePtFullSpec A))
    {ret_pc target_pc : BitVec 64} {s0 s : State}
    {Q : State → SepProp → Prop} {R F : SepProp}
    (v cap ptr : BitVec 64) (vec : List Pt)
    (h1 : 1 ≤ vec.length) (hlen : vec.length ≤ 65536)
    (hcap_eq : cap.toNat = vec.length) (hptr : ptr ≠ 0#64)
    (hpc : s.pc = lsmpl.base 357)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = v)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s sf →
      SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc sf
        (sortedSetPtGrownAt A v vec ∗ A.pool ∗ stackAt s.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc s
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
        A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr vec ∗
        A.pool ∗ stackAt s.sp growOneStack ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) := by
  have hcap_ne0 : cap ≠ 0#64 := by
    intro hc0; subst hc0
    change 0 = vec.length at hcap_eq; omega
  have hbs_len : (ptListBytes vec).length = cap.toNat * 4 := by
    rw [ptListBytes_length, hcap_eq, Nat.mul_comm]
  have hmax_bound : max (2 * cap.toNat) 4 * 4 + 2 ≤ 2 ^ 63 := by omega
  refine SepWPp.call (x := (v, cap, ptr, ptListBytes vec))
    (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗ F)
    hgrow_full hpc hrun hsp hlr ?_ ?_ ?_ ?_
  · intro R' hm
    simp only [growOnePtFullSpec, growOneStrideFullSpec, hcap_ne0, ↓reduceIte,
      hbs_len, ← ptSliceAt_eq_pointsToBytes, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, trivial, hptr, hmax_bound⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [growOnePtFullSpec, growOneStrideFullSpec, addChunkOnPanic] at hm ⊢
    exact allowPanic_frame (allocFailedIn_of_trace_eq htr) hm
  · intro sf hpc_f hrun_f hsp_f hcs_f
    simp only [growOnePtFullSpec, growOneStrideFullSpec, sepConj_assoc]
    apply SepWPp.pure_elim
    intro htr_f
    have hgrown := growOnePtFull_post_entails_grown A v cap vec h1 hcap_eq hlen
    refine SepWPp.weaken_pre ?_ (hnext sf hpc_f hrun_f hsp_f (htr_f.trans htr) hcs_f)
    rw [show (∃∗ p' : BitVec 64,
        ⌜p' ≠ 0#64 ∧ p'.toNat % 2 = 0⌝ ∗
        (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' (max (2 * cap.toNat) 4 * 4) 2 ∗ (p' ↦ₛ ptListBytes vec) ∗
        memRegion (p' + BitVec.ofNat 64 (ptListBytes vec).length) ((max (2 * cap.toNat) 4 - cap.toNat) * 4)) ∗
        A.pool ∗ stackAt s.sp growOneStack ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗ F =
      ((∃∗ p' : BitVec 64,
        ⌜p' ≠ 0#64 ∧ p'.toNat % 2 = 0⌝ ∗
        (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' (max (2 * cap.toNat) 4 * 4) 2 ∗ (p' ↦ₛ ptListBytes vec) ∗
        memRegion (p' + BitVec.ofNat 64 (ptListBytes vec).length) ((max (2 * cap.toNat) 4 - cap.toNat) * 4)) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length)) ∗
        (A.pool ∗ stackAt s.sp growOneStack ∗ F) by ac_rfl]
    exact sepConj_mono_left hgrown

theorem call_grow_one_pt_empty_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hgrow_empty : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (growOnePtSpec A))
    {ret_pc target_pc : BitVec 64} {s0 s : State}
    {Q : State → SepProp → Prop} {R F : SepProp}
    (v ptr lenOld : BitVec 64) (hptr : ptr ≠ 0#64)
    (hpc : s.pc = lsmpl.base 357)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = v)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hnext : ∀ (sf : State) (p' : BitVec 64),
      p' ≠ 0#64 →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s sf →
      SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc sf
        ((v ↦₆₄ 4#64) ∗ ((v + 8#64) ↦₆₄ p') ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
          A.live p' 16 2 ∗ memRegion p' 16 ∗
          A.pool ∗ stackAt s.sp growOneStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext)) target_pc s
      ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
        A.pool ∗ stackAt s.sp growOneStack ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ addChunkOnPanic s0 sf ∗ R)) := by
  have hmax_bound : max (2 * (0#64 : BitVec 64).toNat) 4 * 4 + 2 ≤ 2 ^ 63 := by decide
  refine SepWPp.call (x := (v, 0#64, ptr))
    (F := ((v + 16#64) ↦₆₄ lenOld) ∗ F)
    hgrow_empty hpc hrun hsp hlr ?_ ?_ ?_ ?_
  · intro R' hm
    simp only [growOnePtSpec, growOneStrideEmptySpec, ↓reduceIte, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hptr, hmax_bound⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [growOnePtSpec, growOneStrideEmptySpec, addChunkOnPanic] at hm ⊢
    exact allowPanic_frame (allocFailedIn_of_trace_eq htr) hm
  · intro sf hpc_f hrun_f hsp_f hcs_f
    have hmax0 : max (2 * (0#64 : BitVec 64).toNat) 4 = 4 := rfl
    simp only [growOnePtSpec, growOneStrideEmptySpec, hmax0,
      sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.pure_elim; intro htr_f
    apply SepWPp.exists_elim; intro p'
    apply SepWPp.pure_elim; rintro ⟨hp', _⟩
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sf p' hp' hpc_f hrun_f hsp_f (htr_f.trans htr) hcs_f)

theorem bsearch_push_empty_at_216_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (v cap ptr lenOld : BitVec 64) (pt : Pt)
    (hlt : 0 < cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (blkPl_419).base + 216#64)
    (hstat : s.status = .Running)
    (hx14 : s.readReg64 .x14 = 1#64) (hx21 : s.readReg64 .x21 = v)
    (hx24 : s.readReg64 .x24 = pt.x.value.zeroExtend 64) (hx27 : s.readReg64 .x27 = pt.y.value.zeroExtend 64)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_419).base + 64#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      sf.readReg64 .x14 = 1#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
        ((blkPl_419).base + 64#64)
        sf
        (sortedSetPtOf A v { vec := [pt] } ∗ P)
        post) :
    SepWP ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      ((blkPl_419).base + 64#64)
      s
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ lenOld) ∗
        A.live ptr (cap.toNat * 4) 2 ∗
        memRegion ptr (cap.toNat * 4) ∗ P)
      post := by
  have hsplit := memRegion_spare_split_one ptr (len := 0) hlt hcap
  simp only [Nat.mul_zero, Nat.zero_mul, Nat.sub_zero,
    BitVec.add_zero, Nat.zero_add] at hsplit
  rw [hsplit]
  wp_pull_exists
  rename_i v1 v0
  wp_steps 5
  have hreasm := reassemble_sortedSetPtOf_snoc A v cap ptr [] pt hlt hcap hptr
  unfold ptSliceAt arrayAt at hreasm
  simp only [List.length_nil, Nat.mul_zero, BitVec.add_zero,
    Nat.zero_add, List.nil_append, emp_sepConj] at hreasm
  refine SepWP.weaken_pre (P' := sortedSetPtOf A v { vec := [pt] } ∗ P)
    (by refine Entails.trans ?_ (sepConj_mono_left hreasm)
        exact Entails.of_eq (by ac_rfl)) ?_
  apply hcont <;> simp [wp_norm, arm64_norm, hstat, hx14]

theorem rev16_64_pair (a b : BitVec 8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (rev16_64 (BitVec.zeroExtend 64 (b ++ a)))) =
      BitVec.zeroExtend 64 ((a.zeroExtend 16 <<< 8) + b.zeroExtend 16) := by
  have h1 : BitVec.setWidth 64 (BitVec.setWidth 32 (rev16_64 (BitVec.zeroExtend 64 (b ++ a)))) =
      BitVec.zeroExtend 64 ((a.zeroExtend 16 <<< 8) ||| b.zeroExtend 16) := by
    unfold rev16_64; bv_slice
  rw [h1]; congr 1; bv_kernel

theorem stackAt_addChunk_split (sp : BitVec 64) :
    stackAt sp addChunkStack =
      stackAt (sp - 96#64) growOneStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
         ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
          ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
          ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
          ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗ ((sp - 32#64) ↦₆₄ v8) ∗
          ((sp - 24#64) ↦₆₄ v9) ∗ ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
  have h1 := ProofLib.stackAt_split_cells sp 4208 12 (by decide)
  change stackAt sp addChunkStack = stackAt (sp - 96#64) growOneStack ∗ cells (sp - 96#64) 12 at h1
  rw [h1]; congr 1; cells_unfold

theorem addChunkBsearchLoop_props (chunk : Chunk) :
    ∀ (rem i : Nat) (self : PolyDecoder),
      (addChunkBsearchLoop chunk i rem self).pts.length = self.pts.length ∧
      (addChunkBsearchLoop chunk i rem self).ptsNeeded = self.ptsNeeded ∧
      (addChunkBsearchLoop chunk i rem self).isComplete = self.isComplete
  | 0, _, _ => ⟨rfl, rfl, rfl⟩
  | rem + 1, i, self => by
    obtain ⟨h1, h2, h3⟩ := addChunkBsearchLoop_props chunk rem (i + 1) (addChunkBsearchStep chunk i self)
    exact ⟨h1.trans (addChunkBsearchStep_pts_length chunk i self),
      h2.trans (addChunkBsearchStep_ptsNeeded chunk i self),
      h3.trans (addChunkBsearchStep_isComplete chunk i self)⟩

theorem addChunkBsearch_pts_length (self : PolyDecoder) (chunk : Chunk) :
    (addChunkBsearch self chunk).pts.length = self.pts.length := (addChunkBsearchLoop_props chunk 16 0 self).1
theorem addChunkBsearch_ptsNeeded (self : PolyDecoder) (chunk : Chunk) :
    (addChunkBsearch self chunk).ptsNeeded = self.ptsNeeded := (addChunkBsearchLoop_props chunk 16 0 self).2.1
theorem addChunkBsearch_isComplete (self : PolyDecoder) (chunk : Chunk) :
    (addChunkBsearch self chunk).isComplete = self.isComplete := (addChunkBsearchLoop_props chunk 16 0 self).2.2

end CryptoVerification.SpqrV1.Poly.AddChunk
