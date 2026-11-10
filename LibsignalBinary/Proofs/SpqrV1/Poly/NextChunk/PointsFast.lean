/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Epilogue
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk`: `EncoderState::Points` Fast Path

Verifies the `EncoderState::Points` fast path (`0x6a3e0..0x6a534`) when
`(x.enc.idx.setWidth 16).toNat < pts[i].value.length` for all `i < 16`, composing the setup block,
16-iteration point-indexing loop, prologue, and epilogue.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Alloc
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

attribute [local simp, local arm64_norm, local wp_norm]
  polyEncoderTagOff polyEncoderVecsOff polyEncoderVecsSize
  polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  polyEncoderPointsTag polyEncoderPolysTag
  chunkDataOff chunkIndexOff chunkSize

/-! ## 1. Local Frame Split for `[fsp + 48]`, `[fsp + 88]`, `[fsp + 104]` -/

@[simp, arm64_norm, wp_norm] theorem sp_sub_1200_add_48 (sp : BitVec 64) :
    (sp - 1200#64) + 48#64 = sp - 1152#64 := by bv_omega
@[simp, arm64_norm, wp_norm] theorem sp_sub_1200_add_48' (sp : BitVec 64) :
    48#64 + (sp - 1200#64) = sp - 1152#64 := by bv_omega
@[simp, arm64_norm, wp_norm] theorem sp_sub_1200_add_88 (sp : BitVec 64) :
    (sp - 1200#64) + 88#64 = sp - 1112#64 := by bv_omega
@[simp, arm64_norm, wp_norm] theorem sp_sub_1200_add_88' (sp : BitVec 64) :
    88#64 + (sp - 1200#64) = sp - 1112#64 := by bv_omega
@[simp, arm64_norm, wp_norm] theorem sp_sub_1200_add_104 (sp : BitVec 64) :
    (sp - 1200#64) + 104#64 = sp - 1096#64 := by bv_omega
@[simp, arm64_norm, wp_norm] theorem sp_sub_1200_add_104' (sp : BitVec 64) :
    104#64 + (sp - 1200#64) = sp - 1096#64 := by bv_omega

/-- Rest of the local stack frame during the `0x6a460..0x6a534` loop, after splitting out
    `[fsp + 48]` (`#0x30`), `[fsp + 88]` (`#0x58`), and `[fsp + 104]` (`#0x68`). -/
def localFramePointsRest (fsp : BitVec 64) : SepProp :=
  memRegion fsp 48 ∗
  memRegion (fsp + 64#64) 24 ∗
  memRegion (fsp + 96#64) 8 ∗
  memRegion (fsp + 112#64) 120 ∗
  memRegion (fsp + 256#64) 848

theorem localFrameRest_unfold_points (fsp : BitVec 64) :
    localFrameRest fsp ⊢
      ∃∗ u48 : BitVec 64, ∃∗ u88 : BitVec 64, ∃∗ u104 : BitVec 64,
        ((fsp + 48#64) ↦₆₄ u48) ∗
        ((fsp + 88#64) ↦₆₄ u88) ∗
        ((fsp + 104#64) ↦₆₄ u104) ∗
        localFramePointsRest fsp := by
  unfold localFrameRest localFramePointsRest
  rw [ProofLib.memRegion_split' (b := fsp) (n := 48) (k := 8) (b' := fsp + 48#64)
        rfl rfl (by decide),
      ProofLib.memRegion_eight (fsp + 48#64),
      ProofLib.memRegion_split' (b := fsp + 64#64) (n := 24) (k := 144) (b' := fsp + 88#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 88#64) (n := 8) (k := 136) (b' := fsp + 96#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 88#64),
      ProofLib.memRegion_split' (b := fsp + 96#64) (n := 8) (k := 128) (b' := fsp + 104#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 104#64) (n := 8) (k := 120) (b' := fsp + 112#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 104#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u104
  apply Entails.sepExists_elim; intro u88
  apply Entails.sepExists_elim; intro u48
  exact Entails.sepExists_right u48
    (Entails.sepExists_right u88
      (Entails.sepExists_right u104 (Entails.of_eq (by ac_rfl))))

theorem localFrameRest_fold_points (fsp u48 u88 u104 : BitVec 64) :
    ((fsp + 48#64) ↦₆₄ u48) ∗
      ((fsp + 88#64) ↦₆₄ u88) ∗
      ((fsp + 104#64) ↦₆₄ u104) ∗
      localFramePointsRest fsp ⊢
      localFrameRest fsp := by
  unfold localFrameRest localFramePointsRest
  rw [ProofLib.memRegion_split' (b := fsp) (n := 48) (k := 8) (b' := fsp + 48#64)
        rfl rfl (by decide),
      ProofLib.memRegion_eight (fsp + 48#64),
      ProofLib.memRegion_split' (b := fsp + 64#64) (n := 24) (k := 144) (b' := fsp + 88#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 88#64) (n := 8) (k := 136) (b' := fsp + 96#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 88#64),
      ProofLib.memRegion_split' (b := fsp + 96#64) (n := 8) (k := 128) (b' := fsp + 104#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 104#64) (n := 8) (k := 120) (b' := fsp + 112#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 104#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_right u104
  apply Entails.sepExists_right u88
  apply Entails.sepExists_right u48
  exact Entails.of_eq (by ac_rfl)

/-! ## 2. `pointOf`, `pointListOf`, and `gf16SliceAt` Splitting Helpers -/

theorem pointListOf_split_idx (A : RustAlloc) (base : BitVec 64)
    (pts : List Point) (i : Nat) (hi : i < pts.length) :
    pointListOf A base pts =
      (pointListOf A base (pts.take i) ∗
        pointOf A (base + BitVec.ofNat 64 (24 * i)) (pts[i]'hi) ∗
        pointListOf A (base + BitVec.ofNat 64 (24 * (i + 1))) (pts.drop (i + 1))) := by
  unfold pointListOf
  conv => lhs; rw [← List.take_append_drop i pts]
  rw [arrayAt_append, List.length_take_of_le (by omega), List.drop_eq_getElem_cons hi]
  simp only [arrayAt, vecHeaderBytes]
  have haddr : (base + BitVec.ofNat 64 (24 * i)) + BitVec.ofNat 64 24 =
      base + BitVec.ofNat 64 (24 * (i + 1)) := by
    have hm : 24 * i + 24 = 24 * (i + 1) := by omega
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hm]
  rw [haddr]

theorem gf16SliceAt_split_idx (ptr : BitVec 64) (xs : List GF16)
    (j : Nat) (hj : j < xs.length) :
    gf16SliceAt ptr xs =
      (gf16SliceAt ptr (xs.take j) ∗
        ((ptr + BitVec.ofNat 64 (2 * j)) ↦₁₆ (xs[j]'hj).value) ∗
        gf16SliceAt (ptr + BitVec.ofNat 64 (2 * (j + 1))) (xs.drop (j + 1))) := by
  unfold gf16SliceAt
  conv => lhs; rw [← List.take_append_drop j xs]
  rw [arrayAt_append, List.length_take_of_le (by omega), List.drop_eq_getElem_cons hj]
  simp only [arrayAt, gf16Stride, gf16At]
  have haddr : (ptr + BitVec.ofNat 64 (2 * j)) + BitVec.ofNat 64 2 =
      ptr + BitVec.ofNat 64 (2 * (j + 1)) := by
    have hm : 2 * j + 2 = 2 * (j + 1) := by omega
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hm]
  rw [haddr]

/-- Spare-capacity and allocator-liveness portion of `pointOf`'s buffer. -/
def pointBufRest (A : RustAlloc) (cap ptr : BitVec 64) (pt : Point) : SepProp :=
  if cap = 0 then emp
  else A.live ptr (cap.toNat * gf16Stride) gf16Align ∗
    memRegion (ptr + BitVec.ofNat 64 (pt.value.length * gf16Stride))
      ((cap.toNat - pt.value.length) * gf16Stride)

theorem pointBufBody_eq_slice_rest (A : RustAlloc) (cap ptr : BitVec 64)
    (pt : Point) (hlen : pt.value.length ≤ cap.toNat) :
    (if cap = 0 then emp
     else A.live ptr (cap.toNat * gf16Stride) gf16Align ∗
       arrayAt gf16At gf16Stride ptr pt.value ∗
       memRegion (ptr + BitVec.ofNat 64 (pt.value.length * gf16Stride))
         ((cap.toNat - pt.value.length) * gf16Stride)) =
      (gf16SliceAt ptr pt.value ∗ pointBufRest A cap ptr pt) := by
  unfold pointBufRest gf16SliceAt
  by_cases h0 : cap = 0
  · have hcap0 : cap.toNat = 0 := by subst h0; rfl
    have hlen0 : pt.value.length = 0 := by omega
    have hnil : pt.value = [] := List.eq_nil_of_length_eq_zero hlen0
    simp [h0, hnil, arrayAt]
  · simp only [h0, ↓reduceIte]
    ac_rfl

theorem pointOf_unfold (A : RustAlloc) (v : BitVec 64) (pt : Point) :
    pointOf A v pt ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
        ⌜pt.value.length ≤ cap.toNat ∧ cap.toNat * gf16Stride < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * gf16Stride) gf16Align ∗
           arrayAt gf16At gf16Stride ptr pt.value ∗
           memRegion (ptr + BitVec.ofNat 64 (pt.value.length * gf16Stride))
             ((cap.toNat - pt.value.length) * gf16Stride)) := by
  unfold pointOf vecOf vecAt vecHeader vecBuf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.of_eq (by ac_rfl)))

theorem pointOf_fold (A : RustAlloc) (v cap ptr : BitVec 64) (pt : Point)
    (hbounds : pt.value.length ≤ cap.toNat ∧ cap.toNat * gf16Stride < 2 ^ 63 ∧ ptr ≠ 0) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
      gf16SliceAt ptr pt.value ∗
      pointBufRest A cap ptr pt ⊢
      pointOf A v pt := by
  have htrue : (pt.value.length ≤ cap.toNat ∧ cap.toNat * gf16Stride < 2 ^ 63 ∧ ptr ≠ 0) = True :=
    propext ⟨fun _ => trivial, fun _ => hbounds⟩
  unfold pointOf vecOf vecAt vecHeader vecBuf
  apply Entails.sepExists_right cap
  apply Entails.sepExists_right ptr
  rw [htrue, pure_true, emp_sepConj, pointBufBody_eq_slice_rest A cap ptr pt hbounds.1]
  exact Entails.of_eq (by ac_rfl)

theorem pointValue_len_lt_two_pow_63 {len cap : Nat}
    (hlen : len ≤ cap) (hcap : cap * gf16Stride < 2 ^ 63) :
    len < 2 ^ 63 := by
  dsimp [gf16Stride] at hcap
  omega

/-! ## 3. Arithmetic and Bitvector Normalization for the `Points` Fast Path -/

@[local simp, local arm64_norm, local wp_norm]
theorem madd_24_eq (base : BitVec 64) (i : Nat) :
    base + BitVec.ofNat 64 i * 24#64 = base + BitVec.ofNat 64 (24 * i) := by
  have hm : BitVec.ofNat 64 i * 24#64 = BitVec.ofNat 64 (24 * i) := by
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  rw [hm]

@[local simp, local arm64_norm, local wp_norm]
theorem madd_24_eq' (base : BitVec 64) (i : Nat) :
    BitVec.ofNat 64 i * 24#64 + base = base + BitVec.ofNat 64 (24 * i) := by
  rw [BitVec.add_comm, madd_24_eq]

@[local simp, local arm64_norm, local wp_norm]
theorem zext16_shl1_bv_eq (idx16 : BitVec 16) :
    (idx16.setWidth 64) <<< 1#64 = BitVec.ofNat 64 (2 * idx16.toNat) := by
  have h1 : (idx16.setWidth 64) <<< 1#64 = 2#64 * (idx16.setWidth 64) := by
    bv_slice
  have h2 : (idx16.setWidth 64) = BitVec.ofNat 64 idx16.toNat := by
    apply BitVec.eq_of_toNat_eq
    have hlt : idx16.toNat < 2 ^ 64 := Nat.lt_trans idx16.isLt (by decide : 2 ^ 16 < 2 ^ 64)
    simp [Nat.mod_eq_of_lt hlt]
  rw [h1, h2, ← BitVec.ofNat_mul]

@[local simp, local arm64_norm, local wp_norm]
theorem zext16_shl1_nat_eq (idx16 : BitVec 16) :
    (idx16.setWidth 64) <<< 1 = BitVec.ofNat 64 (2 * idx16.toNat) :=
  zext16_shl1_bv_eq idx16

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_add_one_eq (i : Nat) :
    BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
  rw [BitVec.ofNat_add]

attribute [local simp, local arm64_norm, local wp_norm]
  ofNat_two_mul_add_one ofNat_two_mul_add_two

theorem cmp_len_idx_gt {len : Nat} {idx16 : BitVec 16}
    (hlt : idx16.toNat < len) (hlen : len < 2 ^ 63) :
    BitVec.ult (BitVec.ofNat 64 len) (idx16.setWidth 64) = false ∧
    BitVec.ule (BitVec.ofNat 64 len) (idx16.setWidth 64) = false ∧
    (BitVec.ofNat 64 len == idx16.setWidth 64) = false ∧
    (BitVec.ofNat 64 len - idx16.setWidth 64 == 0#64) = false := by
  have hlen64 : len < 2 ^ 64 := Nat.lt_trans hlen (by decide : 2 ^ 63 < 2 ^ 64)
  have hidx64 : idx16.toNat < 2 ^ 64 := Nat.lt_trans idx16.isLt (by decide : 2 ^ 16 < 2 ^ 64)
  have hlen_mod : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hlen64
  have hidx_mod : (idx16.setWidth 64).toNat = idx16.toNat := by
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt hidx64
  have hne : BitVec.ofNat 64 len ≠ idx16.setWidth 64 := by
    intro h
    have h2 := congrArg BitVec.toNat h
    omega
  have hsub : BitVec.ofNat 64 len - idx16.setWidth 64 ≠ 0#64 := by
    intro h
    exact hne (by revert h; bv_omega)
  refine ⟨?_, ?_, beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr hsub⟩
  · simp [BitVec.ult, hlen_mod, hidx_mod]; omega
  · simp [BitVec.ule, hlen_mod, hidx_mod]; omega

theorem ofNat_add_one_beq_16 {i : Nat} (hi : i < 16) :
    (BitVec.ofNat 64 (i + 1) == 16#64) = (i == 15) ∧
    (BitVec.ofNat 64 (i + 1) - 16#64 == 0#64) = (i == 15) := by
  by_cases h15 : i = 15
  · subst h15; decide
  · have hlt : i + 1 < 16 := by omega
    have h16 : (16#64 : BitVec 64) = BitVec.ofNat 64 16 := rfl
    rw [h16]
    rcases ofNat_beq_false_of_lt (a := i + 1) (b := 16) hlt (by omega) with ⟨h1, h2, _, _⟩
    have hi15 : (i == 15) = false := beq_eq_false_iff_ne.mpr h15
    rw [h1, h2, hi15]
    exact ⟨rfl, rfl⟩

@[local simp, local arm64_norm, local wp_norm]
theorem lsr8_zext16_eq (v : BitVec 16) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 v >>> 8) =
      BitVec.setWidth 8 (v >>> 8) := by
  bv_slice

@[local simp, local arm64_norm, local wp_norm]
theorem trunc8_zext16_eq (v : BitVec 16) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 v) = BitVec.setWidth 8 v := by
  bv_slice

theorem chunkPointsBytes_add (idx : BitVec 16) (pts : List Point) :
    ∀ (m k n : Nat),
      chunkPointsBytes idx pts k (m + n) =
        chunkPointsBytes idx pts k m ++ chunkPointsBytes idx pts (k + m) n
  | 0, k, n => by simp [chunkPointsBytes]
  | m + 1, k, n => by
    have hadd : m + 1 + n = (m + n) + 1 := by omega
    have hk : k + (m + 1) = (k + 1) + m := by omega
    rw [hadd]
    conv => lhs; unfold chunkPointsBytes
    conv => rhs; arg 1; unfold chunkPointsBytes
    rw [chunkPointsBytes_add idx pts m (k + 1) n, hk]
    simp only [List.cons_append]

theorem chunkPointsBytes_zero_succ (idx : BitVec 16) (pts : List Point)
    (i : Nat) (hi : i < pts.length) (hidx : idx.toNat < (pts[i]'hi).value.length) :
    chunkPointsBytes idx pts 0 (i + 1) =
      chunkPointsBytes idx pts 0 i ++
        [BitVec.setWidth 8 (((pts[i]'hi).value[idx.toNat]'hidx).value >>> 8),
         BitVec.setWidth 8 ((pts[i]'hi).value[idx.toNat]'hidx).value] := by
  rw [chunkPointsBytes_add idx pts i 0 1, Nat.zero_add]
  have hpt : pts[i]? = some (pts[i]'hi) := List.getElem?_eq_getElem hi
  have hg : (pts[i]'hi).value[idx.toNat]? = some ((pts[i]'hi).value[idx.toNat]'hidx) :=
    List.getElem?_eq_getElem hidx
  simp [chunkPointsBytes, hpt, hg]

/-! ## 4. Single Iteration of the `Points` Fast-Path Loop (`0x6a4a4..0x6a534 -> 0x6a4e0..0x6a4f8 -> 0x6a480..0x6a4a0`) -/

set_option maxHeartbeats 1600000 in
theorem pointsFastLoop_step_sepWPp
    (A : RustAlloc) (b : BitVec 64) (ext : String → Option (State → State))
    (x : PolyNextChunkGhost) (pts : List Point) (hlen_pts : pts.length = 16)
    (out_ptr : BitVec 64) (R : SepProp)
    {Q : State → SepProp → Prop}
    (i : Nat) (hi16 : i < 16)
    (hidx_lt : (x.enc.idx.setWidth 16).toNat < (pts[i]'(by omega)).value.length)
    (u104 : BitVec 64)
    (s0 s : State) (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 288#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1200#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 i)
    (hx19 : s.readReg64 .x19 = x.encA + 8#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (2 * i))
    (hx21 : s.readReg64 .x21 = 0#64)
    (hx24 : s.readReg64 .x24 = x.encA)
    (hx27 : s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hnext : ∀ sf : State,
      sf.pc = (if i == 15 then
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4484#64
      else
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 288#64) →
      sf.status = .Running →
      sf.sp = s0.sp - 1200#64 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.readReg64 .x9 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x19 = x.encA + 8#64 →
      sf.readReg64 .x20 = BitVec.ofNat 64 (2 * (i + 1)) →
      sf.readReg64 .x21 = 0#64 →
      sf.readReg64 .x24 = x.encA →
      sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      sf.readReg64 .x28 = 24#64 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 .lr) sf
        ((out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 (i + 1)) ∗
          memRegion (out_ptr + BitVec.ofNat 64 (2 * (i + 1))) (32 - 2 * (i + 1)) ∗
          A.live out_ptr 32 1 ∗
          memRegion x.outA chunkSize ∗
          (x.encA ↦₆₄ polyEncoderPointsTag) ∗
          pointListOf A (x.encA + 8#64) pts ∗
          ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
          memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
          (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗
          (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
          (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
          (((s0.sp - 1200#64) + 104#64) ↦₆₄ BitVec.ofNat 64 i) ∗
          (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
          (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
          (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * (i + 1))) ∗
          localFramePointsRest (s0.sp - 1200#64) ∗
          savedCells s0 ∗
          tokenInitAt b ∗
          reduceTableAt b ∗
          A.pool ∗
          stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 .lr) s
      ((out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ∗
        A.live out_ptr 32 1 ∗
        memRegion x.outA chunkSize ∗
        (x.encA ↦₆₄ polyEncoderPointsTag) ∗
        pointListOf A (x.encA + 8#64) pts ∗
        ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
        memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
        (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗
        (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
        (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
        (((s0.sp - 1200#64) + 104#64) ↦₆₄ u104) ∗
        (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
        (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
        (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
        localFramePointsRest (s0.sp - 1200#64) ∗
        savedCells s0 ∗
        tokenInitAt b ∗
        reduceTableAt b ∗
        A.pool ∗
        stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hi_len : i < pts.length := by omega
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xfc 68
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x15c 92
  rw [pointListOf_split_idx A (x.encA + 8#64) pts i hi_len]
  apply SepWPp.fold (pointOf_unfold A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (pts[i]'hi_len))
    (by sep_focus)
  simp only [sepExists_sepConj_left]
  apply sepWPp_exists_left; intro cap
  apply sepWPp_exists_left; intro ptr
  have hpure_pull : ∀ (P_c P_p P_l : SepProp) (φ : Prop) (P_body Rest : SepProp),
      (P_c ∗ P_p ∗ P_l ∗ ⌜φ⌝ ∗ P_body) ∗ Rest = ⌜φ⌝ ∗ ((P_c ∗ P_p ∗ P_l ∗ P_body) ∗ Rest) := by
    intros; ac_rfl
  rw [hpure_pull]
  apply SepWPp.pure_left; rintro ⟨hlen_cap, hcap_bound, hptr_ne⟩
  rw [pointBufBody_eq_slice_rest A cap ptr (pts[i]'hi_len) hlen_cap,
      gf16SliceAt_split_idx ptr (pts[i]'hi_len).value (x.enc.idx.setWidth 16).toNat hidx_lt]
  have hlen_lt : (pts[i]'hi_len).value.length < 2 ^ 63 :=
    pointValue_len_lt_two_pow_63 hlen_cap hcap_bound
  rcases cmp_len_idx_gt (idx16 := x.enc.idx.setWidth 16) hidx_lt hlen_lt with
    ⟨hult_len, hule_len, hbeq_len, hsub_len⟩
  rcases ofNat_beq_false_of_lt (a := 2 * i) (b := 32) (by omega) (by omega) with
    ⟨hcmp1_eq, hcmp1_sub, _, _⟩
  rcases ofNat_beq_false_of_lt (a := 2 * i + 1) (b := 32) (by omega) (by omega) with
    ⟨hcmp2_eq, hcmp2_sub, _, _⟩
  rcases ofNat_add_one_beq_16 hi16 with ⟨hcmp16_eq, hcmp16_sub⟩
  have h32_eq : (32#64 : BitVec 64) = BitVec.ofNat 64 32 := rfl
  rw [← h32_eq] at hcmp1_eq hcmp1_sub hcmp2_eq hcmp2_sub
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := if i == 15 then entry + 4484#64 else entry + 288#64)
  apply SepWP.fold (memRegion_split_two_bytes out_ptr i hi16) (by sep_focus)
  apply sepWP_exists_left_sep; intro b0
  apply sepWP_exists_left_sep; intro b1
  wp_steps 30
  have hfold_bytes :
      (out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i)) ↦₈
          BitVec.setWidth 8 (((pts[i]'hi_len).value[(x.enc.idx.setWidth 16).toNat]'hidx_lt).value >>> 8)) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i + 1)) ↦₈
          BitVec.setWidth 8 ((pts[i]'hi_len).value[(x.enc.idx.setWidth 16).toNat]'hidx_lt).value) ⊢
        (out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 (i + 1)) := by
    rw [chunkPointsBytes_zero_succ (x.enc.idx.setWidth 16) pts i hi_len hidx_lt]
    exact pointsToBytes_append_two_bytes out_ptr
      (chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i) i
      (chunkPointsBytes_length (x.enc.idx.setWidth 16) pts 0 i) _ _
  apply SepWP.fold hfold_bytes (by sep_focus)
  have hfold_slice :
      gf16SliceAt ptr ((pts[i]'hi_len).value.take (x.enc.idx.setWidth 16).toNat) ∗
        ((ptr + BitVec.ofNat 64 (2 * (x.enc.idx.setWidth 16).toNat)) ↦₁₆
          ((pts[i]'hi_len).value[(x.enc.idx.setWidth 16).toNat]'hidx_lt).value) ∗
        gf16SliceAt (ptr + BitVec.ofNat 64 (2 * ((x.enc.idx.setWidth 16).toNat + 1)))
          ((pts[i]'hi_len).value.drop ((x.enc.idx.setWidth 16).toNat + 1)) ⊢
        gf16SliceAt ptr (pts[i]'hi_len).value := by
    rw [← gf16SliceAt_split_idx ptr (pts[i]'hi_len).value (x.enc.idx.setWidth 16).toNat hidx_lt]
    exact Entails.refl _
  apply SepWP.fold hfold_slice (by sep_focus)
  have hfold_point :
      (((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap) ∗
        ((((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr) ∗
        ((((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄
          BitVec.ofNat 64 (pts[i]'hi_len).value.length) ∗
        gf16SliceAt ptr (pts[i]'hi_len).value ∗
        pointBufRest A cap ptr (pts[i]'hi_len) ⊢
        pointOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (pts[i]'hi_len) :=
    pointOf_fold A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) cap ptr (pts[i]'hi_len)
      ⟨hlen_cap, hcap_bound, hptr_ne⟩
  apply SepWP.fold hfold_point (by sep_focus)
  have hfold_list :
      pointListOf A (x.encA + 8#64) (pts.take i) ∗
        pointOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (pts[i]'hi_len) ∗
        pointListOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * (i + 1))) (pts.drop (i + 1)) ⊢
        pointListOf A (x.encA + 8#64) pts := by
    rw [← pointListOf_split_idx A (x.encA + 8#64) pts i hi_len]
    exact Entails.refl _
  apply SepWP.fold hfold_list (by sep_focus)
  apply SepWP.done
  · simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
      hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hcmp16_eq, hcmp16_sub]
  · wp_norm_lhs
  · refine SepWPp.weaken_pre (Entails.of_eq (by simp only [arm64_norm]; ac_rfl))
      (hnext _ ?_ (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp)
        (by simpa [arm64_norm, wp_norm] using htr)
        (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hvregs])
        (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub])
        (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub])
        (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub])
        (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub])
        (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hx24])
        (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hx27])
        (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hx28]))
    simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
      hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hcmp16_eq, hcmp16_sub]

/-! ## 5. Full 16-Iteration `Points` Fast-Path Loop and `nextChunk_points_fast_sepWPp` -/

theorem pointsFastLoop_sepWPp
    (A : RustAlloc) (b : BitVec 64) (ext : String → Option (State → State))
    (x : PolyNextChunkGhost) (pts : List Point) (hlen_pts : pts.length = 16)
    (out_ptr : BitVec 64) (R : SepProp)
    {Q : State → SepProp → Prop}
    (rem i : Nat) (hrem_eq : i + (rem + 1) = 16)
    (hfast : ∀ k : Nat, (hk : i ≤ k ∧ k < 16) →
      (x.enc.idx.setWidth 16).toNat < (pts[k]'(by omega)).value.length)
    (u104 : BitVec 64)
    (s0 s : State) (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 288#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1200#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 i)
    (hx19 : s.readReg64 .x19 = x.encA + 8#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (2 * i))
    (hx21 : s.readReg64 .x21 = 0#64)
    (hx24 : s.readReg64 .x24 = x.encA)
    (hx27 : s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hnext : ∀ sf : State,
      sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4484#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1200#64 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.readReg64 .x20 = 32#64 →
      sf.readReg64 .x24 = x.encA →
      sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 .lr) sf
        ((out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 16) ∗
          A.live out_ptr 32 1 ∗
          memRegion x.outA chunkSize ∗
          (x.encA ↦₆₄ polyEncoderPointsTag) ∗
          pointListOf A (x.encA + 8#64) pts ∗
          ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
          memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
          (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗
          (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
          (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
          (((s0.sp - 1200#64) + 104#64) ↦₆₄ 15#64) ∗
          (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
          (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
          (((s0.sp - 1200#64) + 248#64) ↦₆₄ 32#64) ∗
          localFramePointsRest (s0.sp - 1200#64) ∗
          savedCells s0 ∗
          tokenInitAt b ∗
          reduceTableAt b ∗
          A.pool ∗
          stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 .lr) s
      ((out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ∗
        A.live out_ptr 32 1 ∗
        memRegion x.outA chunkSize ∗
        (x.encA ↦₆₄ polyEncoderPointsTag) ∗
        pointListOf A (x.encA + 8#64) pts ∗
        ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
        memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
        (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗
        (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
        (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
        (((s0.sp - 1200#64) + 104#64) ↦₆₄ u104) ∗
        (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
        (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
        (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
        localFramePointsRest (s0.sp - 1200#64) ∗
        savedCells s0 ∗
        tokenInitAt b ∗
        reduceTableAt b ∗
        A.pool ∗
        stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  induction rem generalizing i s u104 with
  | zero =>
    have hi15 : i = 15 := by omega
    subst hi15
    refine pointsFastLoop_step_sepWPp A b ext x pts hlen_pts out_ptr R 15 (by decide)
      (hfast 15 ⟨by omega, by omega⟩) u104 s0 s hsp0 hpc hrun hsp htr hvregs hx9 hx19 hx20 hx21 hx24 hx27 hx28 ?_
    intro sf hpc_f hrun_f hsp_f htr_f hvregs_f _ _ hx20_f _ hx24_f hx27_f _
    simp only [beq_self_eq_true, ↓reduceIte] at hpc_f
    have h0 : 32 - 2 * (15 + 1) = 0 := rfl
    rw [h0, memRegion_zero, emp_sepConj]
    exact hnext sf hpc_f hrun_f hsp_f htr_f hvregs_f hx20_f hx24_f hx27_f
  | succ r ih =>
    have hi16 : i < 16 := by omega
    have hi15_ne : (i == 15) = false := beq_eq_false_iff_ne.mpr (by omega)
    refine pointsFastLoop_step_sepWPp A b ext x pts hlen_pts out_ptr R i hi16
      (hfast i ⟨by omega, hi16⟩) u104 s0 s hsp0 hpc hrun hsp htr hvregs hx9 hx19 hx20 hx21 hx24 hx27 hx28 ?_
    intro sf hpc_f hrun_f hsp_f htr_f hvregs_f hx9_f hx19_f hx20_f hx21_f hx24_f hx27_f hx28_f
    simp only [hi15_ne, Bool.false_eq_true, ↓reduceIte] at hpc_f
    exact ih (i + 1) (by omega) (fun k hk => hfast k ⟨by omega, hk.2⟩) (BitVec.ofNat 64 i) sf
      hpc_f hrun_f hsp_f htr_f hvregs_f hx9_f hx19_f hx20_f hx21_f hx24_f hx27_f hx28_f

set_option maxHeartbeats 1200000 in
/-- Complete proof of `polyNextChunkSpec` when `x.enc.s = .points pts` and
    `∀ k : Fin 16, (x.enc.idx.setWidth 16).toNat < pts[k].value.length`. -/
theorem nextChunk_points_fast_sepWPp
    (A : RustAlloc) (b : BitVec 64) (ext : String → Option (State → State))
    (hA : AllocContracts b A ext)
    (x : PolyNextChunkGhost) (pts : List Point)
    (hs_pts : x.enc.s = .points pts)
    (hlen_pts : pts.length = NUM_POLYS)
    (hfast_all : ∀ k : Fin NUM_POLYS,
      (x.enc.idx.setWidth 16).toNat < (pts[k.val]'(by have := k.isLt; omega)).value.length)
    (hnext : x.enc.nextChunk = .ok (x.enc', x.chunk))
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName)
    (hrun : s0.status = .Running)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.encA)
    (hx8 : s0.readReg64 .x8 = x.outA) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 .lr) s0
      (memRegion x.outA chunkSize ∗
       polyEncoderAt A x.encA x.enc ∗
       tokenInitAt b ∗
       reduceTableAt b ∗
       A.pool ∗
       stackAt s0.sp polyNextChunkStack)
      (fun sf1 P_f =>
        ((sf1.mem ⊨ P_f ∗ R) →
          (sf1.mem ⊨
            ⌜sf1.trace = s0.trace⌝ ∗
             chunkAt x.outA x.chunk ∗
             polyEncoderAt A x.encA x.enc' ∗
             tokenInitAt b ∗
             reduceTableAt b ∗
             A.pool ∗
             stackAt s0.sp polyNextChunkStack ∗ R)) ∧
          sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  conv => arg 4; unfold polyEncoderAt encoderStateAt; rw [hs_pts]
  have hpure_len :
      ∀ (P1 : SepProp) (φ : Prop) (P_tag P_list P_idx P_pad Rest : SepProp),
        P1 ∗ ((⌜φ⌝ ∗ P_tag ∗ P_list) ∗ P_idx ∗ P_pad) ∗ Rest =
          ⌜φ⌝ ∗ (P1 ∗ P_tag ∗ P_list ∗ P_idx ∗ P_pad ∗ Rest) := by
    intros; ac_rfl
  rw [hpure_len]
  apply SepWPp.pure_left; rintro ⟨_, hbounds⟩
  have hlen16 : pts.length = 16 := hlen_pts
  have henc_eq : x.enc = { idx := x.enc.idx, s := .points pts } := by
    rw [← hs_pts]
  have hnc := nextChunk_points_all_lt_eq (idx := x.enc.idx) hlen16
    (fun k hk => hfast_all ⟨k, by omega⟩)
  rw [← henc_eq] at hnc
  rw [hnc, Except.ok.injEq, Prod.mk.injEq] at hnext
  rcases hnext with ⟨henc'_eq, hchunk_eq⟩
  have hdata_eq : x.chunk.data.toList = chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 16 := by
    rw [← hchunk_eq]; rfl
  have hidx_chunk : x.chunk.index = x.enc.idx.setWidth 16 := by
    rw [← hchunk_eq]
  have hidx_enc' : x.enc'.idx = x.enc.idx + 1#32 := by
    rw [← henc'_eq]
  have hs_enc' : x.enc'.s = .points pts := by
    rw [← henc'_eq]
  refine prologue_sepWPp A b ext hA x polyEncoderPointsTag
    (pointListOf A (x.encA + polyEncoderVecsOff) pts) R s0 hpc hrun hsp0 hx0 hx8 ?_
  intro s1 out_ptr hout_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx9_1 hx19_1 hx24_1 hx27_1 _hx29_1
  change s1.readReg64 .x9 = 0#64 at hx9_1
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x5c 8
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xdc 32
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 288#64)
  apply SepWP.fold (localFrameRest_unfold_points (s0.sp - 1200#64)) (by sep_focus)
  apply sepWP_exists_left_sep; intro u48
  apply sepWP_exists_left_sep; intro u88
  apply sepWP_exists_left_sep; intro u104
  wp_steps 9
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rw [← hentry]
  have hinit_buf :
      memRegion out_ptr 32 =
        (out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 0) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * 0)) (32 - 2 * 0) := by
    simp [chunkPointsBytes, pointsToBytes_nil, emp_sepConj]
  have hfast0 : ∀ k : Nat, (hk : 0 ≤ k ∧ k < 16) →
      (x.enc.idx.setWidth 16).toNat < (pts[k]'(by omega)).value.length :=
    fun k hk => hfast_all ⟨k, hk.2⟩
  refine SepWPp.weaken_pre ?_
    (pointsFastLoop_sepWPp A b ext x pts hlen16 out_ptr R 15 0 rfl hfast0 u104 s0 _ hsp0
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · rw [hinit_buf]
    exact Entails.of_eq (by simp only [arm64_norm]; ac_rfl)
  · rw [hentry]; wp_norm_goal
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hsp1
  · simpa [arm64_norm, wp_norm] using htr1
  · simpa [arm64_norm, wp_norm] using hvregs1
  · rfl
  · simpa [arm64_norm, wp_norm] using hx19_1
  · rfl
  · rfl
  · simpa [arm64_norm, wp_norm] using hx24_1
  · simpa [arm64_norm, wp_norm] using hx27_1
  · rfl
  intro sf hpc_f hrun_f hsp_f htr_f hvregs_f hx20_f hx24_f hx27_f
  apply SepWPp.of_sepWP_ret
  have hlfr_fold :
      (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗
        (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
        (((s0.sp - 1200#64) + 104#64) ↦₆₄ 15#64) ∗
        localFramePointsRest (s0.sp - 1200#64) ⊢
        localFrameRest (s0.sp - 1200#64) :=
    localFrameRest_fold_points (s0.sp - 1200#64) 2#64 (x.encA + 8#64) 15#64
  apply SepWP.fold hlfr_fold (by sep_focus)
  have henc'_state :
      (x.encA ↦₆₄ polyEncoderPointsTag) ∗ pointListOf A (x.encA + 8#64) pts ⊢
        encoderStateAt A x.encA x.enc'.s := by
    rw [hs_enc']
    unfold encoderStateAt
    dsimp only [polyEncoderVecsOff]
    have htrue : (pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)) = True :=
      propext ⟨fun _ => trivial, fun _ => ⟨hlen_pts, hbounds⟩⟩
    rw [htrue, pure_true, emp_sepConj]
    exact Entails.refl _
  apply SepWP.fold henc'_state (by sep_focus)
  rw [← hdata_eq]
  refine SepWP.weaken_pre (Entails.of_eq (by
    simp only [arm64_norm]
    ac_rfl))
    (epilogue_sepWP A b ext hA x R s0 sf out_ptr hout_ne hidx_chunk hidx_enc'
      hpc_f hrun_f hsp_f hsp0 htr_f hx20_f hx24_f ?_ hvregs_f)
  rw [hx27_f, BitVec.setWidth_setWidth_of_le (x.enc.idx.setWidth 16) (by decide)]
  rfl

end CryptoVerification.SpqrV1.Poly.NextChunk
