/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrow
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `RawVecInner::reserve::do_reserve_and_handle` (`[local#2, 4, 7]`)

Verifies the three `do_reserve_and_handle` monomorphizations in SPQR V1 (`[local#7]` with
generic `(stride, align)` and `[local#2, 4]` specialized to `stride = 1, align = 1`) under
`AllocContracts`, `AllocContractsX`, and `[LibsignalPlacement]` (blocks 320, 157, and 218).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace DoReserveNorm

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

theorem pull_fg0_err (P1 P2 P3 P4 P5 R : SepProp) (φ : Prop) :
    (P1 ∗ P2 ∗ P3 ∗ ⌜φ⌝ ∗ P4 ∗ P5) ∗ R =
      ⌜φ⌝ ∗ ((P4 ∗ P5 ∗ P1 ∗ P2 ∗ P3) ∗ R) := by ac_rfl

theorem pull_fg0_ok (P1 P2 P3 L1 L2 P4 P5 R : SepProp) (φ : Prop) :
    (P1 ∗ P2 ∗ P3 ∗ (⌜φ⌝ ∗ L1 ∗ L2) ∗ P4 ∗ P5) ∗ R =
      ⌜φ⌝ ∗ ((L1 ∗ L2 ∗ P4 ∗ P5 ∗ P1 ∗ P2 ∗ P3) ∗ R) := by ac_rfl

theorem pull_fg1_post (P1 P2 P3 L1 L2 L3 P4 P5 R : SepProp) (φ : Prop) :
    (P1 ∗ P2 ∗ P3 ∗ (⌜φ⌝ ∗ L1 ∗ L2 ∗ L3) ∗ P4 ∗ P5) ∗ R =
      ⌜φ⌝ ∗ ((L1 ∗ L2 ∗ L3 ∗ P4 ∗ P5 ∗ P1 ∗ P2 ∗ P3) ∗ R) := by ac_rfl

theorem doReserve_pre_repack (P1 P2 P3 P4 P5 P6 R : SepProp) :
    P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ (P6 ∗ R) =
      P1 ∗ P2 ∗ P6 ∗ P3 ∗ P4 ∗ P5 ∗ R := by ac_rfl

theorem doReserve_post_repack (P1 P2 P6 P3 P4 P5 P7 R : SepProp) :
    (P1 ∗ P2 ∗ P6 ∗ P3 ∗ P4 ∗ P5) ∗ P7 ∗ R =
      (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5) ∗ P7 ∗ (P6 ∗ R) := by ac_rfl

end DoReserveNorm

open DoReserveNorm

/-! ## Symbols and Capacity Helpers -/

abbrev doReserve2Name : String :=
  "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]"

abbrev doReserve4Name : String :=
  "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#4]"

abbrev doReserve7Name : String :=
  "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]"

/-- Minimum element capacity selected by `do_reserve_and_handle`: `8` when `stride = 1`, `4` otherwise. -/
def reserveMinCap (stride : Nat) : Nat :=
  if stride = 1 then 8 else 4

/-- Target element capacity `max (max (len + additional) (2 * cap)) (reserveMinCap stride)`. -/
def reserveCapStride (stride cap len additional : Nat) : Nat :=
  max (max (len + additional) (2 * cap)) (reserveMinCap stride)

@[simp]
theorem reserveCapStride_one (cap len additional : Nat) :
    reserveCapStride 1 cap len additional = reserveCap cap len additional := rfl

theorem adds_cs_eq_false {x2 x1 : BitVec 64}
    (h : x2.toNat + x1.toNat < 2 ^ 64) :
    (x2 + x1).ult x2 = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_add, Nat.mod_eq_of_lt h]
  omega

theorem reserve_new_cap_eq {cap x1 x2 : BitVec 64} {len additional : Nat}
    (hx1 : x1.toNat = len) (hx2 : x2.toNat = additional)
    (h : reserveCap cap.toNat len additional + 1 ≤ 2 ^ 63) :
    (if (8#64).ult (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = true then
      if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1
     else 8#64) =
      BitVec.ofNat 64 (reserveCap cap.toNat len additional) := by
  have hmax : max (max (len + additional) (2 * cap.toNat)) 8 + 1 ≤ 2 ^ 63 := h
  have hadd : (x2 + x1).toNat = len + additional := by
    rw [BitVec.toNat_add, hx2, hx1, Nat.mod_eq_of_lt (by omega)]
    omega
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hm1 : (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1).toNat =
      max (len + additional) (2 * cap.toNat) := by
    by_cases hc : (cap <<< 1).ult (x2 + x1) = true
    · simp only [hc, ite_true, hadd]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc
      omega
    · simp only [hc, Bool.false_eq_true, ite_false, hsh]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc
      omega
  apply BitVec.eq_of_toNat_eq
  dsimp only [reserveCap]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  generalize (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = m1 at hm1 ⊢
  by_cases hc2 : (8#64).ult m1 = true
  · simp only [hc2, ite_true, hm1]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm1] at hc2
    change 8 < max (len + additional) (2 * cap.toNat) at hc2
    omega
  · simp only [hc2, Bool.false_eq_true, ite_false]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm1] at hc2
    change ¬ 8 < max (len + additional) (2 * cap.toNat) at hc2
    change 8 = max (max (len + additional) (2 * cap.toNat)) 8
    omega

theorem reserve_new_cap_stride_eq {stride cap x1 x2 : BitVec 64} {len additional : Nat}
    (hx1 : x1.toNat = len) (hx2 : x2.toNat = additional)
    (h : reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63) :
    (if (if (stride == 1#64) = true then 8#64 else 4#64).ult
          (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = true then
      if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1
     else if (stride == 1#64) = true then 8#64 else 4#64) =
      BitVec.ofNat 64 (reserveCapStride stride.toNat cap.toNat len additional) := by
  have hmin_ge : 4 ≤ reserveMinCap stride.toNat := by
    unfold reserveMinCap; split <;> omega
  have hmax : max (max (len + additional) (2 * cap.toNat)) (reserveMinCap stride.toNat) < 2 ^ 63 := h
  have hadd : (x2 + x1).toNat = len + additional := by
    rw [BitVec.toNat_add, hx2, hx1, Nat.mod_eq_of_lt (by omega)]
    omega
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hm0 : (if (stride == 1#64) = true then 8#64 else 4#64).toNat = reserveMinCap stride.toNat := by
    by_cases hs : (stride == 1#64) = true
    · have hs' : stride = 1#64 := beq_iff_eq.mp hs
      subst hs'
      rfl
    · have hs' : stride.toNat ≠ 1 := by
        intro h1
        apply hs
        exact beq_iff_eq.mpr (BitVec.eq_of_toNat_eq h1)
      simp only [hs, Bool.false_eq_true, ite_false, reserveMinCap, hs']
      rfl
  have hm1 : (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1).toNat =
      max (len + additional) (2 * cap.toNat) := by
    by_cases hc : (cap <<< 1).ult (x2 + x1) = true
    · simp only [hc, ite_true, hadd]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc
      omega
    · simp only [hc, Bool.false_eq_true, ite_false, hsh]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc
      omega
  apply BitVec.eq_of_toNat_eq
  dsimp only [reserveCapStride]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  generalize (if (stride == 1#64) = true then 8#64 else 4#64) = m0 at hm0 ⊢
  generalize (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = m1 at hm1 ⊢
  by_cases hc2 : m0.ult m1 = true
  · simp only [hc2, ite_true, hm1]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm0, hm1] at hc2
    omega
  · simp only [hc2, Bool.false_eq_true, ite_false, hm0]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm0, hm1] at hc2
    omega

theorem stackAt_doReserve_gen (sp : BitVec 64) {hookStack : Nat}
    (h : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64) :
    stackAt sp ((hookStack + 48) + 64) =
      stackAt (sp - 64#64) (hookStack + 48) ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_cells sp (hookStack + 48) 8 h
  change stackAt sp ((hookStack + 48) + 64) =
    stackAt (sp - 64#64) (hookStack + 48) ∗ cells (sp - 64#64) 8 at h1
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

theorem stackAt_doReserve32_gen (sp : BitVec 64) {hookStack : Nat}
    (h : (hookStack + 32) + 8 * 8 ≤ 2 ^ 64) :
    stackAt sp ((hookStack + 32) + 64) =
      stackAt (sp - 64#64) (hookStack + 32) ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_cells sp (hookStack + 32) 8 h
  change stackAt sp ((hookStack + 32) + 64) =
    stackAt (sp - 64#64) (hookStack + 32) ∗ cells (sp - 64#64) 8 at h1
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

/-- Stack budget of 32-byte-frame `do_reserve_and_handle [local#2, 4]` (`finishGrow32Stack + 64`). -/
abbrev doReserve32Stack : Nat := finishGrow32Stack + 64

/-- Stack budget of 32-byte-frame `do_reserve_and_handle` under `AllocContractsX` (`finishGrow32StackX + 64`). -/
abbrev doReserve32StackX : Nat := finishGrow32StackX + 64

theorem stackAt_doReserveX (sp : BitVec 64) :
    stackAt sp doReserveStackX =
      stackAt (sp - 64#64) finishGrowStackX ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) :=
  stackAt_doReserve_gen sp (hookStack := extHookStack) (by decide)

theorem stackAt_doReserve32X (sp : BitVec 64) :
    stackAt sp doReserve32StackX =
      stackAt (sp - 64#64) finishGrow32StackX ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) :=
  stackAt_doReserve32_gen sp (hookStack := extHookStack) (by decide)

/-! ## Cell-Unfolded `finish_grow` Wrappers -/

abbrev FG8Ghost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

def finishGrow8ZeroCellsSpecG (A : RustAlloc) (hookStack : Nat) : Spec FG8Ghost where
  pre := fun (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧ LayoutOk (new.toNat * stride.toNat) align.toNat⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ stackAt fsp (hookStack + 48)
  post := fun (out, _cap, _ptr, new, align, stride, _bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (new.toNat * stride.toNat) align.toNat ∗
          memRegion p' (new.toNat * stride.toNat)) ∗
      A.pool ∗ stackAt fsp (hookStack + 48) ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

def finishGrow8ZeroCellsSpecX (A : RustAlloc) : Spec FG8Ghost :=
  finishGrow8ZeroCellsSpecG A extHookStack

theorem finish_grow_8_zero_cells_opt_of_spec {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat} {img? : Option Obj.Image}
    (hfg : subroutine_ok P addr (Spec.withOptInv (finishGrowSpecWithStack A hookStack) img?)) :
    subroutine_ok P addr (Spec.withOptInv (finishGrow8ZeroCellsSpecG A hookStack) img?) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.withOptInv, finishGrow8ZeroCellsSpecG, sepConj_assoc, satisfies_pure_sepConj]
    at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hstr, hlay⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, align, stride, []⟩
  have hpre' : s0.mem ⊨ (Spec.withOptInv (finishGrowSpecWithStack A hookStack) img?).pre hcall s0 ∗ R := by
    simp only [Spec.withOptInv, finishGrowSpecWithStack, hcall, FinishGrowCall.oldBuf, ite_true,
      memRegion_24, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, hstr, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.withOptInv, finishGrowSpecWithStack, finishGrow8ZeroCellsSpecG, hcall,
      FinishGrowCall.oldBuf, ite_true, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * stride.toNat), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg0_err, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg0_ok, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩
  · exact Or.inr hfail

theorem finish_grow_8_zero_cells_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrow8Name)
      ((finishGrow8ZeroCellsSpecX A).inImage img) :=
  finish_grow_8_zero_cells_opt_of_spec (hookStack := extHookStack) (img? := some img)
    (finish_grow_8_ok_ext_xa hA)

def finishGrow8NeCellsSpecG (A : RustAlloc) (hookStack : Nat) : Spec FG8Ghost where
  pre := fun (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length ≤ cap.toNat * stride.toNat ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧ LayoutOk (new.toNat * stride.toNat) align.toNat⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr (cap.toNat * stride.toNat) align.toNat ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * stride.toNat - bs.length) ∗
    A.pool ∗ stackAt fsp (hookStack + 48)
  post := fun (out, cap, ptr, new, align, stride, bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          A.live ptr (cap.toNat * stride.toNat) align.toNat ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * stride.toNat - bs.length)
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (new.toNat * stride.toNat) align.toNat ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * stride.toNat - bs.length)) ∗
      A.pool ∗ stackAt fsp (hookStack + 48) ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

def finishGrow8NeCellsSpecX (A : RustAlloc) : Spec FG8Ghost :=
  finishGrow8NeCellsSpecG A extHookStack

theorem finish_grow_8_ne_cells_opt_of_spec {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat} {img? : Option Obj.Image}
    (hfg : subroutine_ok P addr (Spec.withOptInv (finishGrowSpecWithStack A hookStack) img?)) :
    subroutine_ok P addr (Spec.withOptInv (finishGrow8NeCellsSpecG A hookStack) img?) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.withOptInv, finishGrow8NeCellsSpecG, sepConj_assoc, satisfies_pure_sepConj]
    at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hstr, hlay⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, align, stride, bs⟩
  have hpre' : s0.mem ⊨ (Spec.withOptInv (finishGrowSpecWithStack A hookStack) img?).pre hcall s0 ∗ R := by
    simp only [Spec.withOptInv, finishGrowSpecWithStack, hcall, FinishGrowCall.oldBuf, hcap, ite_false,
      memRegion_24, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs, hle, hpos, hstr, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.withOptInv, finishGrowSpecWithStack, finishGrow8NeCellsSpecG, hcall,
      FinishGrowCall.oldBuf, hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * stride.toNat), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, by simpa only [sepConj_assoc] using hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩
  · exact Or.inr hfail

theorem finish_grow_8_ne_cells_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrow8Name)
      ((finishGrow8NeCellsSpecX A).inImage img) :=
  finish_grow_8_ne_cells_opt_of_spec (hookStack := extHookStack) (img? := some img)
    (finish_grow_8_ok_ext_xa hA)

abbrev FG24Ghost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

def finishGrow24ZeroCellsSpecG (A : RustAlloc) (hookStack : Nat) : Spec FG24Ghost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧
      cap.toNat ≤ new.toNat ∧ 0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ stackAt fsp (hookStack + 32)
  post := fun (out, _cap, _ptr, new, _bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' new.toNat 1 ∗ memRegion p' new.toNat) ∗
      A.pool ∗ stackAt fsp (hookStack + 32) ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

def finishGrow24ZeroCellsSpecX (A : RustAlloc) : Spec FG24Ghost :=
  finishGrow24ZeroCellsSpecG A extHookStack

theorem finish_grow_24_zero_cells_opt_of_spec {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat} {img? : Option Obj.Image}
    (hfg : subroutine_ok P addr (Spec.withOptInv (finishGrow1SpecWithStack A hookStack) img?)) :
    subroutine_ok P addr (Spec.withOptInv (finishGrow24ZeroCellsSpecG A hookStack) img?) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.withOptInv, finishGrow24ZeroCellsSpecG, sepConj_assoc, satisfies_pure_sepConj]
    at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hfsp, hcap0, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrow1Call := ⟨out, 0#64, ptr, new, []⟩
  have hpre' : s0.mem ⊨ (Spec.withOptInv (finishGrow1SpecWithStack A hookStack) img?).pre hcall s0 ∗ R := by
    simp only [Spec.withOptInv, finishGrow1SpecWithStack, hcall, FinishGrow1Call.oldBuf, ite_true,
      memRegion_24, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, fun _ => trivial, Nat.zero_le _, hle, hpos, hbound⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.withOptInv, finishGrow1SpecWithStack, finishGrow24ZeroCellsSpecG, hcall,
      FinishGrow1Call.oldBuf, ite_true, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', new, ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg0_err, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg0_ok, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩
  · exact Or.inr hfail

theorem finish_grow_24_zero_cells_of_spec_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {name : String}
    (hfg : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name) ((finishGrow1SpecX A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name)
      ((finishGrow24ZeroCellsSpecX A).inImage img) :=
  finish_grow_24_zero_cells_opt_of_spec (hookStack := extHookStack) (img? := some img) hfg

def finishGrow24NeCellsSpecG (A : RustAlloc) (hookStack : Nat) : Spec FG24Ghost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.sp = fsp ∧ cap ≠ 0#64 ∧
      bs.length ≤ cap.toNat ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
    A.pool ∗ stackAt fsp (hookStack + 32)
  post := fun (out, cap, ptr, new, bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' new.toNat 1 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat - bs.length)) ∗
      A.pool ∗ stackAt fsp (hookStack + 32) ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

def finishGrow24NeCellsSpecX (A : RustAlloc) : Spec FG24Ghost :=
  finishGrow24NeCellsSpecG A extHookStack

theorem finish_grow_24_ne_cells_opt_of_spec {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat} {img? : Option Obj.Image}
    (hfg : subroutine_ok P addr (Spec.withOptInv (finishGrow1SpecWithStack A hookStack) img?)) :
    subroutine_ok P addr (Spec.withOptInv (finishGrow24NeCellsSpecG A hookStack) img?) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.withOptInv, finishGrow24NeCellsSpecG, sepConj_assoc, satisfies_pure_sepConj]
    at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hfsp, hcap, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrow1Call := ⟨out, cap, ptr, new, bs⟩
  have hpre' : s0.mem ⊨ (Spec.withOptInv (finishGrow1SpecWithStack A hookStack) img?).pre hcall s0 ∗ R := by
    simp only [Spec.withOptInv, finishGrow1SpecWithStack, hcall, FinishGrow1Call.oldBuf, hcap, ite_false,
      memRegion_24, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, False.elim, hbs, hle, hpos, hbound⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.withOptInv, finishGrow1SpecWithStack, finishGrow24NeCellsSpecG, hcall,
      FinishGrow1Call.oldBuf, hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', new, ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, by simpa only [sepConj_assoc] using hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩
  · exact Or.inr hfail

theorem finish_grow_24_ne_cells_of_spec_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {name : String}
    (hfg : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name) ((finishGrow1SpecX A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name)
      ((finishGrow24NeCellsSpecX A).inImage img) :=
  finish_grow_24_ne_cells_opt_of_spec (hookStack := extHookStack) (img? := some img) hfg

/-! ## `do_reserve_and_handle [local#7]` (Generic `stride` and `align`) -/

/-- Ghost parameters for `do_reserve_and_handle [local#7]` with arbitrary `(stride, align)`. -/
structure DoReserveStrideCall where
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)
  len : Nat
  additional : Nat
  align : BitVec 64
  stride : BitVec 64

/-- `doReserveStrideRawSpec` parameterized by callee `hookStack`. -/
def doReserveStrideRawSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec DoReserveStrideCall where
  pre := fun x s =>
    let newCap := reserveCapStride x.stride.toNat x.cap.toNat x.len x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.len ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = x.align ∧
      s.readReg64 .x4 = x.stride ∧
      x.len ≤ x.cap.toNat ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
      x.ptr ≠ 0#64 ∧ 0 < x.stride.toNat ∧ LayoutOk (newCap * x.stride.toNat) x.align.toNat⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length)
         (x.cap.toNat * x.stride.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s.sp ((hookStack + 48) + 64)
  post := fun x s0 sf =>
    let newCap := reserveCapStride x.stride.toNat x.cap.toNat x.len x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0⌝ ∗
      (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' (newCap * x.stride.toNat) x.align.toNat ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length)
        (newCap * x.stride.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s0.sp ((hookStack + 48) + 64)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Contract of `do_reserve_and_handle [local#7]` for arbitrary `(stride, align)` at `doReserveStack`. -/
def doReserveStrideRawSpec (A : RustAlloc) : Spec DoReserveStrideCall where
  pre := fun x s =>
    let newCap := reserveCapStride x.stride.toNat x.cap.toNat x.len x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.len ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = x.align ∧
      s.readReg64 .x4 = x.stride ∧
      x.len ≤ x.cap.toNat ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
      x.ptr ≠ 0#64 ∧ 0 < x.stride.toNat ∧ LayoutOk (newCap * x.stride.toNat) x.align.toNat⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length)
         (x.cap.toNat * x.stride.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s.sp doReserveStack
  post := fun x s0 sf =>
    let newCap := reserveCapStride x.stride.toNat x.cap.toNat x.len x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0⌝ ∗
      (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' (newCap * x.stride.toNat) x.align.toNat ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length)
        (newCap * x.stride.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s0.sp doReserveStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def doReserveStrideRawSpecX (A : RustAlloc) : Spec DoReserveStrideCall :=
  doReserveStrideRawSpecWithStack A extHookStack

private theorem do_reserve_7_stride_raw_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64)
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (Spec.withOptInv (finishGrowSpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve7Name)
      (Spec.withOptInv (doReserveStrideRawSpecWithStack A hookStack) img?) := by
  unfold Spec.withOptInv
  simp only [doReserveStrideRawSpecWithStack, stackAt_doReserve_gen _ hhook, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff doReserve7Name)
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := doReserve7Name)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% doReserve7Name))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := finish_grow_8_zero_cells_opt_of_spec hfg
  have hfg1 := finish_grow_8_ne_cells_opt_of_spec hfg
  rw [Program.fnAddr_rel (name := doReserve7Name)
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#7]")
    (k := num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#7]" - ls_off% doReserve7Name))
    (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% doReserve7Name) 140
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢
  clear hfn hfg
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr doReserve7Name = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, len, additional, align, stride⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv img? s0 := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = len := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hlen_le_cap : len ≤ cap.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hptr_ne : ptr ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hsz_pos : 0 < reserveCapStride stride.toNat cap.toNat len additional * stride.toNat := h.1
  have hpow : ∃ k, align.toNat = 2 ^ k := h.2.1
  have hbound :
      reserveCapStride stride.toNat cap.toNat len additional * stride.toNat + align.toNat ≤ 2 ^ 63 :=
    h.2.2
  have halign_pos : 1 ≤ align.toNat := by
    rcases hpow with ⟨k, hk⟩; rw [hk]; exact Nat.one_le_two_pow
  have hmin_ge : 4 ≤ reserveMinCap stride.toNat := by
    unfold reserveMinCap; split <;> omega
  have hnew_lt63 : reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63 := by
    have : reserveCapStride stride.toNat cap.toNat len additional * 1 ≤
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat :=
      Nat.mul_le_mul_left _ hstr_pos
    omega
  have hmax : max (max (len + additional) (2 * cap.toNat)) (reserveMinCap stride.toNat) < 2 ^ 63 :=
    hnew_lt63
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_stride_eq (stride := stride) (cap := cap) hx1_eq hx2_eq hnew_lt63
  let new := BitVec.ofNat 64 (reserveCapStride stride.toNat cap.toNat len additional)
  have hnew_toNat : new.toNat = reserveCapStride stride.toNat cap.toNat len additional := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hnew_pos : 0 < new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hnew_lay : LayoutOk (new.toNat * stride.toNat) align.toNat := by
    rw [hnew_toNat]; exact h
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * stride.toNat = 0 := Nat.zero_mul stride.toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 :
        (if (if (stride == 1#64) = true then 8#64 else 4#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
          else 0#64
         else if (stride == 1#64) = true then 8#64 else 4#64) = new := hnew_eq
    have hmul_eq : reserveCapStride stride.toNat 0 len additional * stride.toNat =
        new.toNat * stride.toNat := by
      rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.zero_mod, hmul_eq]
    apply SepWPp.of_sepWP (mid := entry + 88#64)
    apply SepWP.seq_optInv
      (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#7]" - ls_off% doReserve7Name))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv1
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, align, stride, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% doReserve7Name))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq :
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat - bs.length =
          new.toNat * stride.toNat - bs.length := by rw [hnew_toNat]
    have hmul_eq :
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat =
          new.toNat * stride.toNat := by rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := entry + 88#64)
    apply SepWP.seq_optInv
      (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#7]" - ls_off% doReserve7Name))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv1
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, align, stride, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% doReserve7Name))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

/-- `do_reserve_and_handle [local#7]` meets `doReserveStrideRawSpec A`. -/
theorem do_reserve_7_stride_raw_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve7Name)
      (doReserveStrideRawSpec A) :=
  subroutine_ok_of_withOptInv_none
    (do_reserve_7_stride_raw_opt_ok (hookStack := allocHookStack) (by decide)
      (subroutine_ok_withOptInv_none_of (finish_grow_8_ok_ext hA)))

/-- `do_reserve_and_handle [local#7]` meets `(doReserveStrideRawSpecX A).inImage img`. -/
theorem do_reserve_7_stride_raw_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve7Name)
      ((doReserveStrideRawSpecX A).inImage img) :=
  do_reserve_7_stride_raw_opt_ok (A := A) (b := img.base) (ext := ext)
    (hookStack := extHookStack) (img? := some img) (by decide)
    (finish_grow_8_ok_ext_xa hA)

/-- `doReserveRawSpec` parameterized by callee `hookStack`. -/
def doReserveRawSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec DoReserveCall where
  pre := fun x s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧ s.readReg64 .x4 = 1#64 ∧
      x.bs.length ≤ x.cap.toNat ∧ x.ptr ≠ 0#64 ∧ newCap + 1 ≤ 2 ^ 63⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s.sp ((hookStack + 48) + 64)
  post := fun x s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗ (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' newCap 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (newCap - x.bs.length)) ∗
    A.pool ∗ stackAt s0.sp ((hookStack + 48) + 64)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `doReserveSpec` parameterized by callee `hookStack`. -/
def doReserveSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec DoReserveCall where
  pre := fun x s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧ s.readReg64 .x4 = 1#64 ∧
      newCap + 1 ≤ 2 ^ 63⌝ ∗
    vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp ((hookStack + 48) + 64)
  post := fun x s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64, vecU8At A x.v (BitVec.ofNat 64 newCap) p' x.bs) ∗
    A.pool ∗ stackAt s0.sp ((hookStack + 48) + 64)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem do_reserve_7_raw_opt_of_stride {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat} {img? : Option Obj.Image}
    (hs : subroutine_ok P addr (Spec.withOptInv (doReserveStrideRawSpecWithStack A hookStack) img?)) :
    subroutine_ok P addr (Spec.withOptInv (doReserveRawSpecWithStack A hookStack) img?) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.withOptInv, doReserveRawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound⟩, hmem⟩
  let xs : DoReserveStrideCall := ⟨x.v, x.cap, x.ptr, x.bs, x.bs.length, x.additional, 1#64, 1#64⟩
  have hlay : LayoutOk (reserveCap x.cap.toNat x.bs.length x.additional) 1 := by
    refine ⟨by dsimp [reserveCap]; omega, ⟨0, rfl⟩, by omega⟩
  have hpre' : s0.mem ⊨ (Spec.withOptInv (doReserveStrideRawSpecWithStack A hookStack) img?).pre xs s0 ∗ R := by
    simp only [Spec.withOptInv, doReserveStrideRawSpecWithStack, xs, BitVec.toNat_ofNat, Nat.one_mod,
      reserveCapStride_one, Nat.mul_one, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hlen, hlen, hptr, by decide, hlay⟩, hmem⟩
  refine hs.mono_outcome xs R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.withOptInv, doReserveStrideRawSpecWithStack, doReserveRawSpecWithStack, xs,
      BitVec.toNat_ofNat, Nat.one_mod, reserveCapStride_one, Nat.mul_one, Nat.mod_one, and_true]
      at hq ⊢
    exact hq
  · exact Or.inr hfail

private theorem vecU8At_eq (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  ac_rfl

private theorem do_reserve_vec_opt_of_raw {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat} {img? : Option Obj.Image}
    (hraw : subroutine_ok P addr (Spec.withOptInv (doReserveRawSpecWithStack A hookStack) img?)) :
    subroutine_ok P addr (Spec.withOptInv (doReserveSpecWithStack A hookStack) img?) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.withOptInv, doReserveSpecWithStack, vecU8At_eq, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ⟨hlen, _hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ (Spec.withOptInv (doReserveRawSpecWithStack A hookStack) img?).pre x s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [Spec.withOptInv, doReserveRawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound⟩, ?_⟩
    rwa [doReserve_pre_repack]
  refine hraw.mono_outcome x (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R)
    s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _hex, hq⟩ | ⟨_hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.withOptInv, doReserveRawSpecWithStack, doReserveSpecWithStack, vecU8At_eq]
      at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hp', hmem⟩
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by
      dsimp [reserveCap] at hbound ⊢; omega
    have htoNat : (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
        reserveCap x.cap.toNat x.bs.length x.additional := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
      dsimp [reserveCap]; omega
    have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by
      omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [htoNat] at this
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at this
      dsimp [reserveCap] at this; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, htoNat]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
    rwa [doReserve_post_repack]
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.withOptInv, doReserveRawSpecWithStack, doReserveSpecWithStack] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

theorem do_reserve_7_raw_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve7Name)
      (doReserveRawSpec A) :=
  subroutine_ok_of_withOptInv_none
    (do_reserve_7_raw_opt_of_stride
      (do_reserve_7_stride_raw_opt_ok (hookStack := allocHookStack) (by decide)
        (subroutine_ok_withOptInv_none_of (finish_grow_8_ok_ext hA))))

theorem do_reserve_7_raw_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve7Name)
      ((doReserveRawSpecX A).inImage img) :=
  do_reserve_7_raw_opt_of_stride (hookStack := extHookStack) (img? := some img)
    (do_reserve_7_stride_raw_ok_ext_xa hA)

/-- `do_reserve_and_handle [local#7]` meets `doReserveSpec A`. -/
theorem do_reserve_7_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve7Name)
      (doReserveSpec A) :=
  subroutine_ok_of_withOptInv_none
    (do_reserve_vec_opt_of_raw
      (subroutine_ok_withOptInv_none_of (do_reserve_7_raw_ok_ext hA)))

theorem do_reserve_7_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve7Name)
      ((doReserveSpecX A).inImage img) :=
  do_reserve_vec_opt_of_raw (hookStack := extHookStack) (img? := some img)
    (do_reserve_7_raw_ok_ext_xa hA)

/-! ## `do_reserve_and_handle [local#2]` and `[local#4]` (`stride = 1, align = 1`) -/

def doReserve1Raw32SpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec DoReserveCall where
  pre := fun x s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧
      x.bs.length ≤ x.cap.toNat ∧ x.ptr ≠ 0#64 ∧ newCap + 1 ≤ 2 ^ 63⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s.sp ((hookStack + 32) + 64)
  post := fun x s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗ (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' newCap 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (newCap - x.bs.length)) ∗
    A.pool ∗ stackAt s0.sp ((hookStack + 32) + 64)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def doReserve1RawSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec DoReserveCall where
  pre := fun x s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧
      x.bs.length ≤ x.cap.toNat ∧ x.ptr ≠ 0#64 ∧ newCap + 1 ≤ 2 ^ 63⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s.sp ((hookStack + 48) + 64)
  post := fun x s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗ (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' newCap 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (newCap - x.bs.length)) ∗
    A.pool ∗ stackAt s0.sp ((hookStack + 48) + 64)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Contract of `do_reserve_and_handle [local#2, 4]` (`stride = 1, align = 1`) at `doReserve32Stack`. -/
def doReserve1Raw32Spec (A : RustAlloc) : Spec DoReserveCall where
  pre := fun x s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧
      x.bs.length ≤ x.cap.toNat ∧ x.ptr ≠ 0#64 ∧ newCap + 1 ≤ 2 ^ 63⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s.sp doReserve32Stack
  post := fun x s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗ (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' newCap 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (newCap - x.bs.length)) ∗
    A.pool ∗ stackAt s0.sp doReserve32Stack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Contract of `do_reserve_and_handle [local#2, 4]` framed to `doReserveStack`. -/
def doReserve1RawSpec (A : RustAlloc) : Spec DoReserveCall where
  pre := fun x s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧
      x.bs.length ≤ x.cap.toNat ∧ x.ptr ≠ 0#64 ∧ newCap + 1 ≤ 2 ^ 63⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s.sp doReserveStack
  post := fun x s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗ (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' newCap 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (newCap - x.bs.length)) ∗
    A.pool ∗ stackAt s0.sp doReserveStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def doReserve1Raw32SpecX (A : RustAlloc) : Spec DoReserveCall :=
  doReserve1Raw32SpecWithStack A extHookStack

def doReserve1RawSpecX (A : RustAlloc) : Spec DoReserveCall :=
  doReserve1RawSpecWithStack A extHookStack

private theorem do_reserve_2_raw32_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : (hookStack + 32) + 8 * 8 ≤ 2 ^ 64)
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow2Name)
      (Spec.withOptInv (finishGrow1SpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve2Name)
      (Spec.withOptInv (doReserve1Raw32SpecWithStack A hookStack) img?) := by
  unfold Spec.withOptInv
  simp only [doReserve1Raw32SpecWithStack, stackAt_doReserve32_gen _ hhook, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff doReserve2Name)
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := doReserve2Name)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% doReserve2Name))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := finish_grow_24_zero_cells_opt_of_spec hfg
  have hfg1 := finish_grow_24_ne_cells_opt_of_spec hfg
  rw [Program.fnAddr_rel (name := doReserve2Name)
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#2]")
    (k := num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#2]" - ls_off% doReserve2Name))
    (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% doReserve2Name) 120
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢
  clear hfn hfg
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr doReserve2Name = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, additional⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv img? s0 := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = bs.length := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63 := by
    dsimp only [reserveCap] at h ⊢; omega
  have hmax : max (max (bs.length + additional) (2 * cap.toNat)) 8 + 1 ≤ 2 ^ 63 := hbound
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_eq (cap := cap) hx1_eq hx2_eq hbound
  let new := BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)
  have hnew_toNat : new.toNat = reserveCap cap.toNat bs.length additional := by
    dsimp [new, reserveCap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_pos : 0 < new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbs_le_cap)
    subst hbs
    have hnew_eq0 :
        (if (8#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
          else 0#64
         else 8#64) = new := hnew_eq
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero]
    apply SepWPp.of_sepWP (mid := entry + 68#64)
    apply SepWP.seq_optInv
      (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#2]" - ls_off% doReserve2Name))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv1
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% doReserve2Name))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq : reserveCap cap.toNat bs.length additional - bs.length = new.toNat - bs.length := by
      rw [hnew_toNat]
    rw [hsub_eq]
    apply SepWPp.of_sepWP (mid := entry + 68#64)
    apply SepWP.seq_optInv
      (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#2]" - ls_off% doReserve2Name))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv1
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% doReserve2Name))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

private theorem do_reserve_4_raw32_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : (hookStack + 32) + 8 * 8 ≤ 2 ^ 64)
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow4Name)
      (Spec.withOptInv (finishGrow1SpecWithStack A hookStack) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve4Name)
      (Spec.withOptInv (doReserve1Raw32SpecWithStack A hookStack) img?) := by
  unfold Spec.withOptInv
  simp only [doReserve1Raw32SpecWithStack, stackAt_doReserve32_gen _ hhook, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff doReserve4Name)
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := doReserve4Name)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% doReserve4Name))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := finish_grow_24_zero_cells_opt_of_spec hfg
  have hfg1 := finish_grow_24_ne_cells_opt_of_spec hfg
  rw [Program.fnAddr_rel (name := doReserve4Name)
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#4]")
    (k := num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#4]" - ls_off% doReserve4Name))
    (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn (ls_off% doReserve4Name) 120
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢
  clear hfn hfg
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr doReserve4Name = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, additional⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv img? s0 := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = bs.length := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63 := by
    dsimp only [reserveCap] at h ⊢; omega
  have hmax : max (max (bs.length + additional) (2 * cap.toNat)) 8 + 1 ≤ 2 ^ 63 := hbound
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_eq (cap := cap) hx1_eq hx2_eq hbound
  let new := BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)
  have hnew_toNat : new.toNat = reserveCap cap.toNat bs.length additional := by
    dsimp [new, reserveCap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_pos : 0 < new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbs_le_cap)
    subst hbs
    have hnew_eq0 :
        (if (8#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
          else 0#64
         else 8#64) = new := hnew_eq
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero]
    apply SepWPp.of_sepWP (mid := entry + 68#64)
    apply SepWP.seq_optInv
      (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#4]" - ls_off% doReserve4Name))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv1
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% doReserve4Name))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq : reserveCap cap.toNat bs.length additional - bs.length = new.toNat - bs.length := by
      rw [hnew_toNat]
    rw [hsub_eq]
    apply SepWPp.of_sepWP (mid := entry + 68#64)
    apply SepWP.seq_optInv
      (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#4]" - ls_off% doReserve4Name))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv1
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% doReserve4Name))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

private theorem stackAt_doReserve_eq_32_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : (hookStack + 48) + 64 ≤ 2 ^ 64) :
    stackAt sp ((hookStack + 48) + 64) =
      memRegion (sp - BitVec.ofNat 64 ((hookStack + 48) + 64)) 16 ∗
        stackAt sp ((hookStack + 32) + 64) := by
  have heq : (hookStack + 48) + 64 = ((hookStack + 32) + 64) + 16 := by omega
  rw [heq]
  exact ProofLib.stackAt_split_bottom sp ((hookStack + 32) + 64) 16 (by omega)

private theorem do_reserve_raw1_opt_of_raw32 {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : (hookStack + 48) + 64 ≤ 2 ^ 64)
    (h32 : subroutine_ok P addr (Spec.withOptInv (doReserve1Raw32SpecWithStack A hookStack) img?)) :
    subroutine_ok P addr (Spec.withOptInv (doReserve1RawSpecWithStack A hookStack) img?) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.withOptInv, doReserve1RawSpecWithStack, stackAt_doReserve_eq_32_gen _ hhook,
    sepConj_assoc] at hpre
  let btm := memRegion (s0.sp - BitVec.ofNat 64 ((hookStack + 48) + 64)) 16
  have hpre' : s0.mem ⊨ (Spec.withOptInv (doReserve1Raw32SpecWithStack A hookStack) img?).pre x s0 ∗
      (btm ∗ R) := by
    simp only [Spec.withOptInv, doReserve1Raw32SpecWithStack, btm, sepConj_assoc]
    ac_nf at hpre ⊢
  refine h32.mono_outcome x (btm ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _hex, hq⟩ | ⟨_hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.withOptInv, doReserve1Raw32SpecWithStack, doReserve1RawSpecWithStack,
      stackAt_doReserve_eq_32_gen _ hhook, btm, sepConj_assoc] at hq ⊢
    ac_nf at hq ⊢
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.withOptInv, doReserve1Raw32SpecWithStack, doReserve1RawSpecWithStack] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

private theorem do_reserve_raw_opt_of_raw1 {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat} {img? : Option Obj.Image}
    (h1 : subroutine_ok P addr (Spec.withOptInv (doReserve1RawSpecWithStack A hookStack) img?)) :
    subroutine_ok P addr (Spec.withOptInv (doReserveRawSpecWithStack A hookStack) img?) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.withOptInv, doReserveRawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, _, _, hlen, hptr, hbound⟩, hmem⟩
  have hpre' : s0.mem ⊨ (Spec.withOptInv (doReserve1RawSpecWithStack A hookStack) img?).pre x s0 ∗ R := by
    simp only [Spec.withOptInv, doReserve1RawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hlen, hptr, hbound⟩, hmem⟩
  exact h1.mono_outcome x R s0 hpc hrun hpre' hsp fun _ hout => hout

/-- `do_reserve_and_handle [local#2]` meets `doReserve1Raw32Spec A`. -/
theorem do_reserve_2_raw32_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve2Name)
      (doReserve1Raw32Spec A) :=
  subroutine_ok_of_withOptInv_none
    (do_reserve_2_raw32_opt_ok (hookStack := allocHookStack) (by decide)
      (subroutine_ok_withOptInv_none_of (finish_grow_2_ok_ext hA)))

theorem do_reserve_2_raw32_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve2Name)
      ((doReserve1Raw32SpecX A).inImage img) :=
  do_reserve_2_raw32_opt_ok (A := A) (b := img.base) (ext := ext)
    (hookStack := extHookStack) (img? := some img) (by decide)
    (finish_grow_2_ok_ext_xa hA)

/-- `do_reserve_and_handle [local#4]` meets `doReserve1Raw32Spec A`. -/
theorem do_reserve_4_raw32_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve4Name)
      (doReserve1Raw32Spec A) :=
  subroutine_ok_of_withOptInv_none
    (do_reserve_4_raw32_opt_ok (hookStack := allocHookStack) (by decide)
      (subroutine_ok_withOptInv_none_of (finish_grow_4_ok_ext hA)))

theorem do_reserve_4_raw32_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve4Name)
      ((doReserve1Raw32SpecX A).inImage img) :=
  do_reserve_4_raw32_opt_ok (A := A) (b := img.base) (ext := ext)
    (hookStack := extHookStack) (img? := some img) (by decide)
    (finish_grow_4_ok_ext_xa hA)

theorem do_reserve_2_raw1_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve2Name)
      (doReserve1RawSpec A) :=
  subroutine_ok_of_withOptInv_none
    (do_reserve_raw1_opt_of_raw32 (hookStack := allocHookStack) (by decide)
      (subroutine_ok_withOptInv_none_of (do_reserve_2_raw32_ok_ext hA)))

theorem do_reserve_2_raw1_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve2Name)
      ((doReserve1RawSpecX A).inImage img) :=
  do_reserve_raw1_opt_of_raw32 (hookStack := extHookStack) (img? := some img) (by decide)
    (do_reserve_2_raw32_ok_ext_xa hA)

theorem do_reserve_2_raw_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve2Name)
      (doReserveRawSpec A) :=
  subroutine_ok_of_withOptInv_none
    (do_reserve_raw_opt_of_raw1
      (subroutine_ok_withOptInv_none_of (do_reserve_2_raw1_ok_ext hA)))

theorem do_reserve_2_raw_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve2Name)
      ((doReserveRawSpecX A).inImage img) :=
  do_reserve_raw_opt_of_raw1 (hookStack := extHookStack) (img? := some img)
    (do_reserve_2_raw1_ok_ext_xa hA)

/-- `do_reserve_and_handle [local#2]` meets `doReserveSpec A`. -/
theorem do_reserve_2_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve2Name)
      (doReserveSpec A) :=
  subroutine_ok_of_withOptInv_none
    (do_reserve_vec_opt_of_raw
      (subroutine_ok_withOptInv_none_of (do_reserve_2_raw_ok_ext hA)))

theorem do_reserve_2_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve2Name)
      ((doReserveSpecX A).inImage img) :=
  do_reserve_vec_opt_of_raw (hookStack := extHookStack) (img? := some img)
    (do_reserve_2_raw_ok_ext_xa hA)

theorem do_reserve_4_raw1_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve4Name)
      (doReserve1RawSpec A) :=
  subroutine_ok_of_withOptInv_none
    (do_reserve_raw1_opt_of_raw32 (hookStack := allocHookStack) (by decide)
      (subroutine_ok_withOptInv_none_of (do_reserve_4_raw32_ok_ext hA)))

theorem do_reserve_4_raw1_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve4Name)
      ((doReserve1RawSpecX A).inImage img) :=
  do_reserve_raw1_opt_of_raw32 (hookStack := extHookStack) (img? := some img) (by decide)
    (do_reserve_4_raw32_ok_ext_xa hA)

theorem do_reserve_4_raw_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve4Name)
      (doReserveRawSpec A) :=
  subroutine_ok_of_withOptInv_none
    (do_reserve_raw_opt_of_raw1
      (subroutine_ok_withOptInv_none_of (do_reserve_4_raw1_ok_ext hA)))

theorem do_reserve_4_raw_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve4Name)
      ((doReserveRawSpecX A).inImage img) :=
  do_reserve_raw_opt_of_raw1 (hookStack := extHookStack) (img? := some img)
    (do_reserve_4_raw1_ok_ext_xa hA)

/-- `do_reserve_and_handle [local#4]` meets `doReserveSpec A`. -/
theorem do_reserve_4_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserve4Name)
      (doReserveSpec A) :=
  subroutine_ok_of_withOptInv_none
    (do_reserve_vec_opt_of_raw
      (subroutine_ok_withOptInv_none_of (do_reserve_4_raw_ok_ext hA)))

theorem do_reserve_4_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve4Name)
      ((doReserveSpecX A).inImage img) :=
  do_reserve_vec_opt_of_raw (hookStack := extHookStack) (img? := some img)
    (do_reserve_4_raw_ok_ext_xa hA)

/-- Weakens `doReserveSpec A` to `doReserveSpecX A` by framing unused stack space. -/
theorem doReserveSpecX_of_doReserveSpec {P : Program} {addr : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok P addr (doReserveSpec A)) : subroutine_ok P addr (doReserveSpecX A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hle : doReserveStack ≤ doReserveStackX := by decide
  have hsplit : stackAt s0.sp doReserveStackX =
      memRegion (s0.sp - BitVec.ofNat 64 doReserveStackX) (doReserveStackX - doReserveStack) ∗
        stackAt s0.sp doReserveStack := by
    have h1 := stackAt_split_bottom s0.sp doReserveStack (doReserveStackX - doReserveStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 doReserveStackX) (doReserveStackX - doReserveStack) ∗ R
  have hpre' : s0.mem ⊨ (doReserveSpec A).pre x s0 ∗ R' := by
    dsimp only [doReserveSpecX, doReserveSpec, R'] at hpre ⊢; rw [hsplit] at hpre; ac_nf at hpre ⊢
  refine h.mono_outcome x R' s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [doReserveSpecX, doReserveSpec, R'] at hpost ⊢; rw [hsplit]; ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, allowPanic_frame id (by dsimp only [doReserveSpec, R'] at hpost ⊢; rwa [sepConj_assoc])⟩)
  · exact (allowPanic_not_exited hex).elim
  · exact (allowPanic_not_exited hoom).elim

theorem do_reserve_7_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve7Name) ((doReserveSpecX A).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (doReserveSpecX_of_doReserveSpec (do_reserve_7_ok_ext hA))

theorem do_reserve_2_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve2Name) ((doReserveSpecX A).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (doReserveSpecX_of_doReserveSpec (do_reserve_2_ok_ext hA))

theorem do_reserve_4_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve4Name) ((doReserveSpecX A).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (doReserveSpecX_of_doReserveSpec (do_reserve_4_ok_ext hA))

/-! ## Relocatable Contracts (Blocks 320, 157, and 218) -/

theorem finish_grow_8_zero_cells_placed_of_spec {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hfg : subroutine_ok P addr (finishGrowSpecWithStack A hookStack)) :
    subroutine_ok P addr (finishGrow8ZeroCellsSpecG A hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow8ZeroCellsSpecG, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hstr, hlay⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, align, stride, []⟩
  have hpre' : s0.mem ⊨ (finishGrowSpecWithStack A hookStack).pre hcall s0 ∗ R := by
    simp only [finishGrowSpecWithStack, hcall, FinishGrowCall.oldBuf, ite_true,
      memRegion_24, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, hstr, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrowSpecWithStack, finishGrow8ZeroCellsSpecG, hcall,
      FinishGrowCall.oldBuf, ite_true, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * stride.toNat), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg0_err, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg0_ok, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩
  · exact Or.inr hfail

private theorem finish_grow_8_zero_cells_of_spec {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hfg : subroutine_ok P addr (finishGrowSpecWithStack A hookStack)) :
    subroutine_ok P addr (finishGrow8ZeroCellsSpecG A hookStack) :=
  finish_grow_8_zero_cells_placed_of_spec hfg

theorem finish_grow_8_ne_cells_placed_of_spec {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hfg : subroutine_ok P addr (finishGrowSpecWithStack A hookStack)) :
    subroutine_ok P addr (finishGrow8NeCellsSpecG A hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow8NeCellsSpecG, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hstr, hlay⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, align, stride, bs⟩
  have hpre' : s0.mem ⊨ (finishGrowSpecWithStack A hookStack).pre hcall s0 ∗ R := by
    simp only [finishGrowSpecWithStack, hcall, FinishGrowCall.oldBuf, hcap, ite_false,
      memRegion_24, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs, hle, hpos, hstr, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrowSpecWithStack, finishGrow8NeCellsSpecG, hcall,
      FinishGrowCall.oldBuf, hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * stride.toNat), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, by simpa only [sepConj_assoc] using hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩
  · exact Or.inr hfail

private theorem finish_grow_8_ne_cells_of_spec {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hfg : subroutine_ok P addr (finishGrowSpecWithStack A hookStack)) :
    subroutine_ok P addr (finishGrow8NeCellsSpecG A hookStack) :=
  finish_grow_8_ne_cells_placed_of_spec hfg

theorem finish_grow_24_zero_cells_placed_of_spec {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hfg : subroutine_ok P addr (finishGrow1SpecWithStack A hookStack)) :
    subroutine_ok P addr (finishGrow24ZeroCellsSpecG A hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow24ZeroCellsSpecG, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hcap0, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrow1Call := ⟨out, 0#64, ptr, new, []⟩
  have hpre' : s0.mem ⊨ (finishGrow1SpecWithStack A hookStack).pre hcall s0 ∗ R := by
    simp only [finishGrow1SpecWithStack, hcall, FinishGrow1Call.oldBuf, ite_true,
      memRegion_24, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, fun _ => trivial, Nat.zero_le _, hle, hpos, hbound⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrow1SpecWithStack, finishGrow24ZeroCellsSpecG, hcall,
      FinishGrow1Call.oldBuf, ite_true, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', new, ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg0_err, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg0_ok, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩
  · exact Or.inr hfail

private theorem finish_grow_24_zero_cells_of_spec {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hfg : subroutine_ok P addr (finishGrow1SpecWithStack A hookStack)) :
    subroutine_ok P addr (finishGrow24ZeroCellsSpecG A hookStack) :=
  finish_grow_24_zero_cells_placed_of_spec hfg

theorem finish_grow_24_ne_cells_placed_of_spec {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hfg : subroutine_ok P addr (finishGrow1SpecWithStack A hookStack)) :
    subroutine_ok P addr (finishGrow24NeCellsSpecG A hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow24NeCellsSpecG, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hcap, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrow1Call := ⟨out, cap, ptr, new, bs⟩
  have hpre' : s0.mem ⊨ (finishGrow1SpecWithStack A hookStack).pre hcall s0 ∗ R := by
    simp only [finishGrow1SpecWithStack, hcall, FinishGrow1Call.oldBuf, hcap, ite_false,
      memRegion_24, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, False.elim, hbs, hle, hpos, hbound⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrow1SpecWithStack, finishGrow24NeCellsSpecG, hcall,
      FinishGrow1Call.oldBuf, hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', new, ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, by simpa only [sepConj_assoc] using hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩
  · exact Or.inr hfail

private theorem finish_grow_24_ne_cells_of_spec {A : RustAlloc} {P : Program} {addr : BitVec 64}
    {hookStack : Nat}
    (hfg : subroutine_ok P addr (finishGrow1SpecWithStack A hookStack)) :
    subroutine_ok P addr (finishGrow24NeCellsSpecG A hookStack) :=
  finish_grow_24_ne_cells_placed_of_spec hfg

theorem do_reserve_7_stride_raw_placed_ok_of_fg [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : (hookStack + 48) + 8 * 8 ≤ 2 ^ 64)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base
      (finishGrowSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H)
      (blkPl_320).base
      (withLsCodeLoaded lsmpl (doReserveStrideRawSpecWithStack A hookStack)) := by
  unfold withLsCodeLoaded doReserveStrideRawSpecWithStack
  simp only [stackAt_doReserve_gen _ hhook, sepExists_sepConj_right]
  have hpanic : ((blkPC_320).rebase (blkPl_320).base H).externAt? (lsρ spqrHandleErrorSym) =
      some Rust.panicked :=
    (spqr_externAt?_of_mem).trans h_panic
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, len, additional, align, stride⟩ := x
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = len := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hlen_le_cap : len ≤ cap.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hptr_ne : ptr ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hlay : LayoutOk (reserveCapStride stride.toNat cap.toNat len additional * stride.toNat) align.toNat := by
    assumption
  have hsz_pos : 0 < reserveCapStride stride.toNat cap.toNat len additional * stride.toNat := hlay.1
  have hpow : ∃ k, align.toNat = 2 ^ k := hlay.2.1
  have hbound :
      reserveCapStride stride.toNat cap.toNat len additional * stride.toNat + align.toNat ≤ 2 ^ 63 :=
    hlay.2.2
  have halign_pos : 1 ≤ align.toNat := by
    rcases hpow with ⟨k, hk⟩; rw [hk]; exact Nat.one_le_two_pow
  have hmin_ge : 4 ≤ reserveMinCap stride.toNat := by
    unfold reserveMinCap; split <;> omega
  have hnew_lt63 : reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63 := by
    have : reserveCapStride stride.toNat cap.toNat len additional * 1 ≤
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat :=
      Nat.mul_le_mul_left _ hstr_pos
    omega
  have hmax : max (max (len + additional) (2 * cap.toNat)) (reserveMinCap stride.toNat) < 2 ^ 63 :=
    hnew_lt63
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_stride_eq (stride := stride) (cap := cap) hx1_eq hx2_eq hnew_lt63
  let new := BitVec.ofNat 64 (reserveCapStride stride.toNat cap.toNat len additional)
  have hnew_toNat : new.toNat = reserveCapStride stride.toNat cap.toNat len additional := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hnew_pos : 0 < new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hnew_lay : LayoutOk (new.toNat * stride.toNat) align.toNat := by
    rw [hnew_toNat]; exact hlay
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * stride.toNat = 0 := Nat.zero_mul stride.toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 :
        (if (if (stride == 1#64) = true then 8#64 else 4#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
          else 0#64
         else if (stride == 1#64) = true then 8#64 else 4#64) = new := hnew_eq
    have hmul_eq : reserveCapStride stride.toNat 0 len additional * stride.toNat =
        new.toNat * stride.toNat := by
      rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.zero_mod, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_320).base + 88#64)
    wp_steps_lscl (lsmpl.base 361)
    have hfg0 := lscall_blk (callerProg := (blkPC_320).rebase (blkPl_320).base H)
      (finish_grow_8_zero_cells_of_spec hfg) ‹_›
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, align, stride, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq :
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat - bs.length =
          new.toNat * stride.toNat - bs.length := by rw [hnew_toNat]
    have hmul_eq :
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat =
          new.toNat * stride.toNat := by rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_320).base + 88#64)
    wp_steps_lscl (lsmpl.base 361)
    have hfg1 := lscall_blk (callerProg := (blkPC_320).rebase (blkPl_320).base H)
      (finish_grow_8_ne_cells_of_spec hfg) ‹_›
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, align, stride, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

theorem do_reserve_2_raw32_placed_ok_of_fg [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : (hookStack + 32) + 8 * 8 ≤ 2 ^ 64)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (blkPl_160).base
      (finishGrow1SpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H)
      (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32SpecWithStack A hookStack)) := by
  unfold withLsCodeLoaded doReserve1Raw32SpecWithStack
  simp only [stackAt_doReserve32_gen _ hhook, sepExists_sepConj_right]
  have hpanic : ((blkPC_157).rebase (blkPl_157).base H).externAt? (lsρ spqrHandleErrorSym) =
      some Rust.panicked :=
    (spqr_externAt?_of_mem).trans h_panic
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, additional⟩ := x
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = bs.length := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63 := by
    dsimp only [reserveCap] at h_1 ⊢; omega
  have hmax : max (max (bs.length + additional) (2 * cap.toNat)) 8 + 1 ≤ 2 ^ 63 := hbound
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_eq (cap := cap) hx1_eq hx2_eq hbound
  let new := BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)
  have hnew_toNat : new.toNat = reserveCap cap.toNat bs.length additional := by
    dsimp [new, reserveCap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_pos : 0 < new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbs_le_cap)
    subst hbs
    have hnew_eq0 :
        (if (8#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
          else 0#64
         else 8#64) = new := hnew_eq
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero]
    apply SepWPp.of_sepWP (mid := (blkPl_157).base + 68#64)
    wp_steps_lscl (lsmpl.base 160)
    have hfg0 := lscall_blk (callerProg := (blkPC_157).rebase (blkPl_157).base H)
      (finish_grow_24_zero_cells_of_spec hfg) ‹_›
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq : reserveCap cap.toNat bs.length additional - bs.length = new.toNat - bs.length := by
      rw [hnew_toNat]
    rw [hsub_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_157).base + 68#64)
    wp_steps_lscl (lsmpl.base 160)
    have hfg1 := lscall_blk (callerProg := (blkPC_157).rebase (blkPl_157).base H)
      (finish_grow_24_ne_cells_of_spec hfg) ‹_›
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

theorem do_reserve_4_raw32_placed_ok_of_fg [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : (hookStack + 32) + 8 * 8 ≤ 2 ^ 64)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (blkPl_221).base
      (finishGrow1SpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_218).rebase (blkPl_218).base H)
      (blkPl_218).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32SpecWithStack A hookStack)) := by
  unfold withLsCodeLoaded doReserve1Raw32SpecWithStack
  simp only [stackAt_doReserve32_gen _ hhook, sepExists_sepConj_right]
  have hpanic : ((blkPC_218).rebase (blkPl_218).base H).externAt? (lsρ spqrHandleErrorSym) =
      some Rust.panicked :=
    (spqr_externAt?_of_mem).trans h_panic
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, additional⟩ := x
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = bs.length := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63 := by
    dsimp only [reserveCap] at h_1 ⊢; omega
  have hmax : max (max (bs.length + additional) (2 * cap.toNat)) 8 + 1 ≤ 2 ^ 63 := hbound
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_eq (cap := cap) hx1_eq hx2_eq hbound
  let new := BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)
  have hnew_toNat : new.toNat = reserveCap cap.toNat bs.length additional := by
    dsimp [new, reserveCap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_pos : 0 < new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbs_le_cap)
    subst hbs
    have hnew_eq0 :
        (if (8#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
          else 0#64
         else 8#64) = new := hnew_eq
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero]
    apply SepWPp.of_sepWP (mid := (blkPl_218).base + 68#64)
    wp_steps_lscl (lsmpl.base 221)
    have hfg0 := lscall_blk (callerProg := (blkPC_218).rebase (blkPl_218).base H)
      (finish_grow_24_zero_cells_of_spec hfg) ‹_›
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq : reserveCap cap.toNat bs.length additional - bs.length = new.toNat - bs.length := by
      rw [hnew_toNat]
    rw [hsub_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_218).base + 68#64)
    wp_steps_lscl (lsmpl.base 221)
    have hfg1 := lscall_blk (callerProg := (blkPC_218).rebase (blkPl_218).base H)
      (finish_grow_24_ne_cells_of_spec hfg) ‹_›
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

private theorem do_reserve_7_raw_placed_of_stride [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hs : subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserveStrideRawSpecWithStack A hookStack))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack A hookStack)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [doReserveRawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound⟩, hmem⟩
  let xs : DoReserveStrideCall := ⟨x.v, x.cap, x.ptr, x.bs, x.bs.length, x.additional, 1#64, 1#64⟩
  have hlay : LayoutOk (reserveCap x.cap.toNat x.bs.length x.additional) 1 := by
    refine ⟨by dsimp [reserveCap]; omega, ⟨0, rfl⟩, by omega⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (doReserveStrideRawSpecWithStack A hookStack)).pre xs s0 ∗ R := by
    simp only [doReserveStrideRawSpecWithStack, xs, BitVec.toNat_ofNat, Nat.one_mod,
      reserveCapStride_one, Nat.mul_one, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hlen, hptr, by decide, hlay⟩, hmem⟩
  refine hs.mono_outcome xs R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [doReserveStrideRawSpecWithStack, doReserveRawSpecWithStack, xs,
      BitVec.toNat_ofNat, Nat.one_mod, reserveCapStride_one, Nat.mul_one, Nat.mod_one, and_true]
      at hq ⊢
    exact hq
  · exact Or.inr hfail

private theorem do_reserve_vec_placed_of_raw [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hraw : subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack A hookStack))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserveSpecWithStack A hookStack)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [doReserveSpecWithStack, vecU8At_eq, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ⟨hlen, _hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack A hookStack)).pre x s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [doReserveRawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound⟩, ?_⟩
    ac_nf at hmem ⊢
  refine hraw.mono_outcome x (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R)
    s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _hex, hq⟩ | ⟨_hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [doReserveRawSpecWithStack, doReserveSpecWithStack, vecU8At_eq] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hp', hmem⟩
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by
      dsimp [reserveCap] at hbound ⊢; omega
    have htoNat : (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
        reserveCap x.cap.toNat x.bs.length x.additional := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
      dsimp [reserveCap]; omega
    have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by
      omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [htoNat] at this
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at this
      dsimp [reserveCap] at this; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, htoNat]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
    rwa [doReserve_post_repack]
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [doReserveRawSpecWithStack, doReserveSpecWithStack] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

private theorem do_reserve_raw1_placed_of_raw32 [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hhook : (hookStack + 48) + 64 ≤ 2 ^ 64)
    (h32 : subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserve1Raw32SpecWithStack A hookStack))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserve1RawSpecWithStack A hookStack)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [doReserve1RawSpecWithStack, stackAt_doReserve_eq_32_gen _ hhook, sepConj_assoc] at hpre
  let btm := memRegion (s0.sp - BitVec.ofNat 64 ((hookStack + 48) + 64)) 16
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (doReserve1Raw32SpecWithStack A hookStack)).pre x s0 ∗
      (btm ∗ R) := by
    simp only [doReserve1Raw32SpecWithStack, btm, sepConj_assoc]
    ac_nf at hpre ⊢
  refine h32.mono_outcome x (btm ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _hex, hq⟩ | ⟨_hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [doReserve1Raw32SpecWithStack, doReserve1RawSpecWithStack,
      stackAt_doReserve_eq_32_gen _ hhook, btm, sepConj_assoc] at hq ⊢
    ac_nf at hq ⊢
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [doReserve1Raw32SpecWithStack, doReserve1RawSpecWithStack] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

private theorem do_reserve_raw_placed_of_raw1 [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (h1 : subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserve1RawSpecWithStack A hookStack))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack A hookStack)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [doReserveRawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, _, _, hlen, hptr, hbound⟩, hmem⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (doReserve1RawSpecWithStack A hookStack)).pre x s0 ∗ R := by
    simp only [doReserve1RawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlen, hptr, hbound⟩, hmem⟩
  exact h1.mono_outcome x R s0 hpc hrun hpre' hsp fun _ hout => hout

/-- Block 320 (`do_reserve_and_handle [local#7]`) meets `withLsCodeLoaded lsmpl (doReserveStrideRawSpec A)`. -/
theorem do_reserve_7_stride_raw_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H)
      (blkPl_320).base
      (withLsCodeLoaded lsmpl (doReserveStrideRawSpec A)) :=
  do_reserve_7_stride_raw_placed_ok_of_fg (hookStack := allocHookStack) (by decide) h_panic
    (finish_grow_8_placed_ok hshim halloc hrealloc)

theorem do_reserve_7_stride_raw_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H)
      (blkPl_320).base
      (withLsCodeLoaded lsmpl (doReserveStrideRawSpecX A)) :=
  do_reserve_7_stride_raw_placed_ok_of_fg (hookStack := extHookStack) (by decide) h_panic
    (finish_grow_8_placed_ok_x hshim halloc hrealloc)

theorem do_reserve_7_raw_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H)
      (blkPl_320).base
      (withLsCodeLoaded lsmpl (doReserveRawSpec A)) :=
  do_reserve_7_raw_placed_of_stride
    (do_reserve_7_stride_raw_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_7_raw_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H)
      (blkPl_320).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecX A)) :=
  do_reserve_7_raw_placed_of_stride (hookStack := extHookStack)
    (do_reserve_7_stride_raw_placed_ok_x h_panic hshim halloc hrealloc)

/-- Block 320 (`do_reserve_and_handle [local#7]`) meets `withLsCodeLoaded lsmpl (doReserveSpec A)`. -/
theorem do_reserve_7_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H)
      (blkPl_320).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)) :=
  do_reserve_vec_placed_of_raw
    (do_reserve_7_raw_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_7_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H)
      (blkPl_320).base
      (withLsCodeLoaded lsmpl (doReserveSpecX A)) :=
  do_reserve_vec_placed_of_raw (hookStack := extHookStack)
    (do_reserve_7_raw_placed_ok_x h_panic hshim halloc hrealloc)

/-- Block 157 (`do_reserve_and_handle [local#2]`) meets `withLsCodeLoaded lsmpl (doReserve1Raw32Spec A)`. -/
theorem do_reserve_2_raw32_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H)
      (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32Spec A)) :=
  do_reserve_2_raw32_placed_ok_of_fg (hookStack := allocHookStack) (by decide) h_panic
    (finish_grow_2_placed_ok hshim halloc hrealloc)

theorem do_reserve_2_raw32_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H)
      (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32SpecX A)) :=
  do_reserve_2_raw32_placed_ok_of_fg (hookStack := extHookStack) (by decide) h_panic
    (finish_grow_2_placed_ok_x hshim halloc hrealloc)

/-- Block 218 (`do_reserve_and_handle [local#4]`) meets `withLsCodeLoaded lsmpl (doReserve1Raw32Spec A)`. -/
theorem do_reserve_4_raw32_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_218).rebase (blkPl_218).base H)
      (blkPl_218).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32Spec A)) :=
  do_reserve_4_raw32_placed_ok_of_fg (hookStack := allocHookStack) (by decide) h_panic
    (finish_grow_4_placed_ok hshim halloc hrealloc)

theorem do_reserve_4_raw32_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_218).rebase (blkPl_218).base H)
      (blkPl_218).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32SpecX A)) :=
  do_reserve_4_raw32_placed_ok_of_fg (hookStack := extHookStack) (by decide) h_panic
    (finish_grow_4_placed_ok_x hshim halloc hrealloc)

theorem do_reserve_2_raw1_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H)
      (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserve1RawSpec A)) :=
  do_reserve_raw1_placed_of_raw32 (hookStack := allocHookStack) (by decide)
    (do_reserve_2_raw32_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_2_raw1_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H)
      (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserve1RawSpecX A)) :=
  do_reserve_raw1_placed_of_raw32 (hookStack := extHookStack) (by decide)
    (do_reserve_2_raw32_placed_ok_x h_panic hshim halloc hrealloc)

theorem do_reserve_2_raw_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H)
      (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserveRawSpec A)) :=
  do_reserve_raw_placed_of_raw1
    (do_reserve_2_raw1_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_2_raw_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H)
      (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecX A)) :=
  do_reserve_raw_placed_of_raw1 (hookStack := extHookStack)
    (do_reserve_2_raw1_placed_ok_x h_panic hshim halloc hrealloc)

/-- Block 157 (`do_reserve_and_handle [local#2]`) meets `withLsCodeLoaded lsmpl (doReserveSpec A)`. -/
theorem do_reserve_2_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H)
      (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)) :=
  do_reserve_vec_placed_of_raw
    (do_reserve_2_raw_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_2_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H)
      (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserveSpecX A)) :=
  do_reserve_vec_placed_of_raw (hookStack := extHookStack)
    (do_reserve_2_raw_placed_ok_x h_panic hshim halloc hrealloc)

theorem do_reserve_4_raw1_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_218).rebase (blkPl_218).base H)
      (blkPl_218).base
      (withLsCodeLoaded lsmpl (doReserve1RawSpec A)) :=
  do_reserve_raw1_placed_of_raw32 (hookStack := allocHookStack) (by decide)
    (do_reserve_4_raw32_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_4_raw1_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_218).rebase (blkPl_218).base H)
      (blkPl_218).base
      (withLsCodeLoaded lsmpl (doReserve1RawSpecX A)) :=
  do_reserve_raw1_placed_of_raw32 (hookStack := extHookStack) (by decide)
    (do_reserve_4_raw32_placed_ok_x h_panic hshim halloc hrealloc)

theorem do_reserve_4_raw_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_218).rebase (blkPl_218).base H)
      (blkPl_218).base
      (withLsCodeLoaded lsmpl (doReserveRawSpec A)) :=
  do_reserve_raw_placed_of_raw1
    (do_reserve_4_raw1_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_4_raw_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_218).rebase (blkPl_218).base H)
      (blkPl_218).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecX A)) :=
  do_reserve_raw_placed_of_raw1 (hookStack := extHookStack)
    (do_reserve_4_raw1_placed_ok_x h_panic hshim halloc hrealloc)

/-- Block 218 (`do_reserve_and_handle [local#4]`) meets `withLsCodeLoaded lsmpl (doReserveSpec A)`. -/
theorem do_reserve_4_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_218).rebase (blkPl_218).base H)
      (blkPl_218).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)) :=
  do_reserve_vec_placed_of_raw
    (do_reserve_4_raw_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_4_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_218).rebase (blkPl_218).base H)
      (blkPl_218).base
      (withLsCodeLoaded lsmpl (doReserveSpecX A)) :=
  do_reserve_vec_placed_of_raw (hookStack := extHookStack)
    (do_reserve_4_raw_placed_ok_x h_panic hshim halloc hrealloc)

end CryptoVerification.SpqrV1.Alloc
