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
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `RawVecInner::grow_amortized` and `RawVec<(&str, &str)>::grow_one`

Verifies `<alloc::raw_vec::RawVecInner>::grow_amortized` (`0x4abf0`, block 260) and
`<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one` (`0x4ab28`, block 258) for both
initialized byte prefixes (`*BsSpec`) and uninitialized buffers (`bs = []`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace GrowAmortizedNorm

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

end GrowAmortizedNorm

open GrowAmortizedNorm

/-! ## Stack Budgets and Capacity Helper -/

/-- Stack budget of `grow_amortized`: `finishGrow32Stack + 64` (`4256` B). -/
abbrev growAmortizedStack : Nat := finishGrow32Stack + 64

/-- Stack budget of `RawVec<(&str, &str)>::grow_one`: `growAmortizedStack + 16`. -/
abbrev growOneStrPairStack : Nat := growAmortizedStack + 16

/-- Amortized element capacity `max (2 * cap.toNat) 4` computed by `grow_amortized`. -/
def newCap32 (cap : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (max (2 * cap.toNat) 4)

theorem newCap32_toNat {cap : BitVec 64} (h : cap.toNat < 2 ^ 32) :
    (newCap32 cap).toNat = max (2 * cap.toNat) 4 := by
  unfold newCap32
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem grow_amortized_new_eq {cap : BitVec 64} (h : cap.toNat < 2 ^ 32) :
    (if (4#64).ult (if (cap + 1#64).ule (cap <<< 1) = true then cap <<< 1 else cap + 1#64) = true then
      if (cap + 1#64).ule (cap <<< 1) = true then cap <<< 1 else cap + 1#64
    else 4#64) = newCap32 cap := by
  have hadd : (cap + 1#64).toNat = cap.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hm1 : (if (cap + 1#64).ule (cap <<< 1) = true then cap <<< 1 else cap + 1#64).toNat =
      max (2 * cap.toNat) (cap.toNat + 1) := by
    by_cases hc1 : (cap + 1#64).ule (cap <<< 1) = true
    · simp only [hc1, ite_true, hsh]
      rw [BitVec.ule_eq_decide, decide_eq_true_eq, hadd, hsh] at hc1
      omega
    · simp only [hc1, Bool.false_eq_true, ite_false, hadd]
      rw [BitVec.ule_eq_decide, decide_eq_true_eq, hadd, hsh] at hc1
      omega
  apply BitVec.eq_of_toNat_eq
  rw [newCap32_toNat h]
  generalize (if (cap + 1#64).ule (cap <<< 1) = true then cap <<< 1 else cap + 1#64) = m1 at hm1 ⊢
  by_cases hc2 : (4#64).ult m1 = true
  · simp only [hc2, ite_true, hm1]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm1] at hc2
    change 4 < max (2 * cap.toNat) (cap.toNat + 1) at hc2
    omega
  · simp only [hc2, Bool.false_eq_true, ite_false]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm1] at hc2
    change ¬ 4 < max (2 * cap.toNat) (cap.toNat + 1) at hc2
    change 4 = max (2 * cap.toNat) 4
    omega

private theorem fnAddr_back_164 {P : Program} {b : BitVec 64} {X : String → Option (State → State)}
    {name callee : String} {off coff : Nat}
    (h1 : P.fnOff name = off) (h2 : P.fnOff callee = coff)
    (hk : coff + 164 = off) :
    (P.rebase b X).fnAddr callee =
      (P.rebase b X).fnAddr name + 18446744073709551452#64 := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, h1, h2, ← hk]
  bv_omega

private theorem stackAt_growAmortized (sp : BitVec 64) :
    stackAt sp growAmortizedStack =
      stackAt (sp - 64#64) finishGrow32Stack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_cells sp 4128 8 (by decide)
  change stackAt sp growAmortizedStack =
    stackAt (sp - 64#64) finishGrow32Stack ∗ cells (sp - 64#64) 8 at h1
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

private theorem stackAt_growOneStrPair (sp : BitVec 64) :
    stackAt sp growOneStrPairStack =
      stackAt (sp - 16#64) growAmortizedStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64,
          ((sp - 16#64) ↦₆₄ v0) ∗ ((sp - 8#64) ↦₆₄ v1)) := by
  have h1 := ProofLib.stackAt_split_cells sp 4192 2 (by decide)
  change stackAt sp growOneStrPairStack =
    stackAt (sp - 16#64) growAmortizedStack ∗ cells (sp - 16#64) 2 at h1
  have hc2 : cells (sp - 16#64) 2 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64,
        ((sp - 16#64) ↦₆₄ v0) ∗ ((sp - 8#64) ↦₆₄ v1)) := by
    cells_unfold
  rw [h1, hc2]

/-! ## Cell-Unfolded `finish_grow [local#7]` Wrappers -/

private theorem pull_fg7_err0 (P1 P2 P3 P4 P5 R : SepProp) (φ : Prop) :
    (P1 ∗ P2 ∗ P3 ∗ ⌜φ⌝ ∗ P4 ∗ P5) ∗ R =
      ⌜φ⌝ ∗ ((P4 ∗ P5 ∗ P1 ∗ P2 ∗ P3) ∗ R) := by ac_rfl

private theorem pull_fg7_post (P1 P2 P3 L1 L2 L3 P4 P5 R : SepProp) (φ : Prop) :
    (P1 ∗ P2 ∗ P3 ∗ (⌜φ⌝ ∗ L1 ∗ L2 ∗ L3) ∗ P4 ∗ P5) ∗ R =
      ⌜φ⌝ ∗ ((L1 ∗ L2 ∗ L3 ∗ P4 ∗ P5 ∗ P1 ∗ P2 ∗ P3) ∗ R) := by ac_rfl

private abbrev FG7Ghost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

private def finishGrow7ZeroCellsSpec (A : RustAlloc) : Spec FG7Ghost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧
      cap.toNat ≤ new.toNat ∧ 0 < new.toNat ∧ new.toNat * 32 + 8 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ stackAt fsp finishGrow32Stack
  post := fun (out, _cap, _ptr, new, bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (new.toNat * 32) 8 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 32 - bs.length)) ∗
      A.pool ∗ stackAt fsp finishGrow32Stack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem finish_grow_7_zero_cells_of_fg7 {A : RustAlloc} {P : Program} {addr : BitVec 64}
    (hfg : subroutine_ok P addr (finishGrow7Spec A)) :
    subroutine_ok P addr (finishGrow7ZeroCellsSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow7ZeroCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hcap0, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrow1Call := ⟨out, 0#64, ptr, new, []⟩
  have hpre' : s0.mem ⊨ (finishGrow7Spec A).pre hcall s0 ∗ R := by
    simp only [finishGrow7Spec, hcall, FinishGrow1Call.oldBuf32, ite_true,
      memRegion_24, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, fun _ => trivial, Nat.zero_le _, hle, hpos, hbound⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrow7Spec, finishGrow7ZeroCellsSpec, hcall, FinishGrow1Call.oldBuf32,
      ite_true, sepConj_emp, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * 32), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg7_err0, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1, hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg7_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩
  · exact Or.inr hfail

private theorem finish_grow_7_zero_cells_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow7Name)
      (finishGrow7ZeroCellsSpec A) :=
  finish_grow_7_zero_cells_of_fg7 (finish_grow_7_ok_ext hA)

private def finishGrow7NeCellsSpec (A : RustAlloc) : Spec FG7Ghost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.sp = fsp ∧ cap ≠ 0#64 ∧
      bs.length ≤ cap.toNat * 32 ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat * 32 + 8 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr (cap.toNat * 32) 8 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 32 - bs.length) ∗
    A.pool ∗ stackAt fsp finishGrow32Stack
  post := fun (out, cap, ptr, new, bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          A.live ptr (cap.toNat * 32) 8 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 32 - bs.length)
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (new.toNat * 32) 8 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 32 - bs.length)) ∗
      A.pool ∗ stackAt fsp finishGrow32Stack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem finish_grow_7_ne_cells_of_fg7 {A : RustAlloc} {P : Program} {addr : BitVec 64}
    (hfg : subroutine_ok P addr (finishGrow7Spec A)) :
    subroutine_ok P addr (finishGrow7NeCellsSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow7NeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hcap, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrow1Call := ⟨out, cap, ptr, new, bs⟩
  have hpre' : s0.mem ⊨ (finishGrow7Spec A).pre hcall s0 ∗ R := by
    simp only [finishGrow7Spec, hcall, FinishGrow1Call.oldBuf32, hcap, ite_false,
      memRegion_24, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, False.elim, hbs, hle, hpos, hbound⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrow7Spec, finishGrow7NeCellsSpec, hcall, FinishGrow1Call.oldBuf32,
      hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * 32), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg7_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg7_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩
  · exact Or.inr hfail

private theorem finish_grow_7_ne_cells_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow7Name)
      (finishGrow7NeCellsSpec A) :=
  finish_grow_7_ne_cells_of_fg7 (finish_grow_7_ok_ext hA)

/-! ## `RawVecInner::grow_amortized` -/

abbrev growAmortizedName : String :=
  "<alloc::raw_vec::RawVecInner>::grow_amortized"

abbrev growOneStrPairName : String :=
  "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one"

/-- Ghost parameters for `grow_amortized` and `RawVec<(&str, &str)>::grow_one`. -/
structure GrowAmortizedCall where
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Pre-call 32-byte-stride heap buffer for `GrowAmortizedCall`. -/
def GrowAmortizedCall.oldBuf (A : RustAlloc) (x : GrowAmortizedCall) : SepProp :=
  if x.cap = 0#64 then emp
  else
    A.live x.ptr (x.cap.toNat * 32) 8 ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat * 32 - x.bs.length)

/-- Contract of `RawVecInner::grow_amortized` preserving an initialized byte prefix `x.bs`. -/
def growAmortizedBsSpec (A : RustAlloc) : Spec GrowAmortizedCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v ∧ s.readReg64 .x1 = x.cap ∧
      x.bs.length ≤ x.cap.toNat * 32 ∧ x.cap.toNat < 2 ^ 32 ∧ x.ptr ≠ 0#64⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    x.oldBuf A ∗ A.pool ∗ stackAt s.sp growAmortizedStack
  post := fun x s0 sf =>
    ∃∗ res : BitVec 64, ∃∗ p' : BitVec 64,
      (if res = 0xffffffffffffffff#64 then
        ⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧
          sf.trace = s0.trace⌝ ∗
        (x.v ↦₆₄ newCap32 x.cap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
        A.live p' ((newCap32 x.cap).toNat * 32) 8 ∗ (p' ↦ₛ x.bs) ∗
        memRegion (p' + BitVec.ofNat 64 x.bs.length) ((newCap32 x.cap).toNat * 32 - x.bs.length)
       else
        ⌜res = 8#64 ∧ sf.readReg64 .x0 = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
        (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗ x.oldBuf A) ∗
      A.pool ∗ stackAt s0.sp growAmortizedStack

/-- `grow_amortized` meets `growAmortizedBsSpec A`. -/
theorem grow_amortized_bs_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growAmortizedName)
      (growAmortizedBsSpec A) := by
  unfold growAmortizedBsSpec GrowAmortizedCall.oldBuf
  simp only [stackAt_growAmortized, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff growAmortizedName = 0x457f8 :=
    libsignalSessionCode_fnOff_0x457f8
  have hfg0 := finish_grow_7_zero_cells_ok_ext hA
  have hfg1 := finish_grow_7_ne_cells_ok_ext hA
  rw [fnAddr_back_164 (name := growAmortizedName)
    hfn libsignalSessionCode_fnOff_0x45754 (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn 0x457f8 124
  dsimp only [tripleRatchetProgAtExt] at hfg0 hfg1 ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr growAmortizedName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hnew_eq := grow_amortized_new_eq h_4
  have hnew_toNat : (newCap32 cap).toNat = max (2 * cap.toNat) 4 := newCap32_toNat h_4
  have hcap_le_new : cap.toNat ≤ (newCap32 cap).toNat := by omega
  have hnew_pos : 0 < (newCap32 cap).toNat := by omega
  have hnew_bound : (newCap32 cap).toNat * 32 + 8 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero h_3)
    subst hbs
    simp only [ite_true, emp_sepConj, pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero]
    wp_steps
    wp_apply
    by_cases htag : w = 1#64
    · subst htag
      wp_simp_pre [ite_true, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw1, htrace⟩
      subst hw1
      wp_steps
      apply SepWP.instantiate_post_exists 8#64
      apply SepWP.instantiate_post_exists 0#64
      simp only [(by decide : (8#64 : BitVec 64) = 0xffffffffffffffff#64 ↔ False), ite_false]
      wp_done
    · wp_simp_pre [htag, ite_false, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw0, hp', halign, htrace⟩
      subst hw0
      wp_steps
      apply SepWP.instantiate_post_exists 0xffffffffffffffff#64
      apply SepWP.instantiate_post_exists w_1
      simp only [ite_true, (by decide : newCap32 0#64 = 4#64)]
      wp_done
  · wp_simp_pre [hcap0, ite_false]
    wp_steps
    wp_apply
    by_cases htag : w = 1#64
    · subst htag
      wp_simp_pre [ite_true, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw1, htrace⟩
      subst hw1
      wp_steps
      apply SepWP.instantiate_post_exists 8#64
      apply SepWP.instantiate_post_exists 0#64
      simp only [(by decide : (8#64 : BitVec 64) = 0xffffffffffffffff#64 ↔ False), hcap0, ite_false]
      wp_done
    · wp_simp_pre [htag, ite_false, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw0, hp', halign, htrace⟩
      subst hw0
      wp_steps
      apply SepWP.instantiate_post_exists 0xffffffffffffffff#64
      apply SepWP.instantiate_post_exists w_1
      simp only [ite_true]
      wp_done

/-- Contract of `RawVecInner::grow_amortized` on an uninitialized buffer (`bs = []`). -/
def growAmortizedSpec (A : RustAlloc) : Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (v, cap, ptr) s =>
    ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x1 = cap ∧
      cap.toNat < 2 ^ 32 ∧ ptr ≠ 0#64⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) ∗
    A.pool ∗ stackAt s.sp growAmortizedStack
  post := fun (v, cap, ptr) s0 sf =>
    ∃∗ res : BitVec 64, ∃∗ p' : BitVec 64,
      (if res = 0xffffffffffffffff#64 then
        ⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧
          sf.trace = s0.trace⌝ ∗
        (v ↦₆₄ newCap32 cap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' ((newCap32 cap).toNat * 32) 8 ∗ memRegion p' ((newCap32 cap).toNat * 32)
       else
        ⌜res = 8#64 ∧ sf.readReg64 .x0 = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        (if cap = 0#64 then emp
         else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32))) ∗
      A.pool ∗ stackAt s0.sp growAmortizedStack

theorem grow_amortized_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growAmortizedName)
      (growAmortizedSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨v, cap, ptr⟩ R s0 hpc hrun hpre hsp => ?_
  let x : GrowAmortizedCall := ⟨v, cap, ptr, []⟩
  have hpre' : s0.mem ⊨ (growAmortizedBsSpec A).pre x s0 ∗ R := by
    simp only [growAmortizedSpec, growAmortizedBsSpec, GrowAmortizedCall.oldBuf, x,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hcap, hptr⟩, hmem⟩
    exact ⟨⟨hx0, hx1, Nat.zero_le _, hcap, hptr⟩, hmem⟩
  refine (grow_amortized_bs_ok_ext hA).mono_outcome x R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [growAmortizedSpec, growAmortizedBsSpec, GrowAmortizedCall.oldBuf, x,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj] using hq
  · exact Or.inr hfail

/-! ## `RawVec<(&str, &str)>::grow_one` -/

/-- Contract of `RawVec<(&str, &str)>::grow_one` preserving an initialized byte prefix `x.bs`. -/
def growOneStrPairBsSpec (A : RustAlloc) : Spec GrowAmortizedCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v ∧
      x.bs.length ≤ x.cap.toNat * 32 ∧ x.cap.toNat < 2 ^ 32 ∧ x.ptr ≠ 0#64⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    x.oldBuf A ∗ A.pool ∗ stackAt s.sp growOneStrPairStack
  post := fun x s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      (x.v ↦₆₄ newCap32 x.cap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' ((newCap32 x.cap).toNat * 32) 8 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) ((newCap32 x.cap).toNat * 32 - x.bs.length) ∗
      A.pool ∗ stackAt s0.sp growOneStrPairStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private def growAmortizedCallSpec (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (v, cap, ptr, bs, gsp) s =>
    ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x1 = cap ∧ s.sp = gsp ∧
      bs.length ≤ cap.toNat * 32 ∧ cap.toNat < 2 ^ 32 ∧ ptr ≠ 0#64⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 32) 8 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 32 - bs.length)) ∗
    A.pool ∗ stackAt gsp growAmortizedStack
  post := fun (v, cap, ptr, bs, gsp) s0 sf =>
    ∃∗ res : BitVec 64, ∃∗ p' : BitVec 64,
      (if res = 0xffffffffffffffff#64 then
        ⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧
          sf.trace = s0.trace⌝ ∗
        (v ↦₆₄ newCap32 cap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' ((newCap32 cap).toNat * 32) 8 ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 bs.length) ((newCap32 cap).toNat * 32 - bs.length)
       else
        ⌜res = 8#64 ∧ sf.readReg64 .x0 = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        (if cap = 0#64 then emp
         else A.live ptr (cap.toNat * 32) 8 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 32 - bs.length))) ∗
      A.pool ∗ stackAt gsp growAmortizedStack

private theorem grow_amortized_call_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growAmortizedName)
      (growAmortizedCallSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨v, cap, ptr, bs, gsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [growAmortizedCallSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hgsp, hbs, hcap, hptr⟩, hmem⟩
  subst hgsp
  let x : GrowAmortizedCall := ⟨v, cap, ptr, bs⟩
  have hpre' : s0.mem ⊨ (growAmortizedBsSpec A).pre x s0 ∗ R := by
    simp only [growAmortizedBsSpec, GrowAmortizedCall.oldBuf, x, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hbs, hcap, hptr⟩, hmem⟩
  exact (grow_amortized_bs_ok_ext hA).mono_outcome x R s0 hpc hrun hpre' hsp fun _ hout => hout

/-- `RawVec<(&str, &str)>::grow_one` meets `growOneStrPairBsSpec A`. -/
theorem grow_one_str_pair_bs_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneStrPairName)
      (growOneStrPairBsSpec A) := by
  unfold growOneStrPairBsSpec GrowAmortizedCall.oldBuf
  simp only [stackAt_growOneStrPair, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff growOneStrPairName = 0x45730 :=
    libsignalSessionCode_fnOff_0x45730
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := growOneStrPairName) (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x45730))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hga := grow_amortized_call_ok_ext hA
  rw [Program.fnAddr_rel (name := growOneStrPairName)
    hfn libsignalSessionCode_fnOff_0x457f8 (k := 200) (by decide)] at hga
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn 0x45730 36
  dsimp only [tripleRatchetProgAtExt] at hpanic hga ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr growOneStrPairName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  apply SepWPp.of_sepWP (mid := entry + 16#64)
  wp_steps
  wp_call hga (v, cap, ptr, bs, s0.sp - 16#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hres : w = 0xffffffffffffffff#64
  · conv => arg 4; simp only [hres, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0, hp', halign, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    apply SepWP.instantiate_post_exists w_1
    wp_done
  · conv => arg 4; simp only [hres, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hw8, hx0, htrace⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x45730))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm

/-- Contract of `RawVec<(&str, &str)>::grow_one` on an uninitialized buffer (`bs = []`). -/
def growOneStrPairSpec (A : RustAlloc) : Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (v, cap, ptr) s =>
    ⌜s.readReg64 .x0 = v ∧ cap.toNat < 2 ^ 32 ∧ ptr ≠ 0#64⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) ∗
    A.pool ∗ stackAt s.sp growOneStrPairStack
  post := fun (v, cap, _ptr) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      (v ↦₆₄ newCap32 cap) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' ((newCap32 cap).toNat * 32) 8 ∗ memRegion p' ((newCap32 cap).toNat * 32) ∗
      A.pool ∗ stackAt s0.sp growOneStrPairStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem grow_one_str_pair_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneStrPairName)
      (growOneStrPairSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨v, cap, ptr⟩ R s0 hpc hrun hpre hsp => ?_
  let x : GrowAmortizedCall := ⟨v, cap, ptr, []⟩
  have hpre' : s0.mem ⊨ (growOneStrPairBsSpec A).pre x s0 ∗ R := by
    simp only [growOneStrPairSpec, growOneStrPairBsSpec, GrowAmortizedCall.oldBuf, x,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hcap, hptr⟩, hmem⟩
    exact ⟨⟨hx0, Nat.zero_le _, hcap, hptr⟩, hmem⟩
  refine (grow_one_str_pair_bs_ok_ext hA).mono_outcome x R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [growOneStrPairSpec, growOneStrPairBsSpec, GrowAmortizedCall.oldBuf, x,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj] using hq
  · exact Or.inr hfail

/-! ## Relocatable Contracts (Blocks 260 and 258) -/

theorem grow_amortized_bs_placed_ok_of_fg [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hfg : subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (blkPl_259).base (finishGrow7Spec A)) :
    subroutine_ok ((blkPC_260).rebase (blkPl_260).base H)
      (blkPl_260).base
      (withLsCodeLoaded lsmpl (growAmortizedBsSpec A)) := by
  unfold withLsCodeLoaded growAmortizedBsSpec GrowAmortizedCall.oldBuf
  simp only [stackAt_growAmortized, sepExists_sepConj_right]
  wp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hnew_eq := grow_amortized_new_eq h_5
  have hnew_toNat : (newCap32 cap).toNat = max (2 * cap.toNat) 4 := newCap32_toNat h_5
  have hcap_le_new : cap.toNat ≤ (newCap32 cap).toNat := by omega
  have hnew_pos : 0 < (newCap32 cap).toNat := by omega
  have hnew_bound : (newCap32 cap).toNat * 32 + 8 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero h_4)
    subst hbs
    simp only [ite_true, emp_sepConj, pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero]
    wp_steps_lscl (lsmpl.base 259)
    have hfg0 := lscall_blk (callerProg := (blkPC_260).rebase (blkPl_260).base H)
      (finish_grow_7_zero_cells_of_fg7 hfg) ‹_›
    wp_apply
    by_cases htag : w = 1#64
    · subst htag
      wp_simp_pre [ite_true, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw1, htrace⟩
      subst hw1
      wp_steps
      apply SepWP.instantiate_post_exists 8#64
      apply SepWP.instantiate_post_exists 0#64
      simp only [(by decide : (8#64 : BitVec 64) = 0xffffffffffffffff#64 ↔ False), ite_false]
      wp_done
    · wp_simp_pre [htag, ite_false, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw0, hp', halign, htrace⟩
      subst hw0
      wp_steps
      apply SepWP.instantiate_post_exists 0xffffffffffffffff#64
      apply SepWP.instantiate_post_exists w_1
      simp only [ite_true, (by decide : newCap32 0#64 = 4#64)]
      wp_done
  · wp_simp_pre [hcap0, ite_false]
    wp_steps_lscl (lsmpl.base 259)
    have hfg1 := lscall_blk (callerProg := (blkPC_260).rebase (blkPl_260).base H)
      (finish_grow_7_ne_cells_of_fg7 hfg) ‹_›
    wp_apply
    by_cases htag : w = 1#64
    · subst htag
      wp_simp_pre [ite_true, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw1, htrace⟩
      subst hw1
      wp_steps
      apply SepWP.instantiate_post_exists 8#64
      apply SepWP.instantiate_post_exists 0#64
      simp only [(by decide : (8#64 : BitVec 64) = 0xffffffffffffffff#64 ↔ False), hcap0, ite_false]
      wp_done
    · wp_simp_pre [htag, ite_false, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw0, hp', halign, htrace⟩
      subst hw0
      wp_steps
      apply SepWP.instantiate_post_exists 0xffffffffffffffff#64
      apply SepWP.instantiate_post_exists w_1
      simp only [ite_true]
      wp_done

/-- Block 260 (`grow_amortized`) meets `withLsCodeLoaded lsmpl (growAmortizedBsSpec A)`. -/
theorem grow_amortized_bs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_260).rebase (blkPl_260).base H)
      (blkPl_260).base
      (withLsCodeLoaded lsmpl (growAmortizedBsSpec A)) :=
  grow_amortized_bs_placed_ok_of_fg (finish_grow_7_placed_ok hshim halloc hrealloc)

theorem grow_amortized_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_260).rebase (blkPl_260).base H)
      (blkPl_260).base
      (withLsCodeLoaded lsmpl (growAmortizedSpec A)) := by
  refine subroutine_ok_outcome_intro fun ⟨v, cap, ptr⟩ R s0 hpc hrun hpre hsp => ?_
  let x : GrowAmortizedCall := ⟨v, cap, ptr, []⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (growAmortizedBsSpec A)).pre x s0 ∗ R := by
    simp only [growAmortizedSpec, growAmortizedBsSpec, GrowAmortizedCall.oldBuf, x,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hcap, hptr⟩, hmem⟩
    exact ⟨⟨hx0, hx1, Nat.zero_le _, hcap, hptr⟩, hmem⟩
  refine (grow_amortized_bs_placed_ok hshim halloc hrealloc).mono_outcome x R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [growAmortizedSpec, growAmortizedBsSpec, GrowAmortizedCall.oldBuf, x,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj] using hq
  · exact Or.inr hfail

private theorem grow_amortized_call_placed_ok_of_bs [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {addr : BitVec 64}
    (hbs : subroutine_ok P addr (withLsCodeLoaded lsmpl (growAmortizedBsSpec A))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (growAmortizedCallSpec A)) := by
  refine subroutine_ok_outcome_intro fun ⟨v, cap, ptr, bs, gsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [growAmortizedCallSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hgsp, hbs_le, hcap, hptr⟩, hmem⟩
  subst hgsp
  let x : GrowAmortizedCall := ⟨v, cap, ptr, bs⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (growAmortizedBsSpec A)).pre x s0 ∗ R := by
    simp only [growAmortizedBsSpec, GrowAmortizedCall.oldBuf, x, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hbs_le, hcap, hptr⟩, hmem⟩
  exact hbs.mono_outcome x R s0 hpc hrun hpre' hsp fun _ hout => hout

theorem grow_one_str_pair_bs_placed_ok_of_ga [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hga_bs : subroutine_ok ((blkPC_260).rebase (blkPl_260).base H)
      (blkPl_260).base
      (withLsCodeLoaded lsmpl (growAmortizedBsSpec A))) :
    subroutine_ok ((blkPC_258).rebase (blkPl_258).base H)
      (blkPl_258).base
      (withLsCodeLoaded lsmpl (growOneStrPairBsSpec A)) := by
  unfold withLsCodeLoaded growOneStrPairBsSpec GrowAmortizedCall.oldBuf
  simp only [stackAt_growOneStrPair, sepExists_sepConj_right]
  have hpanic : ((blkPC_258).rebase (blkPl_258).base H).externAt? (lsρ spqrHandleErrorSym) =
      some Rust.panicked :=
    (spqr_externAt?_of_mem).trans h_panic
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  apply SepWPp.of_sepWP (mid := (blkPl_258).base + 16#64)
  wp_steps_lscl (lsmpl.base 260)
  have hga := lscall_blk_cl (callerProg := (blkPC_258).rebase (blkPl_258).base H)
    (grow_amortized_call_placed_ok_of_bs hga_bs) ‹_›
  wp_call hga (v, cap, ptr, bs, s0.sp - 16#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hres : w = 0xffffffffffffffff#64
  · conv => arg 4; simp only [hres, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0, hp', halign, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    apply SepWP.instantiate_post_exists w_1
    wp_done
  · conv => arg 4; simp only [hres, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hw8, hx0, htrace⟩ => ?_
    apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm

/-- Block 258 (`RawVec<(&str, &str)>::grow_one`) meets `withLsCodeLoaded lsmpl (growOneStrPairBsSpec A)`. -/
theorem grow_one_str_pair_bs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_258).rebase (blkPl_258).base H)
      (blkPl_258).base
      (withLsCodeLoaded lsmpl (growOneStrPairBsSpec A)) :=
  grow_one_str_pair_bs_placed_ok_of_ga h_panic (grow_amortized_bs_placed_ok hshim halloc hrealloc)

theorem grow_one_str_pair_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_258).rebase (blkPl_258).base H)
      (blkPl_258).base
      (withLsCodeLoaded lsmpl (growOneStrPairSpec A)) := by
  refine subroutine_ok_outcome_intro fun ⟨v, cap, ptr⟩ R s0 hpc hrun hpre hsp => ?_
  let x : GrowAmortizedCall := ⟨v, cap, ptr, []⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (growOneStrPairBsSpec A)).pre x s0 ∗ R := by
    simp only [growOneStrPairSpec, growOneStrPairBsSpec, GrowAmortizedCall.oldBuf, x,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hcap, hptr⟩, hmem⟩
    exact ⟨⟨hx0, Nat.zero_le _, hcap, hptr⟩, hmem⟩
  refine (grow_one_str_pair_bs_placed_ok h_panic hshim halloc hrealloc).mono_outcome
    x R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [growOneStrPairSpec, growOneStrPairBsSpec, GrowAmortizedCall.oldBuf, x,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj] using hq
  · exact Or.inr hfail

end CryptoVerification.SpqrV1.Alloc
