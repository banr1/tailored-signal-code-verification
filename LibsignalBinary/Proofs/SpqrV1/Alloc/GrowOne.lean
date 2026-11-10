/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrow
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `RawVec<{ChainEpoch, Pt, Poly, GF16, &[Pt]}>::grow_one`

Verifies the five 26-instruction `<alloc::raw_vec::RawVec<T>>::grow_one` monomorphizations
calling `finish_grow [local#8]` (`ChainEpoch`, `Pt`, `Poly`, `GF16`, and `&[Pt]`) on
`tripleRatchetProgAtExt` and under `[LibsignalPlacement]` (blocks 356..360).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.CodeLayout

abbrev GrowGhost := BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace GrowOneNorm

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

end GrowOneNorm

open GrowOneNorm

/-! ## Stack Budget and Arithmetic Helpers -/

/-- Stack budget of 64-byte-frame `RawVec<T>::grow_one` (`finishGrowStack + 64`). -/
abbrev growOneStack : Nat := finishGrowStack + 64

private theorem stackAt_growOne (sp : BitVec 64) :
    stackAt sp growOneStack =
      stackAt (sp - 64#64) finishGrowStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_cells sp 4144 8 (by decide)
  change stackAt sp growOneStack =
    stackAt (sp - 64#64) finishGrowStack ∗ cells (sp - 64#64) 8 at h1
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

private theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem grow_new_cap_eq {cap : BitVec 64}
    (h : max (2 * cap.toNat) 4 < 2 ^ 63) :
    (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hc : (4#64).ult (cap <<< 1) = true
  · simp only [hc, ite_true, hsh]
    have hlt : 4 < 2 * cap.toNat := by
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
      exact hc
    omega
  · simp only [hc, Bool.false_eq_true, ite_false]
    have hle : ¬ 4 < 2 * cap.toNat := by
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
      exact hc
    change 4 = max (2 * cap.toNat) 4
    omega

private theorem pull_fg0_err (O1 O2 O3 P A S R : SepProp) :
    (O1 ∗ O2 ∗ O3 ∗ P ∗ A ∗ S) ∗ R = P ∗ ((A ∗ S ∗ O1 ∗ O2 ∗ O3) ∗ R) := by ac_rfl

private theorem pull_fg0_ok (O1 O2 O3 P L M A S R : SepProp) :
    (O1 ∗ O2 ∗ O3 ∗ (P ∗ L ∗ M) ∗ A ∗ S) ∗ R =
      P ∗ ((L ∗ M ∗ A ∗ S ∗ O1 ∗ O2 ∗ O3) ∗ R) := by ac_rfl

private theorem pull_fg1_post (O1 O2 O3 P L B M A S R : SepProp) :
    (O1 ∗ O2 ∗ O3 ∗ (P ∗ L ∗ B ∗ M) ∗ A ∗ S) ∗ R =
      P ∗ ((L ∗ B ∗ M ∗ A ∗ S ∗ O1 ∗ O2 ∗ O3) ∗ R) := by ac_rfl

/-! ## Cell-Unfolded `finish_grow [local#8]` Wrappers -/

private abbrev FG8CellsGhost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

private def finishGrow8ZeroCellsSpec (A : RustAlloc) : Spec FG8CellsGhost where
  pre := fun (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧ LayoutOk (new.toNat * stride.toNat) align.toNat⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ stackAt fsp finishGrowStack
  post := fun (out, _cap, _ptr, new, align, stride, _bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (new.toNat * stride.toNat) align.toNat ∗
          memRegion p' (new.toNat * stride.toNat)) ∗
      A.pool ∗ stackAt fsp finishGrowStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem finish_grow_8_zero_cells_of_fg8 {A : RustAlloc} {P : Program} {addr : BitVec 64}
    (hfg : subroutine_ok P addr (finishGrowSpec A)) :
    subroutine_ok P addr (finishGrow8ZeroCellsSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow8ZeroCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hstr, hlay⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, align, stride, []⟩
  have hpre' : s0.mem ⊨ (finishGrowSpec A).pre hcall s0 ∗ R := by
    simp only [finishGrowSpec, hcall, FinishGrowCall.oldBuf, ite_true,
      memRegion_24_cells, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, hstr, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrowSpec, finishGrow8ZeroCellsSpec, hcall, FinishGrowCall.oldBuf,
      ite_true, pointsToBytes_nil, List.length_nil,
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

private theorem finish_grow_8_zero_cells_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (finishGrow8ZeroCellsSpec A) :=
  finish_grow_8_zero_cells_of_fg8 (finish_grow_8_ok_ext hA)

private def finishGrow8NeCellsSpec (A : RustAlloc) : Spec FG8CellsGhost where
  pre := fun (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length ≤ cap.toNat * stride.toNat ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧ LayoutOk (new.toNat * stride.toNat) align.toNat⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr (cap.toNat * stride.toNat) align.toNat ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * stride.toNat - bs.length) ∗
    A.pool ∗ stackAt fsp finishGrowStack
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
      A.pool ∗ stackAt fsp finishGrowStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem finish_grow_8_ne_cells_of_fg8 {A : RustAlloc} {P : Program} {addr : BitVec 64}
    (hfg : subroutine_ok P addr (finishGrowSpec A)) :
    subroutine_ok P addr (finishGrow8NeCellsSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow8NeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hstr, hlay⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, align, stride, bs⟩
  have hpre' : s0.mem ⊨ (finishGrowSpec A).pre hcall s0 ∗ R := by
    simp only [finishGrowSpec, hcall, FinishGrowCall.oldBuf, hcap, ite_false,
      memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs, hle, hpos, hstr, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrowSpec, finishGrow8NeCellsSpec, hcall, FinishGrowCall.oldBuf,
      hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
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

private theorem finish_grow_8_ne_cells_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow8Name)
      (finishGrow8NeCellsSpec A) :=
  finish_grow_8_ne_cells_of_fg8 (finish_grow_8_ok_ext hA)

/-! ## Generic `(stride, align)` `grow_one` Specifications -/

/-- Prefix-preserving contract for `RawVec<T>::grow_one` (`stride > 1`, `bs.length ≤ cap.toNat * stride`). -/
def growOneStrideBsSpec (A : RustAlloc) (stride align : Nat) : Spec GrowGhost where
  pre := fun (v, cap, ptr, bs) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length ≤ cap.toNat * stride ∧ ptr ≠ 0#64 ∧
      max (2 * cap.toNat) 4 * stride + align ≤ 2 ^ 63⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * stride) align ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * stride - bs.length)) ∗
    A.pool ∗ stackAt s.sp growOneStack
  post := fun (v, cap, _, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % align = 0⌝ ∗
      (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * stride) align ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * cap.toNat) 4 * stride - bs.length)) ∗
    A.pool ∗ stackAt s0.sp growOneStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Full-buffer contract for `RawVec<T>::grow_one` (`bs.length = cap.toNat * stride`). -/
def growOneStrideFullSpec (A : RustAlloc) (stride align : Nat) : Spec GrowGhost where
  pre := fun (v, cap, ptr, bs) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length = cap.toNat * stride ∧ ptr ≠ 0#64 ∧
      max (2 * cap.toNat) 4 * stride + align ≤ 2 ^ 63⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp else A.live ptr bs.length align ∗ (ptr ↦ₛ bs)) ∗
    A.pool ∗ stackAt s.sp growOneStack
  post := fun (v, cap, _, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % align = 0⌝ ∗
      (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * stride) align ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * stride)) ∗
    A.pool ∗ stackAt s0.sp growOneStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Uninitialized (`memRegion`) contract for `RawVec<T>::grow_one` (`bs = []`). -/
def growOneStrideEmptySpec (A : RustAlloc) (stride align : Nat) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (v, cap, ptr) s =>
    ⌜s.readReg64 .x0 = v ∧ ptr ≠ 0#64 ∧
      max (2 * cap.toNat) 4 * stride + align ≤ 2 ^ 63⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * stride) align ∗ memRegion ptr (cap.toNat * stride)) ∗
    A.pool ∗ stackAt s.sp growOneStack
  post := fun (v, cap, _ptr) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % align = 0⌝ ∗
      (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * stride) align ∗
      memRegion p' (max (2 * cap.toNat) 4 * stride)) ∗
    A.pool ∗ stackAt s0.sp growOneStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem grow_one_stride_full_of_bs {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {name : String} {stride align : Nat}
    (hbs : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name)
      (growOneStrideBsSpec A stride align)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name)
      (growOneStrideFullSpec A stride align) := by
  refine subroutine_ok_outcome_intro fun ⟨v, cap, ptr, bs⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [growOneStrideFullSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hlen, hptr, hbound⟩, hmem⟩
  have hpre' : s0.mem ⊨ (growOneStrideBsSpec A stride align).pre (v, cap, ptr, bs) s0 ∗ R := by
    simp only [growOneStrideBsSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, Nat.le_of_eq hlen, hptr, hbound⟩, ?_⟩
    by_cases hcap0 : cap = 0#64
    · simp only [hcap0, ite_true] at hmem ⊢
      exact hmem
    · simp only [hcap0, ite_false, ← hlen, Nat.sub_self, memRegion_zero, sepConj_emp,
        sepConj_assoc] at hmem ⊢
      exact hmem
  refine hbs.mono_outcome (v, cap, ptr, bs) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hsub_mul : (max (2 * cap.toNat) 4 - cap.toNat) * stride =
        max (2 * cap.toNat) 4 * stride - bs.length := by
      rw [Nat.sub_mul, hlen]
    simp only [growOneStrideBsSpec, growOneStrideFullSpec, hsub_mul] at hq ⊢
    exact hq
  · exact Or.inr hfail

theorem grow_one_stride_empty_of_bs {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {name : String} {stride align : Nat}
    (hbs : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name)
      (growOneStrideBsSpec A stride align)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name)
      (growOneStrideEmptySpec A stride align) := by
  refine subroutine_ok_outcome_intro fun ⟨v, cap, ptr⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [growOneStrideEmptySpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hptr, hbound⟩, hmem⟩
  have hpre' : s0.mem ⊨ (growOneStrideBsSpec A stride align).pre (v, cap, ptr, []) s0 ∗ R := by
    simp only [growOneStrideBsSpec, List.length_nil, pointsToBytes_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, Nat.zero_le _, hptr, hbound⟩, hmem⟩
  refine hbs.mono_outcome (v, cap, ptr, []) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [growOneStrideBsSpec, growOneStrideEmptySpec, List.length_nil,
      pointsToBytes_nil, BitVec.add_zero, Nat.sub_zero,
      emp_sepConj] at hq ⊢
    exact hq
  · exact Or.inr hfail

/-! ## `RawVec<ChainEpoch>::grow_one` (`stride = 112, align = 8`) -/

abbrev growOneChainEpochName : String :=
  "<alloc::raw_vec::RawVec<spqr::chain::ChainEpoch>>::grow_one"

abbrev growOneChainEpochBsSpec (A : RustAlloc) := growOneStrideBsSpec A 112 8
abbrev growOneChainEpochFullSpec (A : RustAlloc) := growOneStrideFullSpec A 112 8
abbrev growOneChainEpochSpec (A : RustAlloc) := growOneStrideEmptySpec A 112 8

/-- `RawVec<ChainEpoch>::grow_one` meets `growOneChainEpochBsSpec A`. -/
theorem grow_one_chain_epoch_bs_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneChainEpochName)
      (growOneChainEpochBsSpec A) := by
  simp only [growOneChainEpochBsSpec, growOneStrideBsSpec, stackAt_growOne, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff growOneChainEpochName = 0x5a6e0 :=
    libsignalSessionCode_fnOff_0x5a6e0
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := growOneChainEpochName) (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x5a6e0))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := finish_grow_8_zero_cells_ok_ext hA
  have hfg1 := finish_grow_8_ne_cells_ok_ext hA
  rw [Program.fnAddr_rel (name := growOneChainEpochName)
    hfn libsignalSessionCode_fnOff_0x5a8e8 (k := 520) (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn 0x5a6e0 104
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr growOneChainEpochName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hnew_lay : LayoutOk (new.toNat * (112#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 112; omega, hpow, ?_⟩
    change new.toNat * 112 + 8 ≤ 2 ^ 63; omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * 112 = 0 := rfl
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 112 = new.toNat * 112 := by rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, hmul_eq]
    apply SepWPp.of_sepWP (mid := entry + 60#64)
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5a6e0))
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
    have hsub_eq : max (2 * cap.toNat) 4 * 112 - bs.length = new.toNat * 112 - bs.length := by
      rw [hnew_toNat]
    have hmul_eq : max (2 * cap.toNat) 4 * 112 = new.toNat * 112 := by
      rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := entry + 60#64)
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5a6e0))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, BitVec.toNat_ofNat, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

theorem grow_one_chain_epoch_full_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneChainEpochName)
      (growOneChainEpochFullSpec A) :=
  grow_one_stride_full_of_bs (grow_one_chain_epoch_bs_ok_ext hA)

theorem grow_one_chain_epoch_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneChainEpochName)
      (growOneChainEpochSpec A) :=
  grow_one_stride_empty_of_bs (grow_one_chain_epoch_bs_ok_ext hA)

/-! ## `RawVec<Pt>::grow_one` (`stride = 4, align = 2`) -/

abbrev growOnePtName : String :=
  "<alloc::raw_vec::RawVec<spqr::encoding::polynomial::Pt>>::grow_one"

abbrev growOnePtBsSpec (A : RustAlloc) := growOneStrideBsSpec A 4 2
abbrev growOnePtFullSpec (A : RustAlloc) := growOneStrideFullSpec A 4 2
abbrev growOnePtSpec (A : RustAlloc) := growOneStrideEmptySpec A 4 2

/-- `RawVec<Pt>::grow_one` meets `growOnePtBsSpec A`. -/
theorem grow_one_pt_bs_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOnePtName)
      (growOnePtBsSpec A) := by
  simp only [growOnePtBsSpec, growOneStrideBsSpec, stackAt_growOne, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff growOnePtName = 0x5a748 :=
    libsignalSessionCode_fnOff_0x5a748
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := growOnePtName) (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x5a748))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := finish_grow_8_zero_cells_ok_ext hA
  have hfg1 := finish_grow_8_ne_cells_ok_ext hA
  rw [Program.fnAddr_rel (name := growOnePtName)
    hfn libsignalSessionCode_fnOff_0x5a8e8 (k := 416) (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn 0x5a748 104
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr growOnePtName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 2 = 2 ^ k := ⟨1, rfl⟩
  have hnew_lay : LayoutOk (new.toNat * (4#64 : BitVec 64).toNat) (2#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 4; omega, hpow, ?_⟩
    change new.toNat * 4 + 2 ≤ 2 ^ 63; omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * 4 = 0 := rfl
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 4 = new.toNat * 4 := by rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, hmul_eq]
    apply SepWPp.of_sepWP (mid := entry + 60#64)
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5a748))
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
    have hsub_eq : max (2 * cap.toNat) 4 * 4 - bs.length = new.toNat * 4 - bs.length := by
      rw [hnew_toNat]
    have hmul_eq : max (2 * cap.toNat) 4 * 4 = new.toNat * 4 := by
      rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := entry + 60#64)
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5a748))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, BitVec.toNat_ofNat, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

theorem grow_one_pt_full_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOnePtName)
      (growOnePtFullSpec A) :=
  grow_one_stride_full_of_bs (grow_one_pt_bs_ok_ext hA)

theorem grow_one_pt_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOnePtName)
      (growOnePtSpec A) :=
  grow_one_stride_empty_of_bs (grow_one_pt_bs_ok_ext hA)

/-! ## `RawVec<Poly>::grow_one` (`stride = 24, align = 8`) -/

abbrev growOnePolyName : String :=
  "<alloc::raw_vec::RawVec<spqr::encoding::polynomial::Poly>>::grow_one"

abbrev growOnePolyBsSpec (A : RustAlloc) := growOneStrideBsSpec A 24 8
abbrev growOnePolyFullSpec (A : RustAlloc) := growOneStrideFullSpec A 24 8
abbrev growOnePolySpec (A : RustAlloc) := growOneStrideEmptySpec A 24 8

/-- `RawVec<Poly>::grow_one` meets `growOnePolyBsSpec A`. -/
theorem grow_one_poly_bs_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOnePolyName)
      (growOnePolyBsSpec A) := by
  simp only [growOnePolyBsSpec, growOneStrideBsSpec, stackAt_growOne, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff growOnePolyName = 0x5a7b0 :=
    libsignalSessionCode_fnOff_0x5a7b0
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := growOnePolyName) (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x5a7b0))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := finish_grow_8_zero_cells_ok_ext hA
  have hfg1 := finish_grow_8_ne_cells_ok_ext hA
  rw [Program.fnAddr_rel (name := growOnePolyName)
    hfn libsignalSessionCode_fnOff_0x5a8e8 (k := 312) (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn 0x5a7b0 104
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr growOnePolyName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hnew_lay : LayoutOk (new.toNat * (24#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 24; omega, hpow, ?_⟩
    change new.toNat * 24 + 8 ≤ 2 ^ 63; omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * 24 = 0 := rfl
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 24 = new.toNat * 24 := by rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, hmul_eq]
    apply SepWPp.of_sepWP (mid := entry + 60#64)
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5a7b0))
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
    have hsub_eq : max (2 * cap.toNat) 4 * 24 - bs.length = new.toNat * 24 - bs.length := by
      rw [hnew_toNat]
    have hmul_eq : max (2 * cap.toNat) 4 * 24 = new.toNat * 24 := by
      rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := entry + 60#64)
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5a7b0))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, BitVec.toNat_ofNat, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

theorem grow_one_poly_full_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOnePolyName)
      (growOnePolyFullSpec A) :=
  grow_one_stride_full_of_bs (grow_one_poly_bs_ok_ext hA)

theorem grow_one_poly_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOnePolyName)
      (growOnePolySpec A) :=
  grow_one_stride_empty_of_bs (grow_one_poly_bs_ok_ext hA)

/-! ## `RawVec<GF16>::grow_one` (`stride = 2, align = 2`) -/

abbrev growOneGF16Name : String :=
  "<alloc::raw_vec::RawVec<spqr::encoding::gf::GF16>>::grow_one"

abbrev growOneGF16BsSpec (A : RustAlloc) := growOneStrideBsSpec A 2 2
abbrev growOneGF16FullSpec (A : RustAlloc) := growOneStrideFullSpec A 2 2
abbrev growOneGF16Spec (A : RustAlloc) := growOneStrideEmptySpec A 2 2

/-- `RawVec<GF16>::grow_one` meets `growOneGF16BsSpec A`. -/
theorem grow_one_gf16_bs_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneGF16Name)
      (growOneGF16BsSpec A) := by
  simp only [growOneGF16BsSpec, growOneStrideBsSpec, stackAt_growOne, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff growOneGF16Name = 0x5a818 :=
    libsignalSessionCode_fnOff_0x5a818
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := growOneGF16Name) (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x5a818))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := finish_grow_8_zero_cells_ok_ext hA
  have hfg1 := finish_grow_8_ne_cells_ok_ext hA
  rw [Program.fnAddr_rel (name := growOneGF16Name)
    hfn libsignalSessionCode_fnOff_0x5a8e8 (k := 208) (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn 0x5a818 104
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr growOneGF16Name = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 2 = 2 ^ k := ⟨1, rfl⟩
  have hnew_lay : LayoutOk (new.toNat * (2#64 : BitVec 64).toNat) (2#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 2; omega, hpow, ?_⟩
    change new.toNat * 2 + 2 ≤ 2 ^ 63; omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * 2 = 0 := rfl
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 2 = new.toNat * 2 := by rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, hmul_eq]
    apply SepWPp.of_sepWP (mid := entry + 60#64)
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5a818))
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
    have hsub_eq : max (2 * cap.toNat) 4 * 2 - bs.length = new.toNat * 2 - bs.length := by
      rw [hnew_toNat]
    have hmul_eq : max (2 * cap.toNat) 4 * 2 = new.toNat * 2 := by
      rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := entry + 60#64)
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5a818))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, BitVec.toNat_ofNat, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

theorem grow_one_gf16_full_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneGF16Name)
      (growOneGF16FullSpec A) :=
  grow_one_stride_full_of_bs (grow_one_gf16_bs_ok_ext hA)

theorem grow_one_gf16_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneGF16Name)
      (growOneGF16Spec A) :=
  grow_one_stride_empty_of_bs (grow_one_gf16_bs_ok_ext hA)

/-! ## `RawVec<&[Pt]>::grow_one` (`stride = 16, align = 8`) -/

abbrev growOnePtSliceName : String :=
  "<alloc::raw_vec::RawVec<&[spqr::encoding::polynomial::Pt]>>::grow_one"

abbrev growOnePtSliceBsSpec (A : RustAlloc) := growOneStrideBsSpec A 16 8
abbrev growOnePtSliceFullSpec (A : RustAlloc) := growOneStrideFullSpec A 16 8
abbrev growOnePtSliceSpec (A : RustAlloc) := growOneStrideEmptySpec A 16 8

/-- `RawVec<&[Pt]>::grow_one` meets `growOnePtSliceBsSpec A`. -/
theorem grow_one_pt_slice_bs_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOnePtSliceName)
      (growOnePtSliceBsSpec A) := by
  simp only [growOnePtSliceBsSpec, growOneStrideBsSpec, stackAt_growOne, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff growOnePtSliceName = 0x5a880 :=
    libsignalSessionCode_fnOff_0x5a880
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := growOnePtSliceName) (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x5a880))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := finish_grow_8_zero_cells_ok_ext hA
  have hfg1 := finish_grow_8_ne_cells_ok_ext hA
  rw [Program.fnAddr_rel (name := growOnePtSliceName)
    hfn libsignalSessionCode_fnOff_0x5a8e8 (k := 104) (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBin b
    (Rust.withPanics ext) hfn 0x5a880 104
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr growOnePtSliceName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hnew_lay : LayoutOk (new.toNat * (16#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 16; omega, hpow, ?_⟩
    change new.toNat * 16 + 8 ≤ 2 ^ 63; omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * 16 = 0 := rfl
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 16 = new.toNat * 16 := by rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, hmul_eq]
    apply SepWPp.of_sepWP (mid := entry + 60#64)
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5a880))
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
    have hsub_eq : max (2 * cap.toNat) 4 * 16 - bs.length = new.toNat * 16 - bs.length := by
      rw [hnew_toNat]
    have hmul_eq : max (2 * cap.toNat) 4 * 16 = new.toNat * 16 := by
      rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := entry + 60#64)
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5a880))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, BitVec.toNat_ofNat, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

theorem grow_one_pt_slice_full_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOnePtSliceName)
      (growOnePtSliceFullSpec A) :=
  grow_one_stride_full_of_bs (grow_one_pt_slice_bs_ok_ext hA)

theorem grow_one_pt_slice_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOnePtSliceName)
      (growOnePtSliceSpec A) :=
  grow_one_stride_empty_of_bs (grow_one_pt_slice_bs_ok_ext hA)

/-! ## Relocatable Contracts (Blocks 356..360) -/

theorem grow_one_stride_full_placed_of_bs [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {addr : BitVec 64} {stride align : Nat}
    (hbs : subroutine_ok P addr (withLsCodeLoaded lsmpl (growOneStrideBsSpec A stride align))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (growOneStrideFullSpec A stride align)) := by
  refine subroutine_ok_outcome_intro fun ⟨v, cap, ptr, bs⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [growOneStrideFullSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hlen, hptr, hbound⟩, hmem⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (growOneStrideBsSpec A stride align)).pre (v, cap, ptr, bs) s0 ∗ R := by
    simp only [growOneStrideBsSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, Nat.le_of_eq hlen, hptr, hbound⟩, ?_⟩
    by_cases hcap0 : cap = 0#64
    · simp only [hcap0, ite_true] at hmem ⊢
      exact hmem
    · simp only [hcap0, ite_false, ← hlen, Nat.sub_self, memRegion_zero, sepConj_emp,
        sepConj_assoc] at hmem ⊢
      exact hmem
  refine hbs.mono_outcome (v, cap, ptr, bs) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hsub_mul : (max (2 * cap.toNat) 4 - cap.toNat) * stride =
        max (2 * cap.toNat) 4 * stride - bs.length := by
      rw [Nat.sub_mul, hlen]
    simp only [growOneStrideBsSpec, growOneStrideFullSpec, hsub_mul] at hq ⊢
    exact hq
  · exact Or.inr hfail

theorem grow_one_stride_empty_placed_of_bs [LibsignalPlacement] {A : RustAlloc}
    {P : Program} {addr : BitVec 64} {stride align : Nat}
    (hbs : subroutine_ok P addr (withLsCodeLoaded lsmpl (growOneStrideBsSpec A stride align))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (growOneStrideEmptySpec A stride align)) := by
  refine subroutine_ok_outcome_intro fun ⟨v, cap, ptr⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [growOneStrideEmptySpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hptr, hbound⟩, hmem⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (growOneStrideBsSpec A stride align)).pre (v, cap, ptr, []) s0 ∗ R := by
    simp only [growOneStrideBsSpec, List.length_nil, pointsToBytes_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, Nat.zero_le _, hptr, hbound⟩, hmem⟩
  refine hbs.mono_outcome (v, cap, ptr, []) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [growOneStrideBsSpec, growOneStrideEmptySpec, List.length_nil,
      pointsToBytes_nil, BitVec.add_zero, Nat.sub_zero,
      emp_sepConj] at hq ⊢
    exact hq
  · exact Or.inr hfail

/-- Block 356 (`RawVec<ChainEpoch>::grow_one`) meets `withLsCodeLoaded lsmpl (growOneChainEpochBsSpec A)`. -/
theorem grow_one_chain_epoch_bs_placed_ok_of_fg [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrowSpec A)) :
    subroutine_ok ((blkPC_356).rebase (blkPl_356).base H)
      (blkPl_356).base
      (withLsCodeLoaded lsmpl (growOneChainEpochBsSpec A)) := by
  unfold withLsCodeLoaded
  simp only [growOneChainEpochBsSpec, growOneStrideBsSpec, stackAt_growOne, sepExists_sepConj_right]
  have hpanic : ((blkPC_356).rebase (blkPl_356).base H).externAt? (lsρ spqrHandleErrorSym) =
      some Rust.panicked :=
    (spqr_externAt?_of_mem).trans h_panic
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hnew_lay : LayoutOk (new.toNat * (112#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 112; omega, hpow, ?_⟩
    change new.toNat * 112 + 8 ≤ 2 ^ 63; omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * 112 = 0 := rfl
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 112 = new.toNat * 112 := by rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_356).base + 60#64)
    wp_steps_lscl (lsmpl.base 361)
    have hfg0 := lscall_blk (callerProg := (blkPC_356).rebase (blkPl_356).base H)
      (finish_grow_8_zero_cells_of_fg8 hfg) ‹_›
    wp_apply
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
    have hsub_eq : max (2 * cap.toNat) 4 * 112 - bs.length = new.toNat * 112 - bs.length := by
      rw [hnew_toNat]
    have hmul_eq : max (2 * cap.toNat) 4 * 112 = new.toNat * 112 := by
      rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_356).base + 60#64)
    wp_steps_lscl (lsmpl.base 361)
    have hfg1 := lscall_blk (callerProg := (blkPC_356).rebase (blkPl_356).base H)
      (finish_grow_8_ne_cells_of_fg8 hfg) ‹_›
    wp_apply
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
    · simp only [htag, ite_false, BitVec.toNat_ofNat, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

theorem grow_one_chain_epoch_bs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_356).rebase (blkPl_356).base H)
      (blkPl_356).base
      (withLsCodeLoaded lsmpl (growOneChainEpochBsSpec A)) :=
  grow_one_chain_epoch_bs_placed_ok_of_fg h_panic (finish_grow_8_placed_ok hshim halloc hrealloc)

theorem grow_one_chain_epoch_full_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_356).rebase (blkPl_356).base H)
      (blkPl_356).base
      (withLsCodeLoaded lsmpl (growOneChainEpochFullSpec A)) :=
  grow_one_stride_full_placed_of_bs (grow_one_chain_epoch_bs_placed_ok h_panic hshim halloc hrealloc)

theorem grow_one_chain_epoch_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_356).rebase (blkPl_356).base H)
      (blkPl_356).base
      (withLsCodeLoaded lsmpl (growOneChainEpochSpec A)) :=
  grow_one_stride_empty_placed_of_bs (grow_one_chain_epoch_bs_placed_ok h_panic hshim halloc hrealloc)

/-- Block 357 (`RawVec<Pt>::grow_one`) meets `withLsCodeLoaded lsmpl (growOnePtBsSpec A)`. -/
theorem grow_one_pt_bs_placed_ok_of_fg [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrowSpec A)) :
    subroutine_ok ((blkPC_357).rebase (blkPl_357).base H)
      (blkPl_357).base
      (withLsCodeLoaded lsmpl (growOnePtBsSpec A)) := by
  unfold withLsCodeLoaded
  simp only [growOnePtBsSpec, growOneStrideBsSpec, stackAt_growOne, sepExists_sepConj_right]
  have hpanic : ((blkPC_357).rebase (blkPl_357).base H).externAt? (lsρ spqrHandleErrorSym) =
      some Rust.panicked :=
    (spqr_externAt?_of_mem).trans h_panic
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 2 = 2 ^ k := ⟨1, rfl⟩
  have hnew_lay : LayoutOk (new.toNat * (4#64 : BitVec 64).toNat) (2#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 4; omega, hpow, ?_⟩
    change new.toNat * 4 + 2 ≤ 2 ^ 63; omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * 4 = 0 := rfl
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 4 = new.toNat * 4 := by rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_357).base + 60#64)
    wp_steps_lscl (lsmpl.base 361)
    have hfg0 := lscall_blk (callerProg := (blkPC_357).rebase (blkPl_357).base H)
      (finish_grow_8_zero_cells_of_fg8 hfg) ‹_›
    wp_apply
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
    have hsub_eq : max (2 * cap.toNat) 4 * 4 - bs.length = new.toNat * 4 - bs.length := by
      rw [hnew_toNat]
    have hmul_eq : max (2 * cap.toNat) 4 * 4 = new.toNat * 4 := by
      rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_357).base + 60#64)
    wp_steps_lscl (lsmpl.base 361)
    have hfg1 := lscall_blk (callerProg := (blkPC_357).rebase (blkPl_357).base H)
      (finish_grow_8_ne_cells_of_fg8 hfg) ‹_›
    wp_apply
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
    · simp only [htag, ite_false, BitVec.toNat_ofNat, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

theorem grow_one_pt_bs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_357).rebase (blkPl_357).base H)
      (blkPl_357).base
      (withLsCodeLoaded lsmpl (growOnePtBsSpec A)) :=
  grow_one_pt_bs_placed_ok_of_fg h_panic (finish_grow_8_placed_ok hshim halloc hrealloc)

theorem grow_one_pt_full_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_357).rebase (blkPl_357).base H)
      (blkPl_357).base
      (withLsCodeLoaded lsmpl (growOnePtFullSpec A)) :=
  grow_one_stride_full_placed_of_bs (grow_one_pt_bs_placed_ok h_panic hshim halloc hrealloc)

theorem grow_one_pt_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_357).rebase (blkPl_357).base H)
      (blkPl_357).base
      (withLsCodeLoaded lsmpl (growOnePtSpec A)) :=
  grow_one_stride_empty_placed_of_bs (grow_one_pt_bs_placed_ok h_panic hshim halloc hrealloc)

/-- Block 358 (`RawVec<Poly>::grow_one`) meets `withLsCodeLoaded lsmpl (growOnePolyBsSpec A)`. -/
theorem grow_one_poly_bs_placed_ok_of_fg [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrowSpec A)) :
    subroutine_ok ((blkPC_358).rebase (blkPl_358).base H)
      (blkPl_358).base
      (withLsCodeLoaded lsmpl (growOnePolyBsSpec A)) := by
  unfold withLsCodeLoaded
  simp only [growOnePolyBsSpec, growOneStrideBsSpec, stackAt_growOne, sepExists_sepConj_right]
  have hpanic : ((blkPC_358).rebase (blkPl_358).base H).externAt? (lsρ spqrHandleErrorSym) =
      some Rust.panicked :=
    (spqr_externAt?_of_mem).trans h_panic
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hnew_lay : LayoutOk (new.toNat * (24#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 24; omega, hpow, ?_⟩
    change new.toNat * 24 + 8 ≤ 2 ^ 63; omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * 24 = 0 := rfl
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 24 = new.toNat * 24 := by rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_358).base + 60#64)
    wp_steps_lscl (lsmpl.base 361)
    have hfg0 := lscall_blk (callerProg := (blkPC_358).rebase (blkPl_358).base H)
      (finish_grow_8_zero_cells_of_fg8 hfg) ‹_›
    wp_apply
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
    have hsub_eq : max (2 * cap.toNat) 4 * 24 - bs.length = new.toNat * 24 - bs.length := by
      rw [hnew_toNat]
    have hmul_eq : max (2 * cap.toNat) 4 * 24 = new.toNat * 24 := by
      rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_358).base + 60#64)
    wp_steps_lscl (lsmpl.base 361)
    have hfg1 := lscall_blk (callerProg := (blkPC_358).rebase (blkPl_358).base H)
      (finish_grow_8_ne_cells_of_fg8 hfg) ‹_›
    wp_apply
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
    · simp only [htag, ite_false, BitVec.toNat_ofNat, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

theorem grow_one_poly_bs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_358).rebase (blkPl_358).base H)
      (blkPl_358).base
      (withLsCodeLoaded lsmpl (growOnePolyBsSpec A)) :=
  grow_one_poly_bs_placed_ok_of_fg h_panic (finish_grow_8_placed_ok hshim halloc hrealloc)

theorem grow_one_poly_full_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_358).rebase (blkPl_358).base H)
      (blkPl_358).base
      (withLsCodeLoaded lsmpl (growOnePolyFullSpec A)) :=
  grow_one_stride_full_placed_of_bs (grow_one_poly_bs_placed_ok h_panic hshim halloc hrealloc)

theorem grow_one_poly_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_358).rebase (blkPl_358).base H)
      (blkPl_358).base
      (withLsCodeLoaded lsmpl (growOnePolySpec A)) :=
  grow_one_stride_empty_placed_of_bs (grow_one_poly_bs_placed_ok h_panic hshim halloc hrealloc)

/-- Block 359 (`RawVec<GF16>::grow_one`) meets `withLsCodeLoaded lsmpl (growOneGF16BsSpec A)`. -/
theorem grow_one_gf16_bs_placed_ok_of_fg [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrowSpec A)) :
    subroutine_ok ((blkPC_359).rebase (blkPl_359).base H)
      (blkPl_359).base
      (withLsCodeLoaded lsmpl (growOneGF16BsSpec A)) := by
  unfold withLsCodeLoaded
  simp only [growOneGF16BsSpec, growOneStrideBsSpec, stackAt_growOne, sepExists_sepConj_right]
  have hpanic : ((blkPC_359).rebase (blkPl_359).base H).externAt? (lsρ spqrHandleErrorSym) =
      some Rust.panicked :=
    (spqr_externAt?_of_mem).trans h_panic
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 2 = 2 ^ k := ⟨1, rfl⟩
  have hnew_lay : LayoutOk (new.toNat * (2#64 : BitVec 64).toNat) (2#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 2; omega, hpow, ?_⟩
    change new.toNat * 2 + 2 ≤ 2 ^ 63; omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * 2 = 0 := rfl
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 2 = new.toNat * 2 := by rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_359).base + 60#64)
    wp_steps_lscl (lsmpl.base 361)
    have hfg0 := lscall_blk (callerProg := (blkPC_359).rebase (blkPl_359).base H)
      (finish_grow_8_zero_cells_of_fg8 hfg) ‹_›
    wp_apply
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
    have hsub_eq : max (2 * cap.toNat) 4 * 2 - bs.length = new.toNat * 2 - bs.length := by
      rw [hnew_toNat]
    have hmul_eq : max (2 * cap.toNat) 4 * 2 = new.toNat * 2 := by
      rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_359).base + 60#64)
    wp_steps_lscl (lsmpl.base 361)
    have hfg1 := lscall_blk (callerProg := (blkPC_359).rebase (blkPl_359).base H)
      (finish_grow_8_ne_cells_of_fg8 hfg) ‹_›
    wp_apply
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
    · simp only [htag, ite_false, BitVec.toNat_ofNat, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

theorem grow_one_gf16_bs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_359).rebase (blkPl_359).base H)
      (blkPl_359).base
      (withLsCodeLoaded lsmpl (growOneGF16BsSpec A)) :=
  grow_one_gf16_bs_placed_ok_of_fg h_panic (finish_grow_8_placed_ok hshim halloc hrealloc)

theorem grow_one_gf16_full_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_359).rebase (blkPl_359).base H)
      (blkPl_359).base
      (withLsCodeLoaded lsmpl (growOneGF16FullSpec A)) :=
  grow_one_stride_full_placed_of_bs (grow_one_gf16_bs_placed_ok h_panic hshim halloc hrealloc)

theorem grow_one_gf16_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_359).rebase (blkPl_359).base H)
      (blkPl_359).base
      (withLsCodeLoaded lsmpl (growOneGF16Spec A)) :=
  grow_one_stride_empty_placed_of_bs (grow_one_gf16_bs_placed_ok h_panic hshim halloc hrealloc)

/-- Block 360 (`RawVec<&[Pt]>::grow_one`) meets `withLsCodeLoaded lsmpl (growOnePtSliceBsSpec A)`. -/
theorem grow_one_pt_slice_bs_placed_ok_of_fg [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base (finishGrowSpec A)) :
    subroutine_ok ((blkPC_360).rebase (blkPl_360).base H)
      (blkPl_360).base
      (withLsCodeLoaded lsmpl (growOnePtSliceBsSpec A)) := by
  unfold withLsCodeLoaded
  simp only [growOnePtSliceBsSpec, growOneStrideBsSpec, stackAt_growOne, sepExists_sepConj_right]
  have hpanic : ((blkPC_360).rebase (blkPl_360).base H).externAt? (lsρ spqrHandleErrorSym) =
      some Rust.panicked :=
    (spqr_externAt?_of_mem).trans h_panic
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hnew_lt63 : max (2 * cap.toNat) 4 < 2 ^ 63 := by omega
  have hnew_eq := grow_new_cap_eq hnew_lt63
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hnew_lay : LayoutOk (new.toNat * (16#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 16; omega, hpow, ?_⟩
    change new.toNat * 16 + 8 ≤ 2 ^ 63; omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * 16 = 0 := rfl
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 : (if (4#64).ult (0#64 <<< 1) = true then 0#64 <<< 1 else 4#64) = new := hnew_eq
    have hmul_eq : max (2 * 0) 4 * 16 = new.toNat * 16 := by rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_360).base + 60#64)
    wp_steps_lscl (lsmpl.base 361)
    have hfg0 := lscall_blk (callerProg := (blkPC_360).rebase (blkPl_360).base H)
      (finish_grow_8_zero_cells_of_fg8 hfg) ‹_›
    wp_apply
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
    have hsub_eq : max (2 * cap.toNat) 4 * 16 - bs.length = new.toNat * 16 - bs.length := by
      rw [hnew_toNat]
    have hmul_eq : max (2 * cap.toNat) 4 * 16 = new.toNat * 16 := by
      rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_360).base + 60#64)
    wp_steps_lscl (lsmpl.base 361)
    have hfg1 := lscall_blk (callerProg := (blkPC_360).rebase (blkPl_360).base H)
      (finish_grow_8_ne_cells_of_fg8 hfg) ‹_›
    wp_apply
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
    · simp only [htag, ite_false, BitVec.toNat_ofNat, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

theorem grow_one_pt_slice_bs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_360).rebase (blkPl_360).base H)
      (blkPl_360).base
      (withLsCodeLoaded lsmpl (growOnePtSliceBsSpec A)) :=
  grow_one_pt_slice_bs_placed_ok_of_fg h_panic (finish_grow_8_placed_ok hshim halloc hrealloc)

theorem grow_one_pt_slice_full_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_360).rebase (blkPl_360).base H)
      (blkPl_360).base
      (withLsCodeLoaded lsmpl (growOnePtSliceFullSpec A)) :=
  grow_one_stride_full_placed_of_bs (grow_one_pt_slice_bs_placed_ok h_panic hshim halloc hrealloc)

theorem grow_one_pt_slice_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_360).rebase (blkPl_360).base H)
      (blkPl_360).base
      (withLsCodeLoaded lsmpl (growOnePtSliceSpec A)) :=
  grow_one_stride_empty_placed_of_bs (grow_one_pt_slice_bs_placed_ok h_panic hshim halloc hrealloc)

end CryptoVerification.SpqrV1.Alloc
