/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.Common.InImageKit

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.GrowOne.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli

abbrev cliGrowOneStack : Nat := finishGrowStackX + 64

abbrev CliGrowBytesGhost := BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)

abbrev FGCellsGhost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

theorem memRegion_bound_of_pointsTo64 {m : Memory} {b a v : BitVec 64} {n : Nat} {R : SepProp}
    (h : m ⊨ memRegion b n ∗ ((a ↦₆₄ v) ∗ R)) : n ≤ 2 ^ 64 := by
  by_cases hn0 : n = 0
  · omega
  · have hd := disjointRegions_of_coversRegion (Nat.pos_of_ne_zero hn0) (by decide)
      (IsBlock.memRegion b n).covers (IsBlock.pointsTo64 a v).covers h
    have h1 := hd.1
    omega

theorem stackAt_cliGrowOne (sp : BitVec 64) :
    stackAt sp cliGrowOneStack =
      stackAt (sp - 64#64) finishGrowStackX ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_cells sp finishGrowStackX 8 (by decide)
  change stackAt sp cliGrowOneStack =
    stackAt (sp - 64#64) finishGrowStackX ∗ cells (sp - 64#64) 8 at h1
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

theorem stackAt_split_stk (sp : BitVec 64) {stk : Nat}
    (hlo : 0x40 + finishGrowStackX ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - cliGrowOneStack) ∗
        stackAt sp cliGrowOneStack := by
  have heq : stk = cliGrowOneStack + (stk - cliGrowOneStack) := by
    dsimp [cliGrowOneStack]; omega
  conv_lhs => rw [heq]
  rw [ProofLib.stackAt_split_bottom sp cliGrowOneStack (stk - cliGrowOneStack) (by omega), ← heq]

private theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem grow_new_cap_eq {cap : BitVec 64}
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

def finishGrowZeroCellsSpec (A : RustAlloc) : Spec FGCellsGhost where
  pre := fun (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧ LayoutOk (new.toNat * stride.toNat) align.toNat⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ stackAt fsp finishGrowStackX
  post := fun (out, _cap, _ptr, new, align, stride, _bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (new.toNat * stride.toNat) align.toNat ∗
          memRegion p' (new.toNat * stride.toNat)) ∗
      A.pool ∗ stackAt fsp finishGrowStackX ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

theorem finish_grow_zero_cells_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFG : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliFinishGrowName)
      ((finishGrowSpecX A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliFinishGrowName)
      ((finishGrowZeroCellsSpec A).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (finishGrowZeroCellsSpec A).pre
    (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [finishGrowZeroCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hstr, hlay⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, align, stride, []⟩
  have hpre0 : s0.mem ⊨ (finishGrowSpecX A).pre hcall s0 ∗ R := by
    simp only [finishGrowSpecX, hcall, FinishGrowCall.oldBuf, ite_true,
      memRegion_24_cells, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, hstr, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  have hpre' := satisfies_inImage_pre hinv hpre0
  refine hFG.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, finishGrowSpecX, finishGrowZeroCellsSpec, hcall, FinishGrowCall.oldBuf,
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
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

def finishGrowNeCellsSpec (A : RustAlloc) : Spec FGCellsGhost where
  pre := fun (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length ≤ cap.toNat * stride.toNat ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧ LayoutOk (new.toNat * stride.toNat) align.toNat⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr (cap.toNat * stride.toNat) align.toNat ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * stride.toNat - bs.length) ∗
    A.pool ∗ stackAt fsp finishGrowStackX
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
      A.pool ∗ stackAt fsp finishGrowStackX ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

theorem finish_grow_ne_cells_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFG : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliFinishGrowName)
      ((finishGrowSpecX A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliFinishGrowName)
      ((finishGrowNeCellsSpec A).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (finishGrowNeCellsSpec A).pre
    (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [finishGrowNeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hstr, hlay⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, align, stride, bs⟩
  have hpre0 : s0.mem ⊨ (finishGrowSpecX A).pre hcall s0 ∗ R := by
    simp only [finishGrowSpecX, hcall, FinishGrowCall.oldBuf, hcap, ite_false,
      memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs, hle, hpos, hstr, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  have hpre' := satisfies_inImage_pre hinv hpre0
  refine hFG.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, finishGrowSpecX, finishGrowNeCellsSpec, hcall, FinishGrowCall.oldBuf,
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
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

def growOneDirBytesInnerSpec (A : RustAlloc) : Spec CliGrowBytesGhost where
  pre := fun (v, cap, ptr, bs) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length ≤ cap.toNat * 48 ∧ ptr ≠ 0#64 ∧
      max (2 * cap.toNat) 4 * 48 + 8 ≤ 2 ^ 63⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 48) 8 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 48 - bs.length)) ∗
    A.pool ∗ stackAt s.sp cliGrowOneStack
  post := fun (v, cap, _, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0⌝ ∗
      (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * 48) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * cap.toNat) 4 * 48 - bs.length)) ∗
    A.pool ∗ stackAt s0.sp cliGrowOneStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private def vecHeaderBytes (cap ptr len : BitVec 64) : List (BitVec 8) :=
  unpack64 cap ++ (unpack64 ptr ++ unpack64 len)

private theorem vecHeader_eq_bytes (a cap ptr len : BitVec 64) :
    vecHeader a cap ptr len = (a ↦ₛ vecHeaderBytes cap ptr len) := by
  unfold vecHeader vecHeaderBytes
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  simp only [pointsToBytes_append, unpack64_length, h16, ← pointsTo64_eq_pointsToBytes]

private theorem dirEntry_body_eq (b c1 p1 l1 c2 p2 l2 : BitVec 64) (R1 R2 : SepProp) :
    (vecHeader b c1 p1 l1 ∗ R1) ∗ (vecHeader (b + 0x18#64) c2 p2 l2 ∗ R2) =
      (b ↦ₛ (vecHeaderBytes c1 p1 l1 ++ vecHeaderBytes c2 p2 l2)) ∗ (R1 ∗ R2) := by
  have hl : (vecHeaderBytes c1 p1 l1).length = 24 := by simp [vecHeaderBytes, unpack64_length]
  rw [vecHeader_eq_bytes, vecHeader_eq_bytes, pointsToBytes_append, hl]
  change _ = (_ ∗ ((b + 0x18#64) ↦ₛ _)) ∗ _
  ac_rfl

private theorem dirEntry_reloc (A : RustAlloc) (e : List (BitVec 8) × List (BitVec 8)) (a : BitVec 64) :
    dirEntryAt A e a ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 48 ∧ ∀ b : BitVec 64, (b ↦ₛ bs) ∗ H ⊢ dirEntryAt A e b⌝ ∗ (a ↦ₛ bs) ∗ H := by
  dsimp only [dirEntryAt, vecU8, vecU8At]
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c1
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p1
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c2
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p2
  rw [dirEntry_body_eq]
  apply Entails.sepExists_right
    (vecHeaderBytes c1 p1 (BitVec.ofNat 64 e.1.length) ++
      vecHeaderBytes c2 p2 (BitVec.ofNat 64 e.2.length))
  apply Entails.sepExists_right
  refine Entails.pure_right ⟨by simp [vecHeaderBytes, unpack64_length], fun b => ?_⟩ (Entails.refl _)
  rw [← dirEntry_body_eq]
  exact sepConj_mono
    (Entails.sepExists_right c1 (Entails.sepExists_right p1 (Entails.refl _)))
    (Entails.sepExists_right c2 (Entails.sepExists_right p2 (Entails.refl _)))

private theorem arrayAt_dirEntry_reloc (A : RustAlloc) :
    ∀ (xs : List (List (BitVec 8) × List (BitVec 8))) (a : BitVec 64),
      arrayAt (dirEntryAt A) 48 a xs ⊢
        ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
          ⌜bs.length = xs.length * 48 ∧
            ∀ b : BitVec 64, (b ↦ₛ bs) ∗ H ⊢ arrayAt (dirEntryAt A) 48 b xs⌝ ∗
          (a ↦ₛ bs) ∗ H
  | [], a => by
    refine Entails.sepExists_right [] (Entails.sepExists_right emp ?_)
    simp only [arrayAt, pointsToBytes_nil, List.length_nil, Nat.zero_mul, emp_sepConj]
    exact Entails.pure_right ⟨trivial, fun _ => Entails.refl emp⟩ (Entails.refl emp)
  | e :: xs, a => by
    dsimp only [arrayAt]
    refine Entails.trans (sepConj_mono (dirEntry_reloc A e a) (arrayAt_dirEntry_reloc A xs (a + 48#64))) ?_
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro bs1
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro H1
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs2
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro H2
    rw [sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hl1, hr1⟩
    rw [sepConj_assoc, sepConj_pure_left_comm, sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨hl2, hr2⟩
    refine Entails.sepExists_right (bs1 ++ bs2) (Entails.sepExists_right (H1 ∗ H2) ?_)
    have hlen : (bs1 ++ bs2).length = (e :: xs).length * 48 := by
      simp only [List.length_append, List.length_cons, hl1, hl2]; omega
    refine Entails.pure_right ⟨hlen, fun b => ?_⟩ ?_
    · rw [pointsToBytes_append, hl1]
      have harr : ((b ↦ₛ bs1) ∗ ((b + 48#64) ↦ₛ bs2)) ∗ (H1 ∗ H2) =
          ((b ↦ₛ bs1) ∗ H1) ∗ (((b + 48#64) ↦ₛ bs2) ∗ H2) := by ac_rfl
      rw [harr]
      exact sepConj_mono (hr1 b) (hr2 (b + 48#64))
    · rw [pointsToBytes_append, hl1]
      exact Entails.of_eq (by ac_rfl)

theorem growOneDir_of_bytes {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hbs_ok : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneDirName)
      ((growOneDirBytesInnerSpec A).inImage img))
    (hstk : 0x40 + finishGrowStackX ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneDirName)
      (growOneDirSpec A img stk) := by
  refine subroutine_ok_outcome_intro fun ⟨v, cap, ptr, xs⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (⌜s0.readReg64 .x0 = v ∧ cap.toNat < 2 ^ 32⌝ ∗
      vecAt A 48 8 (dirEntryAt A) v cap ptr xs ∗ stackAt s0.sp stk ∗ A.pool)) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hcap32⟩, hmem⟩
  dsimp only [vecAt, vecHeader, vecBuf] at hmem
  have hmem_p : s0.mem ⊨
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
        (if cap = 0#64 then emp
         else A.live ptr (cap.toNat * 48) 8 ∗
           arrayAt (dirEntryAt A) 48 ptr xs ∗
           memRegion (ptr + BitVec.ofNat 64 (xs.length * 48))
             ((cap.toNat - xs.length) * 48)) ∗
        stackAt s0.sp stk ∗ A.pool ∗ R) := by
    convert hmem using 1; ac_rfl
  rw [satisfies_pure_sepConj] at hmem_p
  rcases hmem_p with ⟨⟨hxs_le, _, hptr_ne⟩, hmem_s⟩
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk) (a := v) (v := cap)
      (R := ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
        (if cap = 0#64 then emp
         else A.live ptr (cap.toNat * 48) 8 ∗
           arrayAt (dirEntryAt A) 48 ptr xs ∗
           memRegion (ptr + BitVec.ofNat 64 (xs.length * 48))
             ((cap.toNat - xs.length) * 48)) ∗
        A.pool ∗ R) ?_
    dsimp only [stackAt] at hmem_s
    convert hmem_s using 1; ac_rfl
  rw [stackAt_split_stk s0.sp hstk hstk_hi] at hmem_s
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cliGrowOneStack)
  let newCap := max (2 * cap.toNat) 4
  have hmax_eq : max (2 * cap.toNat) 4 = newCap := rfl
  have hbound : newCap * 48 + 8 ≤ 2 ^ 63 := by dsimp [newCap]; omega
  have hnew_toNat : (BitVec.ofNat 64 newCap).toNat = newCap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [newCap]; omega)]
  have hnew_ne : BitVec.ofNat 64 newCap ≠ 0 := by
    intro heq
    have ht := congrArg BitVec.toNat heq
    rw [hnew_toNat] at ht
    change newCap = 0 at ht
    dsimp [newCap] at ht; omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hxs0 : xs = [] :=
      List.eq_nil_of_length_eq_zero (by simpa using hxs_le)
    subst hxs0
    simp only [ite_true] at hmem_s
    let F_extra := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 0) ∗ stkRem
    have hpre0 : s0.mem ⊨ (growOneDirBytesInnerSpec A).pre (v, 0#64, ptr, []) s0 ∗ (F_extra ∗ R) := by
      simp only [growOneDirBytesInnerSpec, ite_true, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, Nat.zero_le _, hptr_ne, hbound⟩, ?_⟩
      convert hmem_s using 1
      dsimp [F_extra, stkRem]
      ac_rfl
    have hpre' := satisfies_inImage_pre hinv hpre0
    refine hbs_ok.mono_outcome (v, 0#64, ptr, []) (F_extra ∗ R) s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [Spec.inImage, growOneDirBytesInnerSpec, growOneDirSpec] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      rcases hq with ⟨htrace, hq⟩
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
      rcases hq with ⟨p', hq⟩
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
      rcases hq with ⟨⟨hp', _⟩, hmemf⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨htrace, ?_⟩
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨p', ?_⟩
      dsimp only [vecAt, vecHeader, vecBuf, List.length_nil]
      rw [hmax_eq] at hmemf ⊢
      simp only [hnew_ne, ite_false, hnew_toNat, Nat.sub_zero, Nat.zero_mul,
        pointsToBytes_nil, emp_sepConj, BitVec.add_zero] at hmemf ⊢
      have harray0 : arrayAt (dirEntryAt A) 48 p' [] = emp := rfl
      rw [harray0, emp_sepConj]
      have hpost_p : sf.mem ⊨
          ⌜0 ≤ newCap ∧ newCap * 48 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
          (((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
            ((v + 16#64) ↦₆₄ BitVec.ofNat 64 0) ∗
            (A.live p' (newCap * 48) 8 ∗ memRegion p' (newCap * 48)) ∗
            (stkRem ∗ stackAt s0.sp cliGrowOneStack) ∗ A.pool) ∗ R) := by
        rw [satisfies_pure_sepConj]
        refine ⟨⟨Nat.zero_le _, by omega, hp'⟩, ?_⟩
        convert hmemf using 1
        dsimp [F_extra, stkRem]
        ac_rfl
      rw [← stackAt_split_stk s0.sp hstk hstk_hi] at hpost_p
      convert hpost_p using 1; ac_rfl
    · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
      dsimp only [Spec.inImage, growOneDirBytesInnerSpec, growOneDirSpec] at hq ⊢
      exact allowPanic_frame id (by rwa [sepConj_assoc])
    · exact (allowPanic_not_exited hq).elim
    · dsimp only [Spec.inImage] at hq
      exact (not_satisfies_false_sepConj hq).elim
  · simp only [hcap0, ite_false] at hmem_s
    have hsplit : s0.mem ⊨
        (∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
          ⌜bs.length = xs.length * 48 ∧
            ∀ b : BitVec 64, (b ↦ₛ bs) ∗ H ⊢ arrayAt (dirEntryAt A) 48 b xs⌝ ∗
          (ptr ↦ₛ bs) ∗ H) ∗
        ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          memRegion (ptr + BitVec.ofNat 64 (xs.length * 48))
            ((cap.toNat - xs.length) * 48) ∗
          (stkRem ∗ stackAt s0.sp cliGrowOneStack) ∗ A.pool ∗ R) := by
      refine Satisfies.mono (sepConj_mono_left (arrayAt_dirEntry_reloc A xs ptr)) ?_
      dsimp only [stkRem]
      convert hmem_s using 1; ac_rfl
    rw [sepExists_sepConj_left, satisfies_sepExists] at hsplit
    rcases hsplit with ⟨bs, hsplit⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hsplit
    rcases hsplit with ⟨H, hsplit⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hsplit
    rcases hsplit with ⟨⟨hbs_len, hrec⟩, hsplit⟩
    let F_extra := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗ H ∗ stkRem
    have hbs_le : bs.length ≤ cap.toNat * 48 := by rw [hbs_len]; omega
    have hmr_old :
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 48 - bs.length) =
        memRegion (ptr + BitVec.ofNat 64 (xs.length * 48)) ((cap.toNat - xs.length) * 48) := by
      rw [hbs_len, Nat.sub_mul]
    have hpre0 : s0.mem ⊨ (growOneDirBytesInnerSpec A).pre (v, cap, ptr, bs) s0 ∗ (F_extra ∗ R) := by
      simp only [growOneDirBytesInnerSpec, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, hbs_le, hptr_ne, hbound⟩, ?_⟩
      rw [hmr_old]
      convert hsplit using 1
      dsimp [F_extra, stkRem]
      ac_rfl
    have hpre' := satisfies_inImage_pre hinv hpre0
    refine hbs_ok.mono_outcome (v, cap, ptr, bs) (F_extra ∗ R) s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [Spec.inImage, growOneDirBytesInnerSpec, growOneDirSpec] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      rcases hq with ⟨htrace, hq⟩
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
      rcases hq with ⟨p', hq⟩
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
      rcases hq with ⟨⟨hp', _⟩, hmemf⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨htrace, ?_⟩
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨p', ?_⟩
      dsimp only [vecAt, vecHeader, vecBuf]
      rw [hmax_eq] at hmemf ⊢
      simp only [hnew_ne, ite_false, hnew_toNat]
      have hmr_new :
          memRegion (p' + BitVec.ofNat 64 bs.length) (newCap * 48 - bs.length) =
          memRegion (p' + BitVec.ofNat 64 (xs.length * 48)) ((newCap - xs.length) * 48) := by
        rw [hbs_len, Nat.sub_mul]
      have hreasm : sf.mem ⊨
          arrayAt (dirEntryAt A) 48 p' xs ∗
          (((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
            ((v + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
            A.live p' (newCap * 48) 8 ∗
            memRegion (p' + BitVec.ofNat 64 (xs.length * 48)) ((newCap - xs.length) * 48) ∗
            (stkRem ∗ stackAt s0.sp cliGrowOneStack) ∗ A.pool) ∗ R) := by
        refine Satisfies.mono (sepConj_mono_left (hrec p')) ?_
        rw [hmr_new] at hmemf
        convert hmemf using 1
        dsimp [F_extra, stkRem]
        ac_rfl
      rw [← stackAt_split_stk s0.sp hstk hstk_hi] at hreasm
      have hpost_p : sf.mem ⊨
          ⌜xs.length ≤ newCap ∧ newCap * 48 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
          (((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
            ((v + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
            (A.live p' (newCap * 48) 8 ∗ arrayAt (dirEntryAt A) 48 p' xs ∗
              memRegion (p' + BitVec.ofNat 64 (xs.length * 48)) ((newCap - xs.length) * 48)) ∗
            stackAt s0.sp stk ∗ A.pool) ∗ R) := by
        rw [satisfies_pure_sepConj]
        refine ⟨⟨by dsimp [newCap]; omega, by omega, hp'⟩, ?_⟩
        convert hreasm using 1; ac_rfl
      convert hpost_p using 1; ac_rfl
    · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
      dsimp only [Spec.inImage, growOneDirBytesInnerSpec, growOneDirSpec] at hq ⊢
      exact allowPanic_frame id (by rwa [sepConj_assoc])
    · exact (allowPanic_not_exited hq).elim
    · dsimp only [Spec.inImage] at hq
      exact (not_satisfies_false_sepConj hq).elim

end CryptoVerification.SignalSession.Cli.GrowOne.Helpers
