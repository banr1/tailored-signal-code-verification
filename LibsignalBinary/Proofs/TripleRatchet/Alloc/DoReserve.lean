/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContracts
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrow
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `RawVecInner::reserve::do_reserve_and_handle` (`0x4cac`)

Verifies `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]`
(`0x4cac`, 35 instructions) against both:
- `doReserveRawSpec A` (16-byte `RawVecInner` at `v`, leaving `[v + 16]` untouched for `BytesMut`), and
- `doReserveSpec A` (24-byte `Vec<u8>` at `v`, framing `[v + 16] = bs.length`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.InImageLift

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace DoReserveFacts

@[local arm64_norm ↓, local wp_norm ↓]
theorem doReserve_sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem doReserve_sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem doReserve_readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem doReserve_readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem doReserve_readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem doReserve_readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem doReserve_readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem doReserve_readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

theorem doReserve_fnOff : libsignalSessionCode.fnOff doReserveName = num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]")

theorem finishGrow_fnOff : libsignalSessionCode.fnOff finishGrowName = num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")

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

end DoReserveFacts

open DoReserveFacts

/-! ## Arithmetic and stack helpers for `do_reserve_and_handle` -/

private theorem adds_cs_eq_false {x2 x1 : BitVec 64}
    (h : x2.toNat + x1.toNat < 2 ^ 64) :
    (x2 + x1).ult x2 = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_add, Nat.mod_eq_of_lt h]
  omega

private theorem reserve_new_cap_eq {cap x1 x2 : BitVec 64} {len additional : Nat}
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

private theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide), memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_doReserve_opt {fgStack : Nat}
    (hstack : fgStack + 64 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (fgStack + 64) =
      stackAt (sp - 64#64) fgStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := stackAt_split_cells sp fgStack 8 hstack
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

/-! ## Cell-unfolded `finish_grow` specs for `stride = 1, align = 1` -/

private abbrev FG1Ghost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

private def finishGrow1ZeroSpecWithStack (A : RustAlloc) (fgStack : Nat) : Spec FG1Ghost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 1#64 ∧ s.readReg64 .x5 = 1#64 ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ stackAt fsp fgStack
  post := fun (out, _cap, _ptr, new, _bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' new.toNat 1 ∗ memRegion p' new.toNat) ∗
      A.pool ∗ stackAt fsp fgStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem finish_grow_1_zero_ok_of_fg_opt {oimg : Option Obj.Image} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (specWithOptInv oimg (finishGrowSpecWithStack A hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (specWithOptInv oimg (finishGrow1ZeroSpecWithStack A (hookStack + 48))) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp
  simp only [finishGrow1ZeroSpecWithStack, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, 1#64, 1#64, []⟩
  have hlay : LayoutOk (new.toNat * (1#64 : BitVec 64).toNat) (1#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 1; omega, ⟨0, rfl⟩, ?_⟩
    change new.toNat * 1 + 1 ≤ 2 ^ 63; omega
  have hpre' : s0.mem ⊨ (specWithOptInv oimg (finishGrowSpecWithStack A hookStack)).pre hcall s0 ∗ R := by
    simp only [finishGrowSpecWithStack, hcall, FinishGrowCall.oldBuf, ite_true,
      memRegion_24_cells, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrowSpecWithStack, finishGrow1ZeroSpecWithStack, hcall,
      FinishGrowCall.oldBuf, ite_true, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * (1#64 : BitVec 64).toNat), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg0_err, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      have hm1 : new.toNat * (1#64 : BitVec 64).toNat = new.toNat := Nat.mul_one _
      have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
      rw [hm1] at hq ⊢
      rw [ha1] at hq
      rw [pull_fg0_ok, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.2⟩, ?_⟩
      simpa only [sepConj_assoc] using hq.2
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

private def finishGrow1NeSpecWithStack (A : RustAlloc) (fgStack : Nat) : Spec FG1Ghost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 1#64 ∧ s.readReg64 .x5 = 1#64 ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length ≤ cap.toNat ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
    A.pool ∗ stackAt fsp fgStack
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
      A.pool ∗ stackAt fsp fgStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem finish_grow_1_ne_ok_of_fg_opt {oimg : Option Obj.Image} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (specWithOptInv oimg (finishGrowSpecWithStack A hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (specWithOptInv oimg (finishGrow1NeSpecWithStack A (hookStack + 48))) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp
  simp only [finishGrow1NeSpecWithStack, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, 1#64, 1#64, bs⟩
  have hlay : LayoutOk (new.toNat * (1#64 : BitVec 64).toNat) (1#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 1; omega, ⟨0, rfl⟩, ?_⟩
    change new.toNat * 1 + 1 ≤ 2 ^ 63; omega
  have hpre' : s0.mem ⊨ (specWithOptInv oimg (finishGrowSpecWithStack A hookStack)).pre hcall s0 ∗ R := by
    simp only [finishGrowSpecWithStack, hcall, FinishGrowCall.oldBuf, hcap, ite_false,
      memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    have hm_cap : cap.toNat * (1#64 : BitVec 64).toNat = cap.toNat := Nat.mul_one _
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [hm_cap, ha1]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrowSpecWithStack, finishGrow1NeSpecWithStack, hcall,
      FinishGrowCall.oldBuf, hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    have hm_new : new.toNat * (1#64 : BitVec 64).toNat = new.toNat := Nat.mul_one _
    have hm_cap : cap.toNat * (1#64 : BitVec 64).toNat = cap.toNat := Nat.mul_one _
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [hm_new, hm_cap, ha1] at hq
    refine ⟨tag, p', BitVec.ofNat 64 new.toNat, ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hq.1.2, ?_⟩
      simpa only [sepConj_assoc] using hq.2
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.2⟩, ?_⟩
      simpa only [sepConj_assoc] using hq.2
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

/-! ## Verification of `do_reserve_and_handle` (`doReserveRawSpec` and `doReserveSpec`) -/

attribute [local irreducible] Program.fnOff

theorem do_reserve_raw_ok_of_fg_opt {oimg : Option Obj.Image} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hstack : (hookStack + 48) + 64 ≤ 2 ^ 64 := by decide)
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (specWithOptInv oimg (finishGrowSpecWithStack A hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserveName)
      (specWithOptInv oimg (doReserveRawSpecWithStack A (hookStack + 48))) := by
  unfold specWithOptInv
  simp only [doReserveRawSpecWithStack, stackAt_doReserve_opt hstack, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff doReserveName = num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") :=
    doReserve_fnOff
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := doReserveName) (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]"))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := finish_grow_1_zero_ok_of_fg_opt hfg
  have hfg1 := finish_grow_1_ne_ok_of_fg_opt hfg
  rw [Program.fnAddr_rel (name := doReserveName)
    hfn finishGrow_fnOff (k := num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]" - ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]")) (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]")) 140
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢
  clear hfn hfg
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr doReserveName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, additional⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv oimg s0 := by assumption
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
         else 8#64) = new := by
      exact hnew_eq
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero]
    apply SepWPp.of_sepWP (mid := entry + bv% (88))
    apply SepWP.seq_optImage (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]" - ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]")) hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv1
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]"))
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
  · have hcap0' : cap ≠ 0 := hcap0
    simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq : reserveCap cap.toNat bs.length additional - bs.length = new.toNat - bs.length := by
      rw [hnew_toNat]
    rw [hsub_eq]
    apply SepWPp.of_sepWP (mid := entry + bv% (88))
    apply SepWP.seq_optImage (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]" - ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]")) hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv1
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]"))
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

theorem do_reserve_raw_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserveName)
      (doReserveRawSpec A) :=
  subroutine_ok_of_optNone <|
    do_reserve_raw_ok_of_fg_opt (by decide)
      (subroutine_ok_to_optNone (finish_grow_ok_ext hA))

theorem do_reserve_raw_ok_trap {A : RustAlloc} {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr doReserveName)
      (doReserveRawSpec A) :=
  do_reserve_raw_ok_ext (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA)

/-- `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]`
(`0x4cac`) meets `doReserveRawSpec A` on `tripleRatchetProgAt`. -/
theorem do_reserve_raw_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr doReserveName)
      (doReserveRawSpec A) :=
  (trTrapProgAt_fnAddr_eq b C ctl abs doReserveName).rec
    (motive := fun addr _ => subroutine_ok (tripleRatchetProgAt b C ctl abs) addr (doReserveRawSpec A))
    (subroutine_ok_kit_of_trTrap (do_reserve_raw_ok_trap hA))

theorem vecU8At_eq_shared_lb (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  ac_rfl

private abbrev vecU8At_eq := @vecU8At_eq_shared_lb

theorem do_reserve_ok_of_raw_opt {oimg : Option Obj.Image} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)} {fgStack : Nat}
    (hraw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserveName)
      (specWithOptInv oimg (doReserveRawSpecWithStack A fgStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserveName)
      (specWithOptInv oimg (doReserveSpecWithStack A fgStack)) := by
  refine subroutine_ok_outcome_intro ?_
  intro x R s0 hpc hrun hpre hsp
  simp only [doReserveSpecWithStack, vecU8At_eq, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ⟨hlen, hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ (specWithOptInv oimg (doReserveRawSpecWithStack A fgStack)).pre x s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [doReserveRawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound⟩, ?_⟩
    rwa [doReserve_pre_repack]
  refine hraw.mono_outcome x
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [doReserveRawSpecWithStack, doReserveSpecWithStack,
      vecU8At_eq] at hq ⊢
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
    dsimp only [specWithOptInv, doReserveRawSpecWithStack, doReserveSpecWithStack] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [specWithOptInv] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem do_reserve_ok_of_fg_opt {oimg : Option Obj.Image} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hstack : (hookStack + 48) + 64 ≤ 2 ^ 64 := by decide)
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (specWithOptInv oimg (finishGrowSpecWithStack A hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserveName)
      (specWithOptInv oimg (doReserveSpecWithStack A (hookStack + 48))) :=
  do_reserve_ok_of_raw_opt (do_reserve_raw_ok_of_fg_opt hstack hfg)

theorem do_reserve_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserveName)
      (doReserveSpec A) :=
  subroutine_ok_of_optNone <|
    do_reserve_ok_of_raw_opt (subroutine_ok_to_optNone (do_reserve_raw_ok_ext hA))

theorem do_reserve_ok_trap {A : RustAlloc} {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr doReserveName)
      (doReserveSpec A) :=
  do_reserve_ok_ext (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA)

/-- `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]`
(`0x4cac`) meets `doReserveSpec A` on `tripleRatchetProgAt`. -/
theorem do_reserve_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr doReserveName)
      (doReserveSpec A) :=
  (trTrapProgAt_fnAddr_eq b C ctl abs doReserveName).rec
    (motive := fun addr _ => subroutine_ok (tripleRatchetProgAt b C ctl abs) addr (doReserveSpec A))
    (subroutine_ok_kit_of_trTrap (do_reserve_ok_trap hA))

theorem do_reserve_raw_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserveName)
      ((doReserveRawSpecX A).inImage img) :=
  do_reserve_raw_ok_of_fg_opt (oimg := some img) (by decide)
    (finish_grow_ok_ext_x hA)

theorem do_reserve_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserveName)
      ((doReserveSpecX A).inImage img) :=
  do_reserve_ok_of_raw_opt (oimg := some img) (do_reserve_raw_ok_ext_x hA)

/-! ## Relocatable Per-Block Proofs (`[LibsignalPlacement]`, Block `13`, calling Block `45`) -/

private theorem finish_grow_1_zero_placed_ok_of_fg_opt [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrowSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrow1ZeroSpecWithStack A (hookStack + 48)) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp
  simp only [finishGrow1ZeroSpecWithStack, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, 1#64, 1#64, []⟩
  have hlay : LayoutOk (new.toNat * (1#64 : BitVec 64).toNat) (1#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 1; omega, ⟨0, rfl⟩, ?_⟩
    change new.toNat * 1 + 1 ≤ 2 ^ 63; omega
  have hpre' : s0.mem ⊨ (finishGrowSpecWithStack A hookStack).pre hcall s0 ∗ R := by
    simp only [finishGrowSpecWithStack, hcall, FinishGrowCall.oldBuf, ite_true,
      memRegion_24_cells, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrowSpecWithStack, finishGrow1ZeroSpecWithStack, hcall,
      FinishGrowCall.oldBuf, ite_true, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * (1#64 : BitVec 64).toNat), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg0_err, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      have hm1 : new.toNat * (1#64 : BitVec 64).toNat = new.toNat := Nat.mul_one _
      have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
      rw [hm1] at hq ⊢
      rw [ha1] at hq
      rw [pull_fg0_ok, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.2⟩, ?_⟩
      simpa only [sepConj_assoc] using hq.2
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

private theorem finish_grow_1_ne_placed_ok_of_fg_opt [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrowSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrow1NeSpecWithStack A (hookStack + 48)) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp
  simp only [finishGrow1NeSpecWithStack, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, 1#64, 1#64, bs⟩
  have hlay : LayoutOk (new.toNat * (1#64 : BitVec 64).toNat) (1#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 1; omega, ⟨0, rfl⟩, ?_⟩
    change new.toNat * 1 + 1 ≤ 2 ^ 63; omega
  have hpre' : s0.mem ⊨ (finishGrowSpecWithStack A hookStack).pre hcall s0 ∗ R := by
    simp only [finishGrowSpecWithStack, hcall, FinishGrowCall.oldBuf, hcap, ite_false,
      memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    have hm_cap : cap.toNat * (1#64 : BitVec 64).toNat = cap.toNat := Nat.mul_one _
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [hm_cap, ha1]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrowSpecWithStack, finishGrow1NeSpecWithStack, hcall,
      FinishGrowCall.oldBuf, hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    have hm_new : new.toNat * (1#64 : BitVec 64).toNat = new.toNat := Nat.mul_one _
    have hm_cap : cap.toNat * (1#64 : BitVec 64).toNat = cap.toNat := Nat.mul_one _
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [hm_new, hm_cap, ha1] at hq
    refine ⟨tag, p', BitVec.ofNat 64 new.toNat, ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hq.1.2, ?_⟩
      simpa only [sepConj_assoc] using hq.2
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.2⟩, ?_⟩
      simpa only [sepConj_assoc] using hq.2
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

theorem do_reserve_raw_placed_ok_of_fg_opt [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : (hookStack + 48) + 64 ≤ 2 ^ 64 := by decide)
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base
      (finishGrowSpecWithStack A hookStack))
    (hpanic : ((blkPC_13).rebase (blkPl_13).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack A (hookStack + 48))) := by
  unfold withLsCodeLoaded
  simp only [doReserveRawSpecWithStack, stackAt_doReserve_opt hstack, sepExists_sepConj_right]
  have hfg0 := ls_subroutine_ok_of_block (callerProg := (blkPC_13).rebase (blkPl_13).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain (finish_grow_1_zero_placed_ok_of_fg_opt hfg))
  have hfg1 := ls_subroutine_ok_of_block (callerProg := (blkPC_13).rebase (blkPl_13).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain (finish_grow_1_ne_placed_ok_of_fg_opt hfg))
  change subroutine_ok _ (lsmpl.base 45) _ at hfg0 hfg1
  dsimp only [withLsCodeLoaded,
    finishGrow1ZeroSpecWithStack, finishGrow1NeSpecWithStack] at hfg0 hfg1
  clear hfg
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, additional⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = bs.length := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63 := by
    dsimp only [reserveCap] at *; omega
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
         else 8#64) = new := by
      exact hnew_eq
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero]
    apply SepWPp.of_sepWP (mid := (blkPl_13).base + bv% (88))
    apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 45)
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hcl1
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
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
  · have hcap0' : cap ≠ 0 := hcap0
    simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq : reserveCap cap.toNat bs.length additional - bs.length = new.toNat - bs.length := by
      rw [hnew_toNat]
    rw [hsub_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_13).base + bv% (88))
    apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 45)
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hcl1
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
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

theorem do_reserve_placed_ok_of_raw_opt [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {fgStack : Nat}
    (hraw : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack A fgStack))) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpecWithStack A fgStack)) := by
  refine subroutine_ok_outcome_intro ?_
  intro x R s0 hpc hrun hpre hsp
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [doReserveSpecWithStack, vecU8At_eq, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ⟨hlen, hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (doReserveRawSpecWithStack A fgStack)).pre x s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    simp only [doReserveRawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound⟩, ?_⟩
    rwa [doReserve_pre_repack]
  refine hraw.mono_outcome x
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded] at hq ⊢
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
    dsimp only [withLsCodeLoaded, doReserveRawSpecWithStack, doReserveSpecWithStack] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [withLsCodeLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-- Relocatable `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]`
(Block `13`) meets `withLsCodeLoaded lsmpl (doReserveRawSpec A)`. -/
theorem do_reserve_raw_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveRawSpec A)) :=
  do_reserve_raw_placed_ok_of_fg_opt (hookStack := allocHookStack) (by decide)
    (finish_grow_placed_ok hshim halloc hrealloc)
    ((ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic)

/-- Relocatable `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]`
(Block `13`) meets `withLsCodeLoaded lsmpl (doReserveSpec A)`. -/
theorem do_reserve_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)) :=
  do_reserve_placed_ok_of_raw_opt (do_reserve_raw_placed_ok hshim halloc hrealloc hpanic)

theorem do_reserve_raw_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecX A)) :=
  do_reserve_raw_placed_ok_of_fg_opt (hookStack := extHookStack) (by decide)
    (finish_grow_placed_ok_x hshim halloc hrealloc)
    ((ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic)

theorem do_reserve_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpecX A)) :=
  do_reserve_placed_ok_of_raw_opt (do_reserve_raw_placed_ok_x hshim halloc hrealloc hpanic)

end CryptoVerification.LibsignalTripleRatchet
