/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Defs
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.FromRecordCalleesCodeSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrow
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import ProofLib.SepLogic.WPp

/-!
# Verification of `RawVec<SignalProtocolError>::grow_one` and `RawVec<Chain>::grow_one`

Proves fixed-image and relocatable `[LibsignalPlacement]` contracts for
`<RawVec<SignalProtocolError>>::grow_one` (`0x15c44`, block `42`, stride `48`) and
`<RawVec<Chain>>::grow_one` (`0x15cac`, block `43`, stride `104`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Stack and arithmetic helpers for `grow_one<SignalProtocolError>` -/

private theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide), memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private def growPad (sp : BitVec 64) : SepProp :=
  memRegion (sp - 4608#64) 400

private theorem stackAt_grow_one_spe (sp : BitVec 64) :
    stackAt sp growOneSpeStack =
      growPad sp ∗
      (stackAt (sp - 64#64) finishGrowStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7))) := by
  have h1 := stackAt_split_bottom sp 4208 400 (by decide)
  have h2 := stackAt_split_cells sp 4144 8 (by decide)
  change stackAt sp growOneSpeStack = growPad sp ∗ stackAt sp 4208 at h1
  change stackAt sp 4208 = stackAt (sp - 64#64) finishGrowStack ∗ cells (sp - 64#64) 8 at h2
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, h2, hc8]

private theorem grow_spe_new_cap_eq {cap : BitVec 64}
    (h : max (2 * cap.toNat) 4 * 48 ≤ 9223372036854775800) :
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

private theorem SepWPp.ite_elim_pure1 {prog : Program} {ret : BitVec 64} {s : State}
    {c : Prop} [Decidable c] {φ ψ : Prop} {R2 F : SepProp} {Q Qp : State → SepProp → Prop}
    (hthen : c → φ → SepWPp prog ret s F Q Qp)
    (helse : ¬ c → ψ → SepWPp prog ret s (R2 ∗ F) Q Qp) :
    SepWPp prog ret s ((if c then ⌜φ⌝ else ⌜ψ⌝ ∗ R2) ∗ F) Q Qp := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact SepWPp.pure_elim (hthen hc)
  · simp only [hc, ite_false, sepConj_assoc]; exact SepWPp.pure_elim (helse hc)

private theorem SepWPp.ite_elim_pure2 {prog : Program} {ret : BitVec 64} {s : State}
    {c : Prop} [Decidable c] {φ ψ : Prop} {R1 R2 F : SepProp} {Q Qp : State → SepProp → Prop}
    (hthen : c → φ → SepWPp prog ret s (R1 ∗ F) Q Qp)
    (helse : ¬ c → ψ → SepWPp prog ret s (R2 ∗ F) Q Qp) :
    SepWPp prog ret s ((if c then ⌜φ⌝ ∗ R1 else ⌜ψ⌝ ∗ R2) ∗ F) Q Qp := by
  by_cases hc : c
  · simp only [hc, ite_true, sepConj_assoc]; exact SepWPp.pure_elim (hthen hc)
  · simp only [hc, ite_false, sepConj_assoc]; exact SepWPp.pure_elim (helse hc)

/-! ## Cell-unfolded `finish_grow` wrappers for `stride = 48, align = 8` -/

private abbrev FG48Ghost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

private def finishGrow48ZeroSpec (A : RustAlloc) : Spec FG48Ghost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 48#64 ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat * 48 + 8 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ stackAt fsp finishGrowStack
  post := fun (out, _cap, _ptr, new, _bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
          (A.live p' (new.toNat * 48) 8 ∗ memRegion p' (new.toNat * 48))) ∗
      A.pool ∗ stackAt fsp finishGrowStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem finish_grow_48_zero_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName) (finishGrowSpec A)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (finishGrow48ZeroSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow48ZeroSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, 8#64, 48#64, []⟩
  have hlay : LayoutOk (new.toNat * (48#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 48; omega, ⟨3, rfl⟩, ?_⟩
    change new.toNat * 48 + 8 ≤ 2 ^ 63; omega
  have hpre' : s0.mem ⊨ (finishGrowSpec A).pre hcall s0 ∗ R := by
    simp only [finishGrowSpec, hcall, FinishGrowCall.oldBuf, ite_true,
      memRegion_24_cells, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrowSpec, finishGrow48ZeroSpec, hcall, FinishGrowCall.oldBuf,
      ite_true, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    have hm48 : (48#64 : BitVec 64).toNat = 48 := rfl
    have ha8 : (8#64 : BitVec 64).toNat = 8 := rfl
    rw [hm48, ha8] at hq
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * 48), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [show (out ↦₆₄ 1#64 ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 48) ∗
            ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
            A.pool ∗ stackAt s0.sp finishGrowStack) ∗ R =
          ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
            ((A.pool ∗ stackAt s0.sp finishGrowStack ∗ out ↦₆₄ 1#64 ∗
              (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 48)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [show (out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 48) ∗
            (⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
              A.live p' (new.toNat * 48) 8 ∗ memRegion p' (new.toNat * 48)) ∗
            A.pool ∗ stackAt s0.sp finishGrowStack) ∗ R =
          ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
            ((A.live p' (new.toNat * 48) 8 ∗ memRegion p' (new.toNat * 48) ∗
              A.pool ∗ stackAt s0.sp finishGrowStack ∗
              out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 48)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.2⟩, ?_⟩
      simpa only [sepConj_assoc] using hq.2
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

private def finishGrow48NeSpec (A : RustAlloc) : Spec FG48Ghost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 48#64 ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length = cap.toNat * 48 ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat * 48 + 8 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs) ∗
    A.pool ∗ stackAt fsp finishGrowStack
  post := fun (out, _cap, ptr, new, bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          (A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs))
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
          (A.live p' (new.toNat * 48) 8 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 48 - bs.length))) ∗
      A.pool ∗ stackAt fsp finishGrowStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem finish_grow_48_ne_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName) (finishGrowSpec A)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (finishGrow48NeSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow48NeSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, 8#64, 48#64, bs⟩
  have hlay : LayoutOk (new.toNat * (48#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 48; omega, ⟨3, rfl⟩, ?_⟩
    change new.toNat * 48 + 8 ≤ 2 ^ 63; omega
  have hm48 : (48#64 : BitVec 64).toNat = 48 := rfl
  have ha8 : (8#64 : BitVec 64).toNat = 8 := rfl
  have hpre' : s0.mem ⊨ (finishGrowSpec A).pre hcall s0 ∗ R := by
    simp only [finishGrowSpec, hcall, FinishGrowCall.oldBuf, hcap, ite_false,
      memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [hm48, ha8, ← hbs, Nat.sub_self, memRegion_zero, sepConj_emp, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, Nat.le_refl _, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrowSpec, finishGrow48NeSpec, hcall, FinishGrowCall.oldBuf,
      hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    rw [hm48, ha8, ← hbs, Nat.sub_self, memRegion_zero, sepConj_emp] at hq
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * 48), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [show (out ↦₆₄ 1#64 ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 48) ∗
            (⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
              A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
            A.pool ∗ stackAt s0.sp finishGrowStack) ∗ R =
          ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
            ((A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs) ∗
              A.pool ∗ stackAt s0.sp finishGrowStack ∗
              out ↦₆₄ 1#64 ∗ (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 48)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hq.1.2, ?_⟩
      simpa only [sepConj_assoc] using hq.2
    · simp only [htag, ite_false] at hq ⊢
      rw [show (out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 48) ∗
            (⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
              A.live p' (new.toNat * 48) 8 ∗ (p' ↦ₛ bs) ∗
              memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 48 - bs.length)) ∗
            A.pool ∗ stackAt s0.sp finishGrowStack) ∗ R =
          ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
            ((A.live p' (new.toNat * 48) 8 ∗ (p' ↦ₛ bs) ∗
              memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 48 - bs.length) ∗
              A.pool ∗ stackAt s0.sp finishGrowStack ∗
              out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 48)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.2⟩, ?_⟩
      simpa only [sepConj_assoc] using hq.2
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

/-! ## Unified `grow_one_spe_ok` -/

theorem grow_one_spe_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hfg : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName) (finishGrowSpec A)) :
    GrowOneSpeOkExt b A ext := by
  unfold GrowOneSpeOkExt growOneSpeSpec growOneSpeName
  simp only [stackAt_grow_one_spe, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one")
  have hpanic := panic_at_handle_error_ext (b := b) (ext := ext)
    (name := "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one")
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one"))
  have hfg0 := finish_grow_48_zero_ok (b := b) (ext := ext) hfg
  have hfg1 := finish_grow_48_ne_ok (b := b) (ext := ext) hfg
  rw [Program.fnAddr_rel
    (name := "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one")
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]") (k := 416) (by decide)] at hfg0 hfg1
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one")) 0 104
  wpp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hnew_eq := grow_spe_new_cap_eq h
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hnew_bound : new.toNat * 48 + 8 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero h_2
    subst hbs
    simp only [BitVec.ofNat_eq_ofNat, ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_zero, Nat.mul_zero, Nat.sub_zero]
    apply SepWPp.of_sepWP (mid := entry + bv% (60))
    wp_steps
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by first | rfl | assumption) (by first | rfl | assumption)
    refine SepWPp.ite_elim_pure1 (fun htag htrace => ?_) (fun _ ⟨hw0, hp', htrace⟩ => ?_)
    · subst htag
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one"))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun_sf)
      refine SepWPp.panic (by exact hrun_sf) hpanic fun hm => ?_
      exact allowPanic_panicked
        (allocFailedIn_of_eq (htrace : (Rust.panicked _).trace = s0.trace ++ [allocFailedEvent])) hm
    · subst hw0
      rw [sepConj_assoc]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · have hcap0' : cap ≠ 0 := hcap0
    simp only [hcap0', ite_false, sepConj_assoc]
    have hsub_mul : (max (2 * cap.toNat) 4 - cap.toNat) * 48 = new.toNat * 48 - bs.length := by
      rw [Nat.sub_mul, hnew_toNat, h_2]
    rw [hsub_mul]
    apply SepWPp.of_sepWP (mid := entry + bv% (60))
    wp_steps
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done hpc_sf hrun_sf
    refine SepWPp.ite_elim_pure2 (fun htag htrace => ?_) (fun _ ⟨hw0, hp', htrace⟩ => ?_)
    · subst htag
      rw [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one"))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun_sf)
      refine SepWPp.panic (by exact hrun_sf) hpanic fun hm => ?_
      rw [← sepConj_assoc]
      exact allowPanic_panicked
        (allocFailedIn_of_eq (htrace : (Rust.panicked _).trace = s0.trace ++ [allocFailedEvent])) hm
    · subst hw0
      rw [sepConj_assoc, sepConj_assoc]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

theorem grow_one_spe_ok_trap {A : RustAlloc} {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    GrowOneSpeOk_trap b C A abs :=
  grow_one_spe_ok_ext (finish_grow_ok_trap hA)

/-- `<alloc::raw_vec::RawVec<SignalProtocolError>>::grow_one` (`0x15c44`, 26 insns) meets
`growOneSpeSpec A` on `tripleRatchetProgAt`. -/
theorem grow_one_spe_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    GrowOneSpeOk b C A ctl abs :=
  subroutine_ok_kit_of_trTrap (grow_one_spe_ok_trap hA)

/-! ## `RawVec<Chain>::grow_one` (`0x15cac`, stride = 104, align = 8) under `AllocContractsX` -/

private def growPad104X (sp : BitVec 64) : SepProp :=
  memRegion (sp - 16896#64) 400

private theorem stackAt_grow_one_104_x (sp : BitVec 64) :
    stackAt sp (464 + finishGrowStackX) =
      growPad104X sp ∗
      (stackAt (sp - 64#64) finishGrowStackX ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7))) := by
  have h1 := stackAt_split_bottom sp 16496 400 (by decide)
  have h2 := stackAt_split_cells sp 16432 8 (by decide)
  change stackAt sp (464 + finishGrowStackX) = growPad104X sp ∗ stackAt sp 16496 at h1
  change stackAt sp 16496 = stackAt (sp - 64#64) finishGrowStackX ∗ cells (sp - 64#64) 8 at h2
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, h2, hc8]

private theorem grow_104_new_cap_eq {cap : BitVec 64}
    (h : max (2 * cap.toNat) 4 * 104 ≤ 9223372036854775800) :
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

private def finishGrow104ZeroSpecX (A : RustAlloc) : Spec FG48Ghost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 104#64 ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat * 104 + 8 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ stackAt fsp finishGrowStackX
  post := fun (out, _cap, _ptr, new, _bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
          (A.live p' (new.toNat * 104) 8 ∗ memRegion p' (new.toNat * 104))) ∗
      A.pool ∗ stackAt fsp finishGrowStackX ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem finish_grow_104_zero_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hfg : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrowName) ((finishGrowSpecX A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrowName)
      ((finishGrow104ZeroSpecX A).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, finishGrow104ZeroSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, 8#64, 104#64, []⟩
  have hlay : LayoutOk (new.toNat * (104#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 104; omega, ⟨3, rfl⟩, ?_⟩
    change new.toNat * 104 + 8 ≤ 2 ^ 63; omega
  have hpre' : s0.mem ⊨ ((finishGrowSpecX A).inImage img).pre hcall s0 ∗ R := by
    simp only [Spec.inImage, finishGrowSpecX, hcall, FinishGrowCall.oldBuf, ite_true,
      memRegion_24_cells, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, finishGrowSpecX, finishGrow104ZeroSpecX, hcall, FinishGrowCall.oldBuf,
      ite_true, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    have hm104 : (104#64 : BitVec 64).toNat = 104 := rfl
    have ha8 : (8#64 : BitVec 64).toNat = 8 := rfl
    rw [hm104, ha8] at hq
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * 104), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [show (out ↦₆₄ 1#64 ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104) ∗
            ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
            A.pool ∗ stackAt s0.sp finishGrowStackX) ∗ R =
          ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
            ((A.pool ∗ stackAt s0.sp finishGrowStackX ∗ out ↦₆₄ 1#64 ∗
              (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [show (out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104) ∗
            (⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
              A.live p' (new.toNat * 104) 8 ∗ memRegion p' (new.toNat * 104)) ∗
            A.pool ∗ stackAt s0.sp finishGrowStackX) ∗ R =
          ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
            ((A.live p' (new.toNat * 104) 8 ∗ memRegion p' (new.toNat * 104) ∗
              A.pool ∗ stackAt s0.sp finishGrowStackX ∗
              out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.2⟩, ?_⟩
      simpa only [sepConj_assoc] using hq.2
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

private def finishGrow104NeSpecX (A : RustAlloc) : Spec FG48Ghost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 104#64 ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length = cap.toNat * 104 ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat * 104 + 8 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs) ∗
    A.pool ∗ stackAt fsp finishGrowStackX
  post := fun (out, _cap, ptr, new, bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          (A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs))
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
          (A.live p' (new.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 104 - bs.length))) ∗
      A.pool ∗ stackAt fsp finishGrowStackX ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem finish_grow_104_ne_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hfg : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrowName) ((finishGrowSpecX A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrowName)
      ((finishGrow104NeSpecX A).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, finishGrow104NeSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, 8#64, 104#64, bs⟩
  have hlay : LayoutOk (new.toNat * (104#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 104; omega, ⟨3, rfl⟩, ?_⟩
    change new.toNat * 104 + 8 ≤ 2 ^ 63; omega
  have hm104 : (104#64 : BitVec 64).toNat = 104 := rfl
  have ha8 : (8#64 : BitVec 64).toNat = 8 := rfl
  have hpre' : s0.mem ⊨ ((finishGrowSpecX A).inImage img).pre hcall s0 ∗ R := by
    simp only [Spec.inImage, finishGrowSpecX, hcall, FinishGrowCall.oldBuf, hcap, ite_false,
      memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [hm104, ha8, ← hbs, Nat.sub_self, memRegion_zero, sepConj_emp, sepConj_assoc,
      satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, Nat.le_refl _, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, finishGrowSpecX, finishGrow104NeSpecX, hcall, FinishGrowCall.oldBuf,
      hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    rw [hm104, ha8, ← hbs, Nat.sub_self, memRegion_zero, sepConj_emp] at hq
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * 104), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [show (out ↦₆₄ 1#64 ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104) ∗
            (⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
              A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
            A.pool ∗ stackAt s0.sp finishGrowStackX) ∗ R =
          ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
            ((A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs) ∗
              A.pool ∗ stackAt s0.sp finishGrowStackX ∗
              out ↦₆₄ 1#64 ∗ (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hq.1.2, ?_⟩
      simpa only [sepConj_assoc] using hq.2
    · simp only [htag, ite_false] at hq ⊢
      rw [show (out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104) ∗
            (⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
              A.live p' (new.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
              memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 104 - bs.length)) ∗
            A.pool ∗ stackAt s0.sp finishGrowStackX) ∗ R =
          ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
            ((A.live p' (new.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
              memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 104 - bs.length) ∗
              A.pool ∗ stackAt s0.sp finishGrowStackX ∗
              out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.2⟩, ?_⟩
      simpa only [sepConj_assoc] using hq.2
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

/-- `growOneSpec A` at `464 + finishGrowStackX`. -/
def growOne104SpecX (A : RustAlloc) : Spec GrowGhost where
  pre := fun (v, cap, ptr, bs) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length = cap.toNat * 104 ∧ ptr ≠ 0 ∧
      max (2 * cap.toNat) 4 * 104 + 8 ≤ 2 ^ 63⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
    A.pool ∗ stackAt s.sp (464 + finishGrowStackX)
  post := fun (v, cap, _, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0⌝ ∗ (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * 104) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * 104) ∗
      A.pool ∗ stackAt s0.sp (464 + finishGrowStackX)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `<alloc::raw_vec::RawVec<Chain>>::grow_one` (`0x15cac`, 26 insns) meets
`(growOne104SpecX A).inImage img` on `tripleRatchetProgAtExt img.base ext` under `AllocContractsX`. -/
theorem grow_one_104_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")
      ((growOne104SpecX A).inImage img) := by
  have hfg := finish_grow_ok_ext_x hA
  unfold Spec.inImage growOne104SpecX
  simp only [stackAt_grow_one_104_x, sepExists_sepConj_right]
  have hfn := (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")
  have hpanic := panic_at_handle_error_ext (b := img.base) (ext := ext)
    (name := "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one"))
  have hfg0 := finish_grow_104_zero_ok_x hfg
  have hfg1 := finish_grow_104_ne_ok_x hfg
  rw [Program.fnAddr_rel
    (name := "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]") (k := 312) (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalSession.libsignalSessionBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")) 104
  wpp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hnew_eq := grow_104_new_cap_eq h
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hnew_bound : new.toNat * 104 + 8 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero h_4
    subst hbs
    simp only [BitVec.ofNat_eq_ofNat, ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_zero, Nat.mul_zero, Nat.sub_zero]
    apply SepWPp.of_sepWP (mid := entry + bv% (60))
    apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]" - ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")) hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF1, hsym1⟩
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by first | rfl | assumption) (by first | rfl | assumption)
    refine SepWPp.ite_elim_pure1 (fun htag htrace => ?_) (fun _ ⟨hw0, hp', htrace⟩ => ?_)
    · subst htag
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one"))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun_sf)
      refine SepWPp.panic (by exact hrun_sf) hpanic fun hm => ?_
      exact allowPanic_panicked
        (allocFailedIn_of_eq (htrace : (Rust.panicked _).trace = s0.trace ++ [allocFailedEvent])) hm
    · subst hw0
      rw [sepConj_assoc]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · have hcap0' : cap ≠ 0 := hcap0
    simp only [hcap0', ite_false, sepConj_assoc]
    have hsub_mul : (max (2 * cap.toNat) 4 - cap.toNat) * 104 = new.toNat * 104 - bs.length := by
      rw [Nat.sub_mul, hnew_toNat, h_4]
    rw [hsub_mul]
    apply SepWPp.of_sepWP (mid := entry + bv% (60))
    apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]" - ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")) hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF1, hsym1⟩
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done hpc_sf hrun_sf
    refine SepWPp.ite_elim_pure2 (fun htag htrace => ?_) (fun _ ⟨hw0, hp', htrace⟩ => ?_)
    · subst htag
      rw [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one"))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun_sf)
      refine SepWPp.panic (by exact hrun_sf) hpanic fun hm => ?_
      rw [← sepConj_assoc]
      exact allowPanic_panicked
        (allocFailedIn_of_eq (htrace : (Rust.panicked _).trace = s0.trace ++ [allocFailedEvent])) hm
    · subst hw0
      rw [sepConj_assoc, sepConj_assoc]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

/-! ## Relocatable `[LibsignalPlacement]` Contracts (Blocks `42` and `43`) -/

private theorem finish_grow_48_zero_ok_gen {A : RustAlloc} {prog : Program} {entry : BitVec 64}
    (hfg : subroutine_ok prog entry (finishGrowSpec A)) :
    subroutine_ok prog entry (finishGrow48ZeroSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow48ZeroSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, 8#64, 48#64, []⟩
  have hlay : LayoutOk (new.toNat * (48#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 48; omega, ⟨3, rfl⟩, ?_⟩
    change new.toNat * 48 + 8 ≤ 2 ^ 63; omega
  have hpre' : s0.mem ⊨ (finishGrowSpec A).pre hcall s0 ∗ R := by
    simp only [finishGrowSpec, hcall, FinishGrowCall.oldBuf, ite_true,
      memRegion_24_cells, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrowSpec, finishGrow48ZeroSpec, hcall, FinishGrowCall.oldBuf,
      ite_true, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    have hm48 : (48#64 : BitVec 64).toNat = 48 := rfl
    have ha8 : (8#64 : BitVec 64).toNat = 8 := rfl
    rw [hm48, ha8] at hq
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * 48), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [show (out ↦₆₄ 1#64 ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 48) ∗
            ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
            A.pool ∗ stackAt s0.sp finishGrowStack) ∗ R =
          ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
            ((A.pool ∗ stackAt s0.sp finishGrowStack ∗ out ↦₆₄ 1#64 ∗
              (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 48)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [show (out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 48) ∗
            (⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
              A.live p' (new.toNat * 48) 8 ∗ memRegion p' (new.toNat * 48)) ∗
            A.pool ∗ stackAt s0.sp finishGrowStack) ∗ R =
          ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
            ((A.live p' (new.toNat * 48) 8 ∗ memRegion p' (new.toNat * 48) ∗
              A.pool ∗ stackAt s0.sp finishGrowStack ∗
              out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 48)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.2⟩, ?_⟩
      simpa only [sepConj_assoc] using hq.2
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

private theorem finish_grow_48_ne_ok_gen {A : RustAlloc} {prog : Program} {entry : BitVec 64}
    (hfg : subroutine_ok prog entry (finishGrowSpec A)) :
    subroutine_ok prog entry (finishGrow48NeSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow48NeSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, 8#64, 48#64, bs⟩
  have hlay : LayoutOk (new.toNat * (48#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 48; omega, ⟨3, rfl⟩, ?_⟩
    change new.toNat * 48 + 8 ≤ 2 ^ 63; omega
  have hm48 : (48#64 : BitVec 64).toNat = 48 := rfl
  have ha8 : (8#64 : BitVec 64).toNat = 8 := rfl
  have hpre' : s0.mem ⊨ (finishGrowSpec A).pre hcall s0 ∗ R := by
    simp only [finishGrowSpec, hcall, FinishGrowCall.oldBuf, hcap, ite_false,
      memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [hm48, ha8, ← hbs, Nat.sub_self, memRegion_zero, sepConj_emp, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, Nat.le_refl _, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrowSpec, finishGrow48NeSpec, hcall, FinishGrowCall.oldBuf,
      hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    rw [hm48, ha8, ← hbs, Nat.sub_self, memRegion_zero, sepConj_emp] at hq
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * 48), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [show (out ↦₆₄ 1#64 ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 48) ∗
            (⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
              A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
            A.pool ∗ stackAt s0.sp finishGrowStack) ∗ R =
          ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
            ((A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs) ∗
              A.pool ∗ stackAt s0.sp finishGrowStack ∗
              out ↦₆₄ 1#64 ∗ (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 48)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hq.1.2, ?_⟩
      simpa only [sepConj_assoc] using hq.2
    · simp only [htag, ite_false] at hq ⊢
      rw [show (out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 48) ∗
            (⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
              A.live p' (new.toNat * 48) 8 ∗ (p' ↦ₛ bs) ∗
              memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 48 - bs.length)) ∗
            A.pool ∗ stackAt s0.sp finishGrowStack) ∗ R =
          ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
            ((A.live p' (new.toNat * 48) 8 ∗ (p' ↦ₛ bs) ∗
              memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 48 - bs.length) ∗
              A.pool ∗ stackAt s0.sp finishGrowStack ∗
              out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 48)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.2⟩, ?_⟩
      simpa only [sepConj_assoc] using hq.2
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

/-- Block `42`: `<alloc::raw_vec::RawVec<SignalProtocolError>>::grow_one` meets
`growOneSpeSpec A` under `[LibsignalPlacement]` given `finish_grow_placed_ok`. -/
theorem grow_one_spe_placed_ok_of_fg [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base (finishGrowSpec A))
    (h_panic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_42).rebase (blkPl_42).base H)
      (blkPl_42).base
      (withLsCodeLoaded lsmpl (growOneSpeSpec A)) := by
  simp only [withLsCodeLoaded, growOneSpeSpec, stackAt_grow_one_spe, sepExists_sepConj_right]
  have hpanic : ((blkPC_42).rebase (blkPl_42).base H).externAt?
      (lsρ lsHandleErrorSym) = some Rust.panicked :=
    (ls_externAt?_of_mem).trans h_panic
  have hfg0 : subroutine_ok ((blkPC_42).rebase (blkPl_42).base H) (lsmpl.base 45)
      (withLsCodeLoaded lsmpl (finishGrow48ZeroSpec A)) :=
    ls_subroutine_ok_of_block
      (subroutine_ok_withLsCodeLoaded_of_plain (finish_grow_48_zero_ok_gen hfg))
  have hfg1 : subroutine_ok ((blkPC_42).rebase (blkPl_42).base H) (lsmpl.base 45)
      (withLsCodeLoaded lsmpl (finishGrow48NeSpec A)) :=
    ls_subroutine_ok_of_block
      (subroutine_ok_withLsCodeLoaded_of_plain (finish_grow_48_ne_ok_gen hfg))
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hnew_eq := grow_spe_new_cap_eq (by omega)
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hnew_bound : new.toNat * 48 + 8 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero ‹bs.length = (0#64 : BitVec 64).toNat * 48›
    subst hbs
    simp only [BitVec.ofNat_eq_ofNat, ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_zero, Nat.mul_zero, Nat.sub_zero]
    apply SepWPp.of_sepWP (mid := (blkPl_42).base + 60#64)
    wp_steps_lscl (lsmpl.base 45)
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by first | rfl | assumption) (by first | rfl | assumption)
    refine SepWPp.ite_elim_pure1 (fun htag htrace => ?_) (fun _ ⟨hw0, hp', htrace⟩ => ?_)
    · subst htag
      apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun_sf)
      refine SepWPp.panic (by exact hrun_sf) hpanic fun hm => ?_
      exact allowPanic_panicked
        (allocFailedIn_of_eq (htrace : (Rust.panicked _).trace = s0.trace ++ [allocFailedEvent])) hm
    · subst hw0
      rw [sepConj_assoc]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · have hcap0' : cap ≠ 0 := hcap0
    simp only [hcap0', ite_false, sepConj_assoc]
    have hsub_mul : (max (2 * cap.toNat) 4 - cap.toNat) * 48 = new.toNat * 48 - bs.length := by
      rw [Nat.sub_mul, hnew_toNat, ‹bs.length = cap.toNat * 48›]
    rw [hsub_mul]
    apply SepWPp.of_sepWP (mid := (blkPl_42).base + 60#64)
    wp_steps_lscl (lsmpl.base 45)
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done hpc_sf hrun_sf
    refine SepWPp.ite_elim_pure2 (fun htag htrace => ?_) (fun _ ⟨hw0, hp', htrace⟩ => ?_)
    · subst htag
      rw [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun_sf)
      refine SepWPp.panic (by exact hrun_sf) hpanic fun hm => ?_
      rw [← sepConj_assoc]
      exact allowPanic_panicked
        (allocFailedIn_of_eq (htrace : (Rust.panicked _).trace = s0.trace ++ [allocFailedEvent])) hm
    · subst hw0
      rw [sepConj_assoc, sepConj_assoc]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

/-- Block `42`: `<alloc::raw_vec::RawVec<SignalProtocolError>>::grow_one` meets
`growOneSpeSpec A` under `[LibsignalPlacement]`. -/
theorem grow_one_spe_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_42).rebase (blkPl_42).base H)
      (blkPl_42).base
      (withLsCodeLoaded lsmpl (growOneSpeSpec A)) :=
  grow_one_spe_placed_ok_of_fg (finish_grow_placed_ok hshim halloc hrealloc) hpanic

private theorem finish_grow_104_zero_ok_gen_x {A : RustAlloc} {prog : Program} {entry : BitVec 64}
    (hfg : subroutine_ok prog entry (finishGrowSpecX A)) :
    subroutine_ok prog entry (finishGrow104ZeroSpecX A) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow104ZeroSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, 8#64, 104#64, []⟩
  have hlay : LayoutOk (new.toNat * (104#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 104; omega, ⟨3, rfl⟩, ?_⟩
    change new.toNat * 104 + 8 ≤ 2 ^ 63; omega
  have hpre' : s0.mem ⊨ (finishGrowSpecX A).pre hcall s0 ∗ R := by
    simp only [finishGrowSpecX, hcall, FinishGrowCall.oldBuf, ite_true,
      memRegion_24_cells, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrowSpecX, finishGrow104ZeroSpecX, hcall,
      FinishGrowCall.oldBuf, ite_true, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    have hm104 : (104#64 : BitVec 64).toNat = 104 := rfl
    have ha8 : (8#64 : BitVec 64).toNat = 8 := rfl
    rw [hm104, ha8] at hq
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * 104), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [show (out ↦₆₄ 1#64 ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104) ∗
            ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
            A.pool ∗ stackAt s0.sp finishGrowStackX) ∗ R =
          ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
            ((A.pool ∗ stackAt s0.sp finishGrowStackX ∗ out ↦₆₄ 1#64 ∗
              (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [show (out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104) ∗
            (⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
              A.live p' (new.toNat * 104) 8 ∗ memRegion p' (new.toNat * 104)) ∗
            A.pool ∗ stackAt s0.sp finishGrowStackX) ∗ R =
          ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
            ((A.live p' (new.toNat * 104) 8 ∗ memRegion p' (new.toNat * 104) ∗
              A.pool ∗ stackAt s0.sp finishGrowStackX ∗
              out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.2⟩, ?_⟩
      simpa only [sepConj_assoc] using hq.2
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

private theorem finish_grow_104_ne_ok_gen_x {A : RustAlloc} {prog : Program} {entry : BitVec 64}
    (hfg : subroutine_ok prog entry (finishGrowSpecX A)) :
    subroutine_ok prog entry (finishGrow104NeSpecX A) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [finishGrow104NeSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, 8#64, 104#64, bs⟩
  have hlay : LayoutOk (new.toNat * (104#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 104; omega, ⟨3, rfl⟩, ?_⟩
    change new.toNat * 104 + 8 ≤ 2 ^ 63; omega
  have hm104 : (104#64 : BitVec 64).toNat = 104 := rfl
  have ha8 : (8#64 : BitVec 64).toNat = 8 := rfl
  have hpre' : s0.mem ⊨ (finishGrowSpecX A).pre hcall s0 ∗ R := by
    simp only [finishGrowSpecX, hcall, FinishGrowCall.oldBuf, hcap,
      ite_false, memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [hm104, ha8, ← hbs, Nat.sub_self, memRegion_zero, sepConj_emp, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, Nat.le_refl _, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrowSpecX, finishGrow104NeSpecX, hcall,
      FinishGrowCall.oldBuf, hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    rw [hm104, ha8, ← hbs, Nat.sub_self, memRegion_zero, sepConj_emp] at hq
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * 104), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [show (out ↦₆₄ 1#64 ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104) ∗
            (⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
              A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
            A.pool ∗ stackAt s0.sp finishGrowStackX) ∗ R =
          ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
            ((A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs) ∗
              A.pool ∗ stackAt s0.sp finishGrowStackX ∗
              out ↦₆₄ 1#64 ∗ (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hq.1.2, ?_⟩
      simpa only [sepConj_assoc] using hq.2
    · simp only [htag, ite_false] at hq ⊢
      rw [show (out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
            (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104) ∗
            (⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
              A.live p' (new.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
              memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 104 - bs.length)) ∗
            A.pool ∗ stackAt s0.sp finishGrowStackX) ∗ R =
          ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
            ((A.live p' (new.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
              memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 104 - bs.length) ∗
              A.pool ∗ stackAt s0.sp finishGrowStackX ∗
              out ↦₆₄ tag ∗ (out + 8#64) ↦₆₄ p' ∗
              (out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * 104)) ∗ R) by ac_rfl,
        satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.2⟩, ?_⟩
      simpa only [sepConj_assoc] using hq.2
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

/-- Block `43`: `<alloc::raw_vec::RawVec<Chain>>::grow_one` meets
`growOne104SpecX A` under `[LibsignalPlacement]` given `finish_grow_placed_ok_x`. -/
theorem grow_one_104_placed_ok_of_fg_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (blkPl_45).base (finishGrowSpecX A))
    (h_panic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H)
      (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOne104SpecX A)) := by
  simp only [withLsCodeLoaded, growOne104SpecX, stackAt_grow_one_104_x, sepExists_sepConj_right]
  have hpanic : ((blkPC_43).rebase (blkPl_43).base H).externAt?
      (lsρ lsHandleErrorSym) = some Rust.panicked :=
    (ls_externAt?_of_mem).trans h_panic
  have hfg0 : subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (lsmpl.base 45)
      (withLsCodeLoaded lsmpl (finishGrow104ZeroSpecX A)) :=
    ls_subroutine_ok_of_block
      (subroutine_ok_withLsCodeLoaded_of_plain (finish_grow_104_zero_ok_gen_x hfg))
  have hfg1 : subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (lsmpl.base 45)
      (withLsCodeLoaded lsmpl (finishGrow104NeSpecX A)) :=
    ls_subroutine_ok_of_block
      (subroutine_ok_withLsCodeLoaded_of_plain (finish_grow_104_ne_ok_gen_x hfg))
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hnew_eq := grow_104_new_cap_eq (by omega)
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hnew_bound : new.toNat * 104 + 8 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero ‹bs.length = (0#64 : BitVec 64).toNat * 104›
    subst hbs
    simp only [BitVec.ofNat_eq_ofNat, ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, BitVec.toNat_zero, Nat.mul_zero, Nat.sub_zero]
    apply SepWPp.of_sepWP (mid := (blkPl_43).base + 60#64)
    wp_steps_lscl (lsmpl.base 45)
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by first | rfl | assumption) (by first | rfl | assumption)
    refine SepWPp.ite_elim_pure1 (fun htag htrace => ?_) (fun _ ⟨hw0, hp', htrace⟩ => ?_)
    · subst htag
      apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun_sf)
      refine SepWPp.panic (by exact hrun_sf) hpanic fun hm => ?_
      exact allowPanic_panicked
        (allocFailedIn_of_eq (htrace : (Rust.panicked _).trace = s0.trace ++ [allocFailedEvent])) hm
    · subst hw0
      rw [sepConj_assoc]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · have hcap0' : cap ≠ 0 := hcap0
    simp only [hcap0', ite_false, sepConj_assoc]
    have hsub_mul : (max (2 * cap.toNat) 4 - cap.toNat) * 104 = new.toNat * 104 - bs.length := by
      rw [Nat.sub_mul, hnew_toNat, ‹bs.length = cap.toNat * 104›]
    rw [hsub_mul]
    apply SepWPp.of_sepWP (mid := (blkPl_43).base + 60#64)
    wp_steps_lscl (lsmpl.base 45)
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done hpc_sf hrun_sf
    refine SepWPp.ite_elim_pure2 (fun htag htrace => ?_) (fun _ ⟨hw0, hp', htrace⟩ => ?_)
    · subst htag
      rw [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun_sf)
      refine SepWPp.panic (by exact hrun_sf) hpanic fun hm => ?_
      rw [← sepConj_assoc]
      exact allowPanic_panicked
        (allocFailedIn_of_eq (htrace : (Rust.panicked _).trace = s0.trace ++ [allocFailedEvent])) hm
    · subst hw0
      rw [sepConj_assoc, sepConj_assoc]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

/-- Block `43`: `<alloc::raw_vec::RawVec<Chain>>::grow_one` meets
`growOne104SpecX A` under `[LibsignalPlacement]`. -/
theorem grow_one_104_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H)
      (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOne104SpecX A)) :=
  grow_one_104_placed_ok_of_fg_x (finish_grow_placed_ok_x hshim halloc hrealloc) hpanic

end CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
