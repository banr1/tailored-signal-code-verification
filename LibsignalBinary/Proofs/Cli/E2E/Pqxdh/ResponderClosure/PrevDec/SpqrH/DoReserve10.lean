/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.ShardFill.HandshakeProstDecode
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Handshake `finish_grow [local#11]` and `do_reserve_and_handle [local#10]`

Verifies the 1-byte-element (`stride = 1, align = 1`) handshake subroutines
`<RawVecInner>::finish_grow [local#11]` (`168` B) and
`<RawVecInner>::reserve::do_reserve_and_handle [local#10]` (`120` B) on `tripleRatchetProgAtExt`
under `AllocContractsX`, using wrapping 64-bit relative call offsets (`fnAddr_rel64`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.HMAC
open CryptoGames.LibsignalSession CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Direction-agnostic 64-bit wrapping relative call-target address lemma for `libsignalSessionCode`. -/
theorem fnAddr_rel64 {b : BitVec 64} {H : String → Option (State → State)}
    {caller callee : String} {o1 o2 : Nat} {rel : BitVec 64}
    (h1 : libsignalSessionCode.fnOff caller = o1)
    (h2 : libsignalSessionCode.fnOff callee = o2)
    (hrel : BitVec.ofNat 64 o1 + rel = BitVec.ofNat 64 o2) :
    (libsignalSessionCode.rebase b H).fnAddr caller + rel =
      (libsignalSessionCode.rebase b H).fnAddr callee := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, h1, h2, BitVec.add_assoc, hrel]

namespace ReserveNorm

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

end ReserveNorm

open ReserveNorm

/-! ## Symbol names and stack budgets -/

/-- `<alloc::raw_vec::RawVecInner>::finish_grow [local#11]` (`168` B, `stride = 1, align = 1`). -/
abbrev finishGrow11Name : String :=
  "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]"

/-- `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#10]`
(`120` B, `stride = 1, align = 1`, calling `finish_grow [local#11]`). -/
abbrev doReserve10Name : String :=
  "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#8]"

/-- Stack budget of 32-byte-frame `finish_grow` instances: `extHookStack + 32` (`16416` B). -/
abbrev finishGrow32Stack : Nat := extHookStack + 32

/-- Stack budget of 32-byte-frame `do_reserve_and_handle` instances: `finishGrow32Stack + 64` (`16480` B). -/
abbrev doReserve32Stack : Nat := finishGrow32Stack + 64

/-! ## Arithmetic and memory helpers -/

private theorem getLsbD_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new.getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem getElem_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new[63] = false := by
  rw [BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem beq_zero_eq_false {new : BitVec 64} (h0 : 0 < new.toNat) :
    (new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  change new.toNat = 0 at ht
  omega

theorem memRegion_24 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, ProofLib.memRegion_split a 8 (8 + 8) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_finishGrow32 (sp : BitVec 64) :
    stackAt sp finishGrow32Stack =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp 16384 4 (by decide)

theorem stackAt_doReserve32 (sp : BitVec 64) :
    stackAt sp doReserve32Stack =
      stackAt (sp - 64#64) finishGrow32Stack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_cells sp 16416 8 (by decide)
  change stackAt sp doReserve32Stack =
    stackAt (sp - 64#64) finishGrow32Stack ∗ cells (sp - 64#64) 8 at h1
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

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

/-! ## 1. `<alloc::raw_vec::RawVecInner>::finish_grow [local#11]` -/

/-- Ghost of a 1-byte-element `finish_grow` call (`[local#11]`). -/
structure FinishGrow1Call where
  out : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  new : BitVec 64
  bs : List (BitVec 8)

/-- The heap buffer of a `RawVecInner` with `stride = 1, align = 1` before `finish_grow`. -/
def FinishGrow1Call.oldBuf (A : RustAlloc) (x : FinishGrow1Call) : SepProp :=
  if x.cap = 0#64 then emp
  else
    A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)

/-- Contract of 1-byte-element `finish_grow` (`stride = 1, align = 1`, 32-byte frame). -/
def finishGrow1Spec (A : RustAlloc) : Spec FinishGrow1Call where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧
      (x.cap = 0#64 → x.bs = []) ∧ x.bs.length ≤ x.cap.toNat ∧
      x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
    memRegion x.out 24 ∗ x.oldBuf A ∗ A.pool ∗ stackAt s.sp finishGrow32Stack
  post := fun x s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64,
      (x.out ↦₆₄ tag) ∗ ((x.out + 8#64) ↦₆₄ p') ∗
      ((x.out + 16#64) ↦₆₄ x.new) ∗
      (if tag = 1#64 then
        ⌜p' = 1#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗ x.oldBuf A
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' x.new.toNat 1 ∗ (p' ↦ₛ x.bs) ∗
          memRegion (p' + BitVec.ofNat 64 x.bs.length) (x.new.toNat - x.bs.length)) ∗
      A.pool ∗ stackAt s0.sp finishGrow32Stack

private def finishGrow1AllocSpec (A : RustAlloc) : Spec FinishGrow1Call :=
  { finishGrow1Spec A with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp finishGrow32Stack }

private def finishGrow1ReallocSpec (A : RustAlloc) : Spec FinishGrow1Call :=
  { finishGrow1Spec A with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length) ∗
      A.pool ∗ stackAt s.sp finishGrow32Stack }

private theorem finish_grow_11_zero_ok_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrow11Name)
      ((finishGrow1AllocSpec A).inImage img) := by
  unfold Spec.inImage finishGrow1AllocSpec finishGrow1Spec
  simp only [memRegion_24, stackAt_finishGrow32, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff finishGrow11Name =
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]" :=
    ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]"
  have hshim := shim_ok_at2_ext_x hA (name := finishGrow11Name)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_norm_ext_x hA (name := finishGrow11Name)
    (k := num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  code_fetches CryptoVerification.libsignalSessionCode finishGrow11 img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]")) 168
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  subst cap
  subst bs
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcbz := beq_zero_eq_false hnew_pos
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk new.toNat 1 := ⟨hnew_pos, hpow, hnew_bound⟩
  apply SepWP.seq_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]")) hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  have ⟨hF1, hsym1⟩ := hinv1
  apply SepWP.seq_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]")) hinv1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  rintro ⟨hF2, hsym2⟩
  wp_call halloc (new.toNat, 1)
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf]
    wp_done

private theorem finish_grow_11_ne_ok_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrow11Name)
      ((finishGrow1ReallocSpec A).inImage img) := by
  unfold Spec.inImage finishGrow1ReallocSpec finishGrow1Spec
  simp only [memRegion_24, stackAt_finishGrow32, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff finishGrow11Name =
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]" :=
    ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]"
  have hrealloc := realloc_ok_at_norm_ext_x hA (name := finishGrow11Name)
    (k := num% (ls_off% "__rustc::__rust_realloc" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_realloc")])
  code_fetches CryptoVerification.libsignalSessionCode finishGrow11 img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]")) 168
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hle_new : bs.length ≤ new.toNat := by omega
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay_old : LayoutOk cap.toNat 1 := ⟨hcap_pos, hpow, by omega⟩
  have hlay : LayoutOk new.toNat 1 := ⟨hnew_pos, hpow, hnew_bound⟩
  apply SepWP.seq_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_realloc" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]")) hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  rintro ⟨hF1, hsym1⟩
  wp_call hrealloc (ptr, cap.toNat, 1, new.toNat, bs)
  wp_steps
  wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf, hcap_ne, ite_false]
    wp_done

/-- `<alloc::raw_vec::RawVecInner>::finish_grow [local#11]` meets `(finishGrow1Spec A).inImage img`
on `tripleRatchetProgAtExt img.base ext` under `AllocContractsX`. -/
theorem finish_grow_11_ok_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrow11Name)
      ((finishGrow1Spec A).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_11_zero_ok_ext hA).mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [Spec.inImage, finishGrow1Spec, finishGrow1AllocSpec, FinishGrow1Call.oldBuf,
      hcap0, ite_true, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hbs0, _, hle, hnew, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, trivial, hbs0 trivial, hle, hnew, hlay⟩, hmem⟩
  · refine (finish_grow_11_ne_ok_ext hA).mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [Spec.inImage, finishGrow1Spec, finishGrow1ReallocSpec, FinishGrow1Call.oldBuf,
      hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, _, hbs, hle, hnew, hlay⟩, hmem⟩
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hcap0, hbs, hle, hnew, hlay⟩, hmem⟩

/-! ## Cell-unfolded `finish_grow` wrappers -/

abbrev FG24Ghost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

def finishGrow24ZeroCellsSpec (A : RustAlloc) : Spec FG24Ghost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧
      cap.toNat ≤ new.toNat ∧ 0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ stackAt fsp finishGrow32Stack
  post := fun (out, _cap, _ptr, new, _bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' new.toNat 1 ∗ memRegion p' new.toNat) ∗
      A.pool ∗ stackAt fsp finishGrow32Stack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

theorem finish_grow_24_zero_cells_of_spec {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {name : String}
    (hfg : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name) ((finishGrow1Spec A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name)
      ((finishGrow24ZeroCellsSpec A).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, finishGrow24ZeroCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hfsp, hcap0, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrow1Call := ⟨out, 0#64, ptr, new, []⟩
  have hpre' : s0.mem ⊨ ((finishGrow1Spec A).inImage img).pre hcall s0 ∗ R := by
    simp only [Spec.inImage, finishGrow1Spec, hcall, FinishGrow1Call.oldBuf, ite_true,
      memRegion_24, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, fun _ => trivial, Nat.zero_le _, hle, hpos, hbound⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, finishGrow1Spec, finishGrow24ZeroCellsSpec, hcall, FinishGrow1Call.oldBuf,
      ite_true, pointsToBytes_nil, List.length_nil,
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

def finishGrow24NeCellsSpec (A : RustAlloc) : Spec FG24Ghost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.sp = fsp ∧ cap ≠ 0#64 ∧
      bs.length ≤ cap.toNat ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
    A.pool ∗ stackAt fsp finishGrow32Stack
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
      A.pool ∗ stackAt fsp finishGrow32Stack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

theorem finish_grow_24_ne_cells_of_spec {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {name : String}
    (hfg : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name) ((finishGrow1Spec A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name)
      ((finishGrow24NeCellsSpec A).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, finishGrow24NeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hfsp, hcap, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrow1Call := ⟨out, cap, ptr, new, bs⟩
  have hpre' : s0.mem ⊨ ((finishGrow1Spec A).inImage img).pre hcall s0 ∗ R := by
    simp only [Spec.inImage, finishGrow1Spec, hcall, FinishGrow1Call.oldBuf, hcap, ite_false,
      memRegion_24, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, False.elim, hbs, hle, hpos, hbound⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine hfg.mono_outcome hcall R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, finishGrow1Spec, finishGrow24NeCellsSpec, hcall, FinishGrow1Call.oldBuf,
      hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
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

/-! ## 2. `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#10]` -/

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
    A.pool ∗ stackAt s.sp doReserveStackX
  post := fun x s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗ (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' newCap 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (newCap - x.bs.length)) ∗
    A.pool ∗ stackAt s0.sp doReserveStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `do_reserve_and_handle [local#10]` meets `(doReserve1Raw32Spec A).inImage img`
on `tripleRatchetProgAtExt img.base ext` under `AllocContractsX`. -/
theorem do_reserve_10_raw32_ok_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve10Name)
      ((doReserve1Raw32Spec A).inImage img) := by
  unfold Spec.inImage
  simp only [doReserve1Raw32Spec, stackAt_doReserve32, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff doReserve10Name =
      ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#8]" :=
    ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#8]"
  have hfn_fg11 : libsignalSessionCode.fnOff finishGrow11Name =
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]" :=
    ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]"
  have hpanic := panic_at_handle_error_norm_ext (b := img.base) (ext := ext)
    (name := doReserve10Name)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" -
      ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#8]"))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := finish_grow_24_zero_cells_of_spec (finish_grow_11_ok_ext hA)
  have hfg1 := finish_grow_24_ne_cells_of_spec (finish_grow_11_ok_ext hA)
  have hrel_fg11 :
      (tripleRatchetProgAtExt img.base ext).fnAddr doReserve10Name +
        bv% ((2 ^ 64 + ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]" -
          ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#8]") % 2 ^ 64) =
      (tripleRatchetProgAtExt img.base ext).fnAddr finishGrow11Name :=
    fnAddr_rel64 hfn hfn_fg11 (by decide)
  rw [← hrel_fg11] at hfg0 hfg1
  clear hrel_fg11
  code_fetches CryptoVerification.libsignalSessionCode doReserve10 img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#8]")) 120
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢
  clear hfn hfn_fg11 hA
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr doReserve10Name = entry
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, additional⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
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
    apply SepWPp.of_sepWP (mid := entry + bv% (68))
    apply SepWP.seq_inImage
      (mid := entry + bv% ((2 ^ 64 + ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]" -
        ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#8]") % 2 ^ 64))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF1, hsym1⟩
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" -
          ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#8]"))
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
    apply SepWPp.of_sepWP (mid := entry + bv% (68))
    apply SepWP.seq_inImage
      (mid := entry + bv% ((2 ^ 64 + ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]" -
        ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#8]") % 2 ^ 64))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF1, hsym1⟩
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" -
          ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#8]"))
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

private theorem stackAt_doReserve_eq_32 (sp : BitVec 64) :
    stackAt sp doReserveStackX =
      memRegion (sp - 16496#64) 16 ∗ stackAt sp doReserve32Stack :=
  ProofLib.stackAt_split_bottom sp 16480 16 (by decide)

private theorem do_reserve_raw1_of_raw32 {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {name : String}
    (h32 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name) ((doReserve1Raw32Spec A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name)
      ((doReserve1RawSpec A).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, doReserve1RawSpec, stackAt_doReserve_eq_32, sepConj_assoc] at hpre
  have hpre' : s0.mem ⊨ ((doReserve1Raw32Spec A).inImage img).pre x s0 ∗
      (memRegion (s0.sp - 16496#64) 16 ∗ R) := by
    simp only [Spec.inImage, doReserve1Raw32Spec, sepConj_assoc]
    exact (by ac_rfl :
      (⌜ImgCallInv img s0⌝ ∗
        ⌜s0.readReg64 Reg.x0 = x.v ∧ (s0.readReg64 Reg.x1).toNat = x.bs.length ∧
          (s0.readReg64 Reg.x2).toNat = x.additional ∧ x.bs.length ≤ x.cap.toNat ∧
          x.ptr ≠ 0#64 ∧ reserveCap x.cap.toNat x.bs.length x.additional + 1 ≤ 2 ^ 63⌝ ∗
        x.v ↦₆₄ x.cap ∗ (x.v + 8#64) ↦₆₄ x.ptr ∗
        (if x.cap = 0#64 then emp
         else A.live x.ptr x.cap.toNat 1 ∗ x.ptr ↦ₛ x.bs ∗
           memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
        A.pool ∗ memRegion (s0.sp - 16496#64) 16 ∗ stackAt s0.sp doReserve32Stack ∗ R) =
      (⌜ImgCallInv img s0⌝ ∗
        ⌜s0.readReg64 Reg.x0 = x.v ∧ (s0.readReg64 Reg.x1).toNat = x.bs.length ∧
          (s0.readReg64 Reg.x2).toNat = x.additional ∧ x.bs.length ≤ x.cap.toNat ∧
          x.ptr ≠ 0#64 ∧ reserveCap x.cap.toNat x.bs.length x.additional + 1 ≤ 2 ^ 63⌝ ∗
        x.v ↦₆₄ x.cap ∗ (x.v + 8#64) ↦₆₄ x.ptr ∗
        (if x.cap = 0#64 then emp
         else A.live x.ptr x.cap.toNat 1 ∗ x.ptr ↦ₛ x.bs ∗
           memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
        A.pool ∗ stackAt s0.sp doReserve32Stack ∗ memRegion (s0.sp - 16496#64) 16 ∗ R)) ▸ hpre
  refine h32.mono_outcome x (memRegion (s0.sp - 16496#64) 16 ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, doReserve1Raw32Spec, doReserve1RawSpec, stackAt_doReserve_eq_32, sepConj_assoc] at hq ⊢
    exact (by ac_rfl :
      (⌜sf.trace = s0.trace⌝ ∗
        (∃∗ p', ⌜p' ≠ 0#64⌝ ∗
          x.v ↦₆₄ BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ∗
          (x.v + 8#64) ↦₆₄ p' ∗
          A.live p' (reserveCap x.cap.toNat x.bs.length x.additional) 1 ∗
          p' ↦ₛ x.bs ∗
          memRegion (p' + BitVec.ofNat 64 x.bs.length)
            (reserveCap x.cap.toNat x.bs.length x.additional - x.bs.length)) ∗
        A.pool ∗ stackAt s0.sp doReserve32Stack ∗ memRegion (s0.sp - 16496#64) 16 ∗ R) =
      (⌜sf.trace = s0.trace⌝ ∗
        (∃∗ p', ⌜p' ≠ 0#64⌝ ∗
          x.v ↦₆₄ BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ∗
          (x.v + 8#64) ↦₆₄ p' ∗
          A.live p' (reserveCap x.cap.toNat x.bs.length x.additional) 1 ∗
          p' ↦ₛ x.bs ∗
          memRegion (p' + BitVec.ofNat 64 x.bs.length)
            (reserveCap x.cap.toNat x.bs.length x.additional - x.bs.length)) ∗
        A.pool ∗ memRegion (s0.sp - 16496#64) 16 ∗ stackAt s0.sp doReserve32Stack ∗ R)) ▸ hq
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, doReserve1Raw32Spec, doReserve1RawSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

private theorem do_reserve_raw_of_raw1 {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {name : String}
    (h1 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name) ((doReserve1RawSpec A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name)
      ((doReserveRawSpecX A).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, doReserveRawSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, _, _, hlen, hptr, hbound⟩, hmem⟩
  have hpre' : s0.mem ⊨ ((doReserve1RawSpec A).inImage img).pre x s0 ∗ R := by
    simp only [Spec.inImage, doReserve1RawSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hlen, hptr, hbound⟩, hmem⟩
  exact h1.mono_outcome x R s0 hpc hrun hpre' hsp fun _ hout => hout

private theorem vecU8At_eq (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  ac_rfl

private theorem do_reserve_vec_of_raw {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {name : String}
    (hraw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name) ((doReserveRawSpecX A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name)
      ((doReserveSpecX A).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, doReserveSpecX, vecU8At_eq, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ⟨hlen, hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ ((doReserveRawSpecX A).inImage img).pre x s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [Spec.inImage, doReserveRawSpecX, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound⟩, ?_⟩
    rwa [doReserve_pre_repack]
  refine hraw.mono_outcome x
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, doReserveRawSpecX, doReserveSpecX, vecU8At_eq] at hq ⊢
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
    dsimp only [Spec.inImage, doReserveRawSpecX, doReserveSpecX] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

/-- Vec wrapper around `doReserve1RawSpec`: contract of 3-argument `do_reserve_and_handle`
(`stride = 1, align = 1` hardcoded, so `x3` and `x4` are unconstrained) at `doReserveStackX`. -/
def doReserve1VecSpecX (A : RustAlloc) : Spec DoReserveCall where
  pre := fun x s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧
      newCap + 1 ≤ 2 ^ 63⌝ ∗
    vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp doReserveStackX
  post := (doReserveSpecX A).post
  onPanic := (doReserveSpecX A).onPanic

/-- Contract statement for `do_reserve_and_handle [local#10]` (`(doReserveSpecX A).inImage img`). -/
def DoReserve10OkExtX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve10Name)
    ((doReserveSpecX A).inImage img)

/-- Contract statement for `do_reserve_and_handle [local#10]` (`(doReserve1VecSpecX A).inImage img`,
3-argument `Vec<u8>` wrapper with `x3, x4` unconstrained). -/
def DoReserve10VecOkExtX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve10Name)
    ((doReserve1VecSpecX A).inImage img)

theorem do_reserve_vec1_of_raw1 {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {name : String}
    (hraw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name) ((doReserve1RawSpec A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name)
      ((doReserve1VecSpecX A).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, doReserve1VecSpecX, vecU8At_eq, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hbound⟩, ⟨hlen, hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ ((doReserve1RawSpec A).inImage img).pre x s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [Spec.inImage, doReserve1RawSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ⟨hx0, hx1, hx2, hlen, hptr, hbound⟩, ?_⟩
    rwa [doReserve_pre_repack]
  refine hraw.mono_outcome x
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, doReserve1RawSpec, doReserve1VecSpecX, doReserveSpecX, vecU8At_eq] at hq ⊢
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
    dsimp only [Spec.inImage, doReserve1RawSpec, doReserve1VecSpecX, doReserveSpecX] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

theorem do_reserve_10_raw1_ok_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve10Name)
      ((doReserve1RawSpec A).inImage img) :=
  do_reserve_raw1_of_raw32 (do_reserve_10_raw32_ok_ext hA)

theorem do_reserve_10_vec_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    DoReserve10VecOkExtX img A ext :=
  do_reserve_vec1_of_raw1 (do_reserve_10_raw1_ok_ext hA)

theorem do_reserve_10_raw_ok_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve10Name)
      ((doReserveRawSpecX A).inImage img) :=
  do_reserve_raw_of_raw1 (do_reserve_10_raw1_ok_ext hA)

theorem do_reserve_10_ok_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve10Name)
      ((doReserveSpecX A).inImage img) :=
  do_reserve_vec_of_raw (do_reserve_10_raw_ok_ext hA)

theorem do_reserve_10_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    DoReserve10OkExtX img A ext :=
  do_reserve_10_ok_ext hA

/-- Top-level handshake contract theorem for `do_reserve_and_handle [local#10]`. -/
theorem doReserve10_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    DoReserve10OkExtX img A ext :=
  do_reserve_10_ok_ext_x hA

/-- `LibsignalTripleRatchet.AllocContractsX` gives `Proofs.libsignal.Stage1X.AllocContractsX`
(for `growOneMessageKey_ok_ext_x` in `ArmChainRecv` and `Chain3Callees`). -/
theorem c3_stage1Alloc_of_allocContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hAlloc : AllocContractsX img A ext) :
    Proofs.libsignal.Stage1X.AllocContractsX img A ext where
  alloc := subroutine_ok_mono_entails hAlloc.alloc
    (fun ⟨_, _⟩ _ => Entails.refl _)
    (fun ⟨_, _⟩ _ _ => Entails.of_eq (by
      dsimp only [Spec.inImage, rustAllocSpecWithStack,
        Proofs.libsignal.Stage1X.rustAllocSpecWithStack]
      ac_rfl))
  dealloc := subroutine_ok_mono_entails hAlloc.dealloc
    (fun ⟨_, _, _⟩ _ => Entails.of_eq (by
      dsimp only [Spec.inImage, rustDeallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack]
      ac_rfl))
    (fun ⟨_, _, _⟩ _ _ => Entails.refl _)
  realloc := subroutine_ok_mono hAlloc.realloc
    (fun ⟨_, _, _, _, _⟩ _ _ h => by
      dsimp only [Spec.inImage, rustReallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      obtain ⟨hinv, h⟩ := h
      refine ⟨hinv, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      obtain ⟨⟨hx0, hx1, hx2, hx3, hb1, hb2, hl1, hl2⟩, h⟩ := h
      refine ⟨⟨hx0, hx1, hx2, hx3, hl1, hl2, hb1, hb2⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h)
    (fun ⟨_, _, _, _, _⟩ _ _ _ h => by
      dsimp only [Spec.inImage, rustReallocExternSpecWithStack, rustReallocSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocSpecWithStack] at h ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h)
  shim := hAlloc.shim extHookStack (by decide) (by decide)
  session_memmove := hAlloc.session_memmove extHookStack (by decide) (by decide)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

export SpqrH (
  fnAddr_rel64
  finishGrow11Name
  doReserve10Name
  finishGrow32Stack
  doReserve32Stack
  FinishGrow1Call
  finishGrow1Spec
  doReserve1Raw32Spec
  doReserve1RawSpec
  doReserve1VecSpecX
  DoReserve10OkExtX
  DoReserve10VecOkExtX
  finish_grow_11_ok_ext
  do_reserve_vec1_of_raw1
  do_reserve_10_raw32_ok_ext
  do_reserve_10_raw1_ok_ext
  do_reserve_10_vec_ok_ext_x
  do_reserve_10_raw_ok_ext
  do_reserve_10_ok_ext
  do_reserve_10_ok_ext_x
  doReserve10_ok
  c3_stage1Alloc_of_allocContractsX
)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
