/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbLoop
public import LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPt
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyDecoder>::into_pb`: Outer Loop

**Checked by Lean.**

Proves per-slot `Vec<u8>` allocation + serialization (`+148..+300`) and the 16-slot outer loop
(`+148..+328`), at fixed base (`0x63030`) and on Block `377`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop (vecPtOf vecPtListOf
  sortedSetPtListOf_eq_vecPtListOf)
open CryptoVerification.CodeLayout
open CryptoGames.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local arm64_norm, local wp_norm]
  fp64_sub_24 fp64_sub_16 fp64_sub_8
  fp64_sub_24_int fp64_sub_16_int fp64_sub_8_int
  sp_add_40_add_8
  ofNat_add_one madd_24_eq

section Legacy

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

local macro "into_pb_fetches_range " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode spqrDecoderIntoPbBin $b $H libsignalSessionCode_fnOff_0x5dc38 0x5dc38 $k0 $len)

/-! ## `vecPtOf` and `vecU8Buf` Unfolding / Reassembly Lemmas -/

/-- Remaining buffer and allocator block of a `Vec<Pt>` after splitting out `arrayAt ptAt 4 ptr pts`. -/
def vecPtTail (A : RustAlloc) (cap ptr : BitVec 64) (len : Nat) : SepProp :=
  ⌜len ≤ cap.toNat ∧ cap.toNat * 4 < 2 ^ 63 ∧ len * 4 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr (cap.toNat * 4) 2 ∗
       memRegion (ptr + BitVec.ofNat 64 (len * 4)) ((cap.toNat - len) * 4))

theorem vecPtOf_expose (A : RustAlloc) (v : BitVec 64) (pts : List Pt) :
    vecPtOf A v pts ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜4 * pts.length < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
          arrayAt ptAt 4 ptr pts ∗
          vecPtTail A cap ptr pts.length := by
  unfold vecPtOf vecOf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  refine Entails.trans (DropGlueFacts.vecAt_expose_loop A 4 2 ptAt v cap ptr pts) ?_
  unfold vecPtTail
  apply Entails.pure_left; rintro ⟨hle, hcap, hxs, hptr⟩
  have hlen : 4 * pts.length < 2 ^ 63 := by omega
  have heq :
      (⌜4 * pts.length < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
        arrayAt ptAt 4 ptr pts ∗
        (⌜pts.length ≤ cap.toNat ∧ cap.toNat * 4 < 2 ^ 63 ∧ pts.length * 4 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 4) 2 ∗
             memRegion (ptr + BitVec.ofNat 64 (pts.length * 4)) ((cap.toNat - pts.length) * 4)))) =
      (⌜4 * pts.length < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ⌜pts.length ≤ cap.toNat ∧ cap.toNat * 4 < 2 ^ 63 ∧ pts.length * 4 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
          arrayAt ptAt 4 ptr pts ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 4) 2 ∗
             memRegion (ptr + BitVec.ofNat 64 (pts.length * 4)) ((cap.toNat - pts.length) * 4)))) := by
    ac_rfl
  rw [heq]
  exact Entails.pure_right ⟨hlen, hptr⟩ (Entails.pure_right ⟨hle, hcap, hxs, hptr⟩ (Entails.refl _))

theorem vecPtOf_intro (A : RustAlloc) (v cap ptr : BitVec 64) (pts : List Pt) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
      arrayAt ptAt 4 ptr pts ∗
      vecPtTail A cap ptr pts.length) ⊢
    vecPtOf A v pts := by
  unfold vecPtOf vecOf
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  unfold vecAt vecHeader vecBuf vecPtTail ptStride ptAlign
  rw [show (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
      arrayAt ptAt 4 ptr pts ∗
      (⌜pts.length ≤ cap.toNat ∧ cap.toNat * 4 < 2 ^ 63 ∧ pts.length * 4 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 4) 2 ∗
           memRegion (ptr + BitVec.ofNat 64 (pts.length * 4)) ((cap.toNat - pts.length) * 4))) =
    ⌜pts.length ≤ cap.toNat ∧ cap.toNat * 4 < 2 ^ 63 ∧ pts.length * 4 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 pts.length)) ∗
        (arrayAt ptAt 4 ptr pts ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 4) 2 ∗
             memRegion (ptr + BitVec.ofNat 64 (pts.length * 4)) ((cap.toNat - pts.length) * 4)))) by
    ac_rfl]
  apply Entails.pure_left; rintro ⟨hle, hcap, _, hptr⟩
  apply sepConj_mono_right
  apply Entails.pure_right ⟨hle, hcap, hptr⟩
  by_cases hc : cap = 0
  · subst hc
    have hnil : pts = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hnil
    simp [arrayAt_nil]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem vecU8Buf_nil_intro (A : RustAlloc) (Rest : SepProp) :
    Rest ⊢ vecU8Buf A 0#64 1#64 [] ∗ Rest := by
  unfold vecU8Buf
  have hp : ([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0 := by decide
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [h0, ↓reduceIte, sepConj_emp]
  exact Entails.pure_right hp (Entails.refl _)

theorem vecU8Buf_of_exact_alloc (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen_pos : 0 < bs.length) (hlen_bound : bs.length < 2 ^ 63) (hptr : ptr ≠ 0) :
    ((ptr ↦ₛ bs) ∗ A.live ptr bs.length 1) ⊢
      vecU8Buf A (BitVec.ofNat 64 bs.length) ptr bs := by
  unfold vecU8Buf
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [htoNat] at ht
    change bs.length = 0 at ht
    omega
  have hp : bs.length ≤ (BitVec.ofNat 64 bs.length).toNat ∧
      (BitVec.ofNat 64 bs.length).toNat < 2 ^ 63 ∧ ptr ≠ 0 := by
    refine ⟨by omega, by omega, hptr⟩
  have hite :
      (if BitVec.ofNat 64 bs.length = 0 then emp
       else A.live ptr (BitVec.ofNat 64 bs.length).toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) ((BitVec.ofNat 64 bs.length).toNat - bs.length)) =
      (A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs)) := by
    simp only [hne0, ↓reduceIte, htoNat, Nat.sub_self, memRegion_zero, sepConj_emp]
  rw [hite]
  exact Entails.pure_right hp (Entails.of_eq (by ac_rfl))

theorem shiftLeft_two_eq_mul_four {n : Nat} (h : 4 * n < 2 ^ 63) :
    (BitVec.ofNat 64 n) <<< 2 = BitVec.ofNat 64 (4 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  omega

theorem ofNat_beq_zero_false {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

/-! ## `SepWPp` Sequencing and Pure Extraction Helpers -/

theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

theorem SepWPp.seq_clean {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_mid : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_mid sm →
      SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hq))

structure HiddenEq {α : Type} (a b : α) : Prop where
  eq : a = b

@[irreducible] noncomputable def intoPbEntry (b : BitVec 64) (ext : String → Option (State → State)) : BitVec 64 :=
  (tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName

theorem intoPbEntry_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    intoPbEntry b ext = (tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName := by
  unfold intoPbEntry; rfl

theorem intoPbEntry_raw_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder>::into_pb" = intoPbEntry b ext := by
  unfold intoPbEntry; rfl

/-! ## `pts` Outer Loop Iteration (`+148 -> +300 -> +148/+328`) -/

/-- Allocate and serialize one `SortedSet<Pt>` element (`+148 -> +300`, or OOM panic via `+384`). -/
theorem pts_outer_alloc_and_copy {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName +
        bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5dc38))
      sessionShimSpec)
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName +
        bv% (ls_off% "__rustc::__rust_alloc" - 0x5dc38))
      (rustAllocSpec A))
    {Q : State → SepProp → Prop} {R : SepProp}
    (s0 : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j : Nat) (pts : List Pt)
    (v40 v48 v56 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName + 148#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 64#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 j)
    (hx23 : s.readReg64 .x23 = 24#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (sm : State) (cap_c ptr_c : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName + 300#64 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.readReg64 .x29 = fsp + 64#64 →
      sm.readReg64 .x19 = s0.readReg64 .x19 →
      sm.readReg64 .x20 = s0.readReg64 .x20 →
      sm.readReg64 .x22 = BitVec.ofNat 64 j →
      sm.readReg64 .x23 = 24#64 →
      sm.readReg64 .x24 = 1#64 →
      sm.readReg64 .x28 = s0.readReg64 .x28 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        (((fsp + 40#64) ↦₆₄ cap_c) ∗
          ((fsp + 48#64) ↦₆₄ ptr_c) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (serializePtList pts).length) ∗
          vecU8Buf A cap_c ptr_c (serializePtList pts) ∗
          vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
        ((fsp + 40#64) ↦₆₄ v40) ∗
        ((fsp + 48#64) ↦₆₄ v48) ∗
        ((fsp + 56#64) ↦₆₄ v56) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  refine SepWPp.weaken_pre
    (sepConj_mono_left (vecPtOf_expose A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts)) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap_pts
  apply SepWPp.exists_elim; intro ptr_pts
  apply SepWPp.pure_elim; rintro ⟨hmax, hptr_pts⟩
  cases pts with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, serializePtList_nil, BitVec.ofNat_eq_ofNat] at hmax hnext
    conv => arg 4; simp only [List.length_nil, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
    refine SepWPp.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName + 300#64)
      (P_mid :=
        ((fsp + 40#64) ↦₆₄ 0#64) ∗
          ((fsp + 48#64) ↦₆₄ 1#64) ∗
          ((fsp + 56#64) ↦₆₄ 0#64) ∗
          vecU8Buf A 0#64 1#64 [] ∗
          vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) [] ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q_mid := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 64#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 j ∧
        sm.readReg64 .x23 = 24#64 ∧
        sm.readReg64 .x24 = 1#64 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · into_pb_fetches_range b (Rust.withPanics ext) 148 16
      into_pb_fetches_range b (Rust.withPanics ext) 292 8
      dsimp only [tripleRatchetProgAtExt, decoderIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder>::into_pb" = entry
      examples_hide_fetches
      wp_steps
      have hfold_pt := vecPtOf_intro A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) cap_pts ptr_pts []
      simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hfold_pt
      have hbuf := vecU8Buf_nil_intro A
        (vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) [] ∗
          ((fsp + 40#64) ↦₆₄ 0#64) ∗
          ((fsp + 48#64) ↦₆₄ 1#64) ∗
          ((fsp + 56#64) ↦₆₄ 0#64) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      have hent :
          (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
            (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
            (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
            arrayAt ptAt 4 ptr_pts [] ∗
            vecPtTail A cap_pts ptr_pts 0 ∗
            ((fsp + 40#64) ↦₆₄ 0#64) ∗
            ((fsp + 48#64) ↦₆₄ 1#64) ∗
            ((fsp + 56#64) ↦₆₄ 0#64) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ⊢
          (((fsp + 40#64) ↦₆₄ 0#64) ∗
            ((fsp + 48#64) ↦₆₄ 1#64) ∗
            ((fsp + 56#64) ↦₆₄ 0#64) ∗
            vecU8Buf A 0#64 1#64 [] ∗
            vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) [] ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame) := by
        have h1 :
            (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
              (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
              (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
              arrayAt ptAt 4 ptr_pts [] ∗
              vecPtTail A cap_pts ptr_pts 0 ∗
              ((fsp + 40#64) ↦₆₄ 0#64) ∗
              ((fsp + 48#64) ↦₆₄ 1#64) ∗
              ((fsp + 56#64) ↦₆₄ 0#64) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame) =
            ((((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
              (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
              (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
              arrayAt ptAt 4 ptr_pts [] ∗
              vecPtTail A cap_pts ptr_pts 0) ∗
              (((fsp + 40#64) ↦₆₄ 0#64) ∗
                ((fsp + 48#64) ↦₆₄ 1#64) ∗
                ((fsp + 56#64) ↦₆₄ 0#64) ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame)) := by ac_rfl
        rw [h1]
        refine Entails.trans (sepConj_mono_left hfold_pt) ?_
        refine Entails.trans hbuf ?_
        exact Entails.of_eq (by ac_rfl)
      exact SepWP.weaken_pre hent (by wp_done)
    · intro sm hpcm hrunm ⟨hspm, hx29m, hx19m, hx20m, hx22m, hx23m, hx24m, hx28m, htrm, hvregsm⟩
      exact hnext sm 0#64 1#64 hpcm hrunm hspm hx29m hx19m hx20m hx22m hx23m hx24m hx28m htrm hvregsm
  | cons pt pts' =>
    have hpts_pos : 0 < (pt :: pts').length := by simp
    have hbeq0 : (BitVec.ofNat 64 (pt :: pts').length == 0#64) = false :=
      ofNat_beq_zero_false hpts_pos (by omega)
    have hlsl : (BitVec.ofNat 64 (pt :: pts').length) <<< 2 = BitVec.ofNat 64 (4 * (pt :: pts').length) :=
      shiftLeft_two_eq_mul_four hmax
    have htoNat_len : (BitVec.ofNat 64 (4 * (pt :: pts').length)).toNat = 4 * (pt :: pts').length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk (4 * (pt :: pts').length) 1 := ⟨by omega, hpow2, by omega⟩
    into_pb_fetches_range b (Rust.withPanics ext) 148 56
    dsimp only [tripleRatchetProgAtExt, decoderIntoPbName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hnext ⊢
    have hentry_raw : HiddenEq ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<spqr::encoding::polynomial::PolyDecoder>::into_pb") (intoPbEntry b ext) :=
      ⟨intoPbEntry_raw_eq b ext⟩
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder>::into_pb" = entry
    have hentry : HiddenEq entry ((tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName) :=
      ⟨hentry_raw.eq.trans (intoPbEntry_eq b ext)⟩
    clear hentry_raw
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 180#64)
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
      refine sepWPp_pure_mid fun htr_oom => ?_
      refine SepWPp.seq_clean (mid := entry + 384#64)
        (P_mid :=
          A.pool ∗
          stackAt sf.sp allocHookStack ∗
          ((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
          (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
          (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt :: pts').length) ∗
          arrayAt ptAt 4 ptr_pts (pt :: pts') ∗
          vecPtTail A cap_pts ptr_pts (pt :: pts').length ∗
          ((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗ ((fsp + 56#64) ↦₆₄ v56) ∗ Frame)
        (Q_mid := fun sm => sm.trace = s0.trace ++ [allocFailedEvent])
        ?_ ?_
      · wp_steps
        wp_done
      · intro sm hpcm hrunm htrm
        rw [hentry.eq] at hpcm
        exact into_pb_panic_384 s0 sm _ R hpcm hrunm htrm
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hoom64
      conv => arg 4; simp only [hoom, ↓reduceIte, htoNat_len, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
      let ptr_c := sf_1.readReg64 (Reg.gpr 0#5)
      refine SepWPp.seq_clean (mid := entry + 204#64)
        (P_mid :=
          arrayAt ptAt 4 ptr_pts (pt :: pts') ∗
            memRegion (ptr_c + BitVec.ofNat 64 (4 * 0)) (4 * (pt :: pts').length) ∗
            ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
            ((fsp + 56#64) ↦₆₄ 0#64) ∗
            ((fsp + 48#64) ↦₆₄ ptr_c) ∗
            ((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
            (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
            (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt :: pts').length) ∗
            vecPtTail A cap_pts ptr_pts (pt :: pts').length ∗
            A.live ptr_c (4 * (pt :: pts').length) 1 ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q_mid := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x29 = fsp + 64#64 ∧
          sm.readReg64 .x0 = ptr_c ∧
          sm.readReg64 .x1 = BitVec.ofNat 64 (4 * 0) ∧
          sm.readReg64 .x25 = BitVec.ofNat 64 (pt :: pts').length ∧
          sm.readReg64 .x21 = ptr_pts + 2#64 ∧
          sm.readReg64 .x19 = s0.readReg64 .x19 ∧
          sm.readReg64 .x20 = s0.readReg64 .x20 ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 j ∧
          sm.readReg64 .x23 = 24#64 ∧
          sm.readReg64 .x24 = 1#64 ∧
          sm.readReg64 .x28 = s0.readReg64 .x28 ∧
          sm.trace = s0.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0)
        ?_ ?_
      · wp_steps
        have hz : ptr_c + BitVec.ofNat 64 (4 * 0) = ptr_c := by simp
        rw [hz]
        wp_done
      · intro s_in hpc_in hrun_in ⟨hsp_in, hx29_in, hx0_in, hx1_in, hx25_in, hx21_in,
          hx19_in, hx20_in, hx22_in, hx23_in, hx24_in, hx28_in, htr_in, hvregs_in⟩
        have hpc_in' : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName + 204#64 := by
          rw [← hentry.eq]; exact hpc_in
        have hloop := pts_inner_loop (b := b) (ext := ext) s_in fsp ptr_c
          (pt :: pts').length hmax (pt :: pts') (List.cons_ne_nil pt pts') 0 (by omega)
          s_in ptr_pts 0#64
          (((fsp + 48#64) ↦₆₄ ptr_c) ∗
            ((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
            (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
            (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt :: pts').length) ∗
            vecPtTail A cap_pts ptr_pts (pt :: pts').length ∗
            A.live ptr_c (4 * (pt :: pts').length) 1 ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          hpc_in' hrun_in hsp_in hx29_in hx0_in hx1_in hx25_in hx21_in
          rfl rfl rfl rfl rfl rfl rfl rfl
        refine SepWPp.seq_clean hloop ?_
        intro s_out hpc_out hrun_out ⟨hsp_out, hx29_out, hx19_out, hx20_out,
          hx22_out, hx23_out, hx24_out, hx28_out, htr_out, hvregs_out⟩
        rw [hx19_in] at hx19_out
        rw [hx20_in] at hx20_out
        rw [hx22_in] at hx22_out
        rw [hx23_in] at hx23_out
        rw [hx24_in] at hx24_out
        rw [hx28_in] at hx28_out
        rw [htr_in] at htr_out
        rw [hvregs_in] at hvregs_out
        have hz : ptr_c + BitVec.ofNat 64 (4 * 0) = ptr_c := by simp
        have hser_len : (serializePtList (pt :: pts')).length = 4 * (pt :: pts').length :=
          length_serializePtList (pt :: pts')
        have hbuf := vecU8Buf_of_exact_alloc A ptr_c (serializePtList (pt :: pts'))
          (by rw [hser_len]; omega) (by rw [hser_len]; omega) hoom
        have hfold_pt := vecPtOf_intro A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) cap_pts ptr_pts (pt :: pts')
        have hent :
            (arrayAt ptAt 4 ptr_pts (pt :: pts') ∗
              ((ptr_c + BitVec.ofNat 64 (4 * 0)) ↦ₛ serializePtList (pt :: pts')) ∗
              ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
              ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
              ((fsp + 48#64) ↦₆₄ ptr_c) ∗
              ((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
              (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
              (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt :: pts').length) ∗
              vecPtTail A cap_pts ptr_pts (pt :: pts').length ∗
              A.live ptr_c (4 * (pt :: pts').length) 1 ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ⊢
            (((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
              ((fsp + 48#64) ↦₆₄ ptr_c) ∗
              ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (serializePtList (pt :: pts')).length) ∗
              vecU8Buf A (BitVec.ofNat 64 (4 * (pt :: pts').length)) ptr_c (serializePtList (pt :: pts')) ∗
              vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) (pt :: pts') ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame) := by
          rw [hz]
          rw [hser_len] at hbuf ⊢
          have hg1 :
              (arrayAt ptAt 4 ptr_pts (pt :: pts') ∗
                (ptr_c ↦ₛ serializePtList (pt :: pts')) ∗
                ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
                ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
                ((fsp + 48#64) ↦₆₄ ptr_c) ∗
                ((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
                (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
                (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt :: pts').length) ∗
                vecPtTail A cap_pts ptr_pts (pt :: pts').length ∗
                A.live ptr_c (4 * (pt :: pts').length) 1 ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame) =
              (((ptr_c ↦ₛ serializePtList (pt :: pts')) ∗
                A.live ptr_c (4 * (pt :: pts').length) 1) ∗
                ((((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
                  (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
                  (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt :: pts').length) ∗
                  arrayAt ptAt 4 ptr_pts (pt :: pts') ∗
                  vecPtTail A cap_pts ptr_pts (pt :: pts').length) ∗
                  (((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
                    ((fsp + 48#64) ↦₆₄ ptr_c) ∗
                    ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
                    A.pool ∗ stackAt fsp allocHookStack ∗ Frame))) := by ac_rfl
          rw [hg1]
          refine Entails.trans (sepConj_mono hbuf (sepConj_mono_left hfold_pt)) ?_
          exact Entails.of_eq (by ac_rfl)
        rw [← hentry.eq] at hpc_out
        exact SepWPp.weaken_pre hent
          (hnext s_out (BitVec.ofNat 64 (4 * (pt :: pts').length)) ptr_c
            hpc_out hrun_out hsp_out hx29_out hx19_out hx20_out hx22_out hx23_out hx24_out hx28_out htr_out hvregs_out)

theorem arrayAt_24_off_cons {α : Type} (elemPred : α → BitVec 64 → SepProp)
    (base : BitVec 64) (j : Nat) (x : α) (xs : List α) :
    arrayAt elemPred 24 (base + BitVec.ofNat 64 (24 * j)) (x :: xs) =
      (elemPred x (base + BitVec.ofNat 64 (24 * j)) ∗
        arrayAt elemPred 24 (base + BitVec.ofNat 64 (24 * (j + 1))) xs) := by
  rw [arrayAt_cons, off_24_succ]

theorem arrayAt_24_off_singleton {α : Type} (elemPred : α → BitVec 64 → SepProp)
    (base : BitVec 64) (j : Nat) (x : α) :
    arrayAt elemPred 24 (base + BitVec.ofNat 64 (24 * j)) [x] =
      elemPred x (base + BitVec.ofNat 64 (24 * j)) := by
  rw [arrayAt_cons, arrayAt_nil, sepConj_emp]

/-- Full `pts` outer loop (`+148 -> +328`, or OOM panic). -/
theorem pts_outer_loop {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName +
        bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5dc38))
      sessionShimSpec)
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName +
        bv% (ls_off% "__rustc::__rust_alloc" - 0x5dc38))
      (rustAllocSpec A))
    {Q : State → SepProp → Prop} {R : SepProp}
    (s0 : State) (fsp ptr_pts : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (rem : List (List Pt)) (hne : rem ≠ [])
    (j : Nat) (htot : j + rem.length = 16)
    (v40 v48 v56 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName + 148#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 64#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 j)
    (hx23 : s.readReg64 .x23 = 24#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (sm : State) (w40 w48 w56 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName + 328#64 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.readReg64 .x29 = fsp + 64#64 →
      sm.readReg64 .x19 = s0.readReg64 .x19 →
      sm.readReg64 .x20 = s0.readReg64 .x20 →
      sm.readReg64 .x28 = s0.readReg64 .x28 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        ((fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
          ((fsp + 16#64) ↦₆₄ 16#64) ∗
          ((fsp + 40#64) ↦₆₄ w40) ∗
          ((fsp + 48#64) ↦₆₄ w48) ∗
          ((fsp + 56#64) ↦₆₄ w56) ∗
          arrayAt (fun pts addr => vecPtOf A addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) rem ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptr_pts + BitVec.ofNat 64 (24 * j)) (rem.map serializePtList) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 40#64) ↦₆₄ v40) ∗
        ((fsp + 48#64) ↦₆₄ v48) ∗
        ((fsp + 56#64) ↦₆₄ v56) ∗
        arrayAt (fun pts addr => vecPtOf A addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) rem ∗
        memRegion (ptr_pts + BitVec.ofNat 64 (24 * j)) (24 * rem.length) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  induction rem generalizing j v40 v48 v56 s Frame with
  | nil => exact (hne rfl).elim
  | cons pts rem' ih =>
    have htot' : j + (rem'.length + 1) = 16 := by
      simpa [List.length_cons] using htot
    rw [arrayAt_24_off_cons]
    conv => arg 4; rw [List.length_cons]
    refine SepWPp.weaken_pre (P' :=
      vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
        ((fsp + 40#64) ↦₆₄ v40) ∗
        ((fsp + 48#64) ↦₆₄ v48) ∗
        ((fsp + 56#64) ↦₆₄ v56) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        ((fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
          ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
          arrayAt (fun pts addr => vecPtOf A addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * (j + 1))) rem' ∗
          memRegion (ptr_pts + BitVec.ofNat 64 (24 * j)) (24 * (rem'.length + 1)) ∗
          Frame))
      (Entails.of_eq (by ac_rfl)) ?_
    refine pts_outer_alloc_and_copy hshim halloc s0 fsp hfsp_align j pts v40 v48 v56 s _
      hpc hrun hsp hx29 hx19 hx20 hx22 hx23 hx24 hx28 htrace hvregs ?_
    intro sm1 cap_c ptr_c hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1 hvregs1
    refine SepWPp.weaken_pre (P' :=
      (fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 40#64) ↦₆₄ cap_c) ∗
        ((fsp + 48#64) ↦₆₄ ptr_c) ∗
        ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (serializePtList pts).length) ∗
        vecU8Buf A cap_c ptr_c (serializePtList pts) ∗
        memRegion (ptr_pts + BitVec.ofNat 64 (24 * j)) (24 * (rem'.length + 1)) ∗
        (vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
          arrayAt (fun pts addr => vecPtOf A addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * (j + 1))) rem' ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame))
      (Entails.of_eq (by ac_rfl)) ?_
    have hfin := pts_outer_finish_iter (b := b) (A := A) (ext := ext)
      s0 fsp ptr_pts hfsp_align j rem'.length htot'
      (serializePtList pts) cap_c ptr_c sm1
      (vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
        arrayAt (fun pts addr => vecPtOf A addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * (j + 1))) rem' ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1 hvregs1
    refine SepWPp.seq_clean hfin ?_
    intro sm2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx28_2, htr2, hvregs2⟩
    cases rem' with
    | nil =>
      have hj1 : j + 1 = 16 := by simp at htot'; omega
      simp only [hj1, ↓reduceIte] at hpc2
      have h16 : BitVec.ofNat 64 (j + 1) = 16#64 := by rw [hj1]
      refine SepWPp.weaken_pre ?_ (hnext sm2 cap_c ptr_c (BitVec.ofNat 64 (serializePtList pts).length)
        hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx28_2 htr2 hvregs2)
      simp only [List.length_nil, List.map_cons, List.map_nil, arrayAt_nil, arrayAt_24_off_singleton,
        Nat.mul_zero, memRegion_zero, sepConj_emp, h16]
      exact Entails.of_eq (by ac_rfl)
    | cons pts2 rem'' =>
      have hj1 : j + 1 ≠ 16 := by simp at htot'; omega
      simp only [hj1, ↓reduceIte] at hpc2
      refine SepWPp.weaken_pre (P' :=
        (fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
          ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 40#64) ↦₆₄ cap_c) ∗
          ((fsp + 48#64) ↦₆₄ ptr_c) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (serializePtList pts).length) ∗
          arrayAt (fun pts addr => vecPtOf A addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * (j + 1))) (pts2 :: rem'') ∗
          memRegion (ptr_pts + BitVec.ofNat 64 (24 * (j + 1))) (24 * (pts2 :: rem'').length) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
            vecU8 A (ptr_pts + BitVec.ofNat 64 (24 * j)) (serializePtList pts) ∗
            Frame))
        (Entails.of_eq (by ac_rfl)) ?_
      refine ih (List.cons_ne_nil pts2 rem'') (j + 1) (by simp at htot' ⊢; omega)
        cap_c ptr_c (BitVec.ofNat 64 (serializePtList pts).length)
        sm2
        (vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
          vecU8 A (ptr_pts + BitVec.ofNat 64 (24 * j)) (serializePtList pts) ∗
          Frame)
        hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx22_2 hx23_2 hx24_2 hx28_2 htr2 hvregs2 ?_
      intro sm3 w40 w48 w56 hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 hx28_3 htr3 hvregs3
      refine SepWPp.weaken_pre ?_
        (hnext sm3 w40 w48 w56 hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 hx28_3 htr3 hvregs3)
      simp only [List.map_cons, arrayAt_24_off_cons]
      exact Entails.of_eq (by ac_rfl)

end Legacy

/-! ## Relocatable (`[LibsignalPlacement]`) Outer Loop for Block `377` -/

theorem pts_outer_alloc_and_copy_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    {Q : State → SepProp → Prop} {R : SepProp}
    (s0 : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j : Nat) (pts : List Pt)
    (v40 v48 v56 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_377).base + 148#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 64#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 j)
    (hx23 : s.readReg64 .x23 = 24#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (sm : State) (cap_c ptr_c : BitVec 64),
      sm.pc = (blkPl_377).base + 300#64 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.readReg64 .x29 = fsp + 64#64 →
      sm.readReg64 .x19 = s0.readReg64 .x19 →
      sm.readReg64 .x20 = s0.readReg64 .x20 →
      sm.readReg64 .x22 = BitVec.ofNat 64 j →
      sm.readReg64 .x23 = 24#64 →
      sm.readReg64 .x24 = 1#64 →
      sm.readReg64 .x28 = s0.readReg64 .x28 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
        (((fsp + 40#64) ↦₆₄ cap_c) ∗
          ((fsp + 48#64) ↦₆₄ ptr_c) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (serializePtList pts).length) ∗
          vecU8Buf A cap_c ptr_c (serializePtList pts) ∗
          vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
        ((fsp + 40#64) ↦₆₄ v40) ∗
        ((fsp + 48#64) ↦₆₄ v48) ∗
        ((fsp + 56#64) ↦₆₄ v56) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  have hshim : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimSpec :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem hshim_sat
  have halloc : subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem halloc_sat
  simp only [sessionShimSpec, BitVec.ofNat_eq_ofNat] at hshim
  simp only [rustAllocSpec, BitVec.ofNat_eq_ofNat] at halloc
  refine SepWPp.weaken_pre
    (sepConj_mono_left (vecPtOf_expose A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts)) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap_pts
  apply SepWPp.exists_elim; intro ptr_pts
  apply SepWPp.pure_elim; rintro ⟨hmax, hptr_pts⟩
  cases pts with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, serializePtList_nil, BitVec.ofNat_eq_ofNat] at hmax hnext
    conv => arg 4; simp only [List.length_nil, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
    refine SepWPp.seq_clean (mid := (blkPl_377).base + 300#64)
      (P_mid :=
        ((fsp + 40#64) ↦₆₄ 0#64) ∗
          ((fsp + 48#64) ↦₆₄ 1#64) ∗
          ((fsp + 56#64) ↦₆₄ 0#64) ∗
          vecU8Buf A 0#64 1#64 [] ∗
          vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) [] ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q_mid := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 64#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 j ∧
        sm.readReg64 .x23 = 24#64 ∧
        sm.readReg64 .x24 = 1#64 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · wp_steps
      have hfold_pt := vecPtOf_intro A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) cap_pts ptr_pts []
      simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hfold_pt
      have hbuf := vecU8Buf_nil_intro A
        (vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) [] ∗
          ((fsp + 40#64) ↦₆₄ 0#64) ∗
          ((fsp + 48#64) ↦₆₄ 1#64) ∗
          ((fsp + 56#64) ↦₆₄ 0#64) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      have hent :
          (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
            (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
            (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
            arrayAt ptAt 4 ptr_pts [] ∗
            vecPtTail A cap_pts ptr_pts 0 ∗
            ((fsp + 40#64) ↦₆₄ 0#64) ∗
            ((fsp + 48#64) ↦₆₄ 1#64) ∗
            ((fsp + 56#64) ↦₆₄ 0#64) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ⊢
          (((fsp + 40#64) ↦₆₄ 0#64) ∗
            ((fsp + 48#64) ↦₆₄ 1#64) ∗
            ((fsp + 56#64) ↦₆₄ 0#64) ∗
            vecU8Buf A 0#64 1#64 [] ∗
            vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) [] ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame) := by
        have h1 :
            (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
              (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
              (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
              arrayAt ptAt 4 ptr_pts [] ∗
              vecPtTail A cap_pts ptr_pts 0 ∗
              ((fsp + 40#64) ↦₆₄ 0#64) ∗
              ((fsp + 48#64) ↦₆₄ 1#64) ∗
              ((fsp + 56#64) ↦₆₄ 0#64) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame) =
            ((((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
              (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
              (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
              arrayAt ptAt 4 ptr_pts [] ∗
              vecPtTail A cap_pts ptr_pts 0) ∗
              (((fsp + 40#64) ↦₆₄ 0#64) ∗
                ((fsp + 48#64) ↦₆₄ 1#64) ∗
                ((fsp + 56#64) ↦₆₄ 0#64) ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame)) := by ac_rfl
        rw [h1]
        refine Entails.trans (sepConj_mono_left hfold_pt) ?_
        refine Entails.trans hbuf ?_
        exact Entails.of_eq (by ac_rfl)
      exact SepWP.weaken_pre hent (by wp_done)
    · intro sm hpcm hrunm ⟨hspm, hx29m, hx19m, hx20m, hx22m, hx23m, hx24m, hx28m, htrm, hvregsm⟩
      exact hnext sm 0#64 1#64 hpcm hrunm hspm hx29m hx19m hx20m hx22m hx23m hx24m hx28m htrm hvregsm
  | cons pt pts' =>
    have hpts_pos : 0 < (pt :: pts').length := by simp
    have hbeq0 : (BitVec.ofNat 64 (pt :: pts').length == 0#64) = false :=
      ofNat_beq_zero_false hpts_pos (by omega)
    have hlsl : (BitVec.ofNat 64 (pt :: pts').length) <<< 2 = BitVec.ofNat 64 (4 * (pt :: pts').length) :=
      shiftLeft_two_eq_mul_four hmax
    have htoNat_len : (BitVec.ofNat 64 (4 * (pt :: pts').length)).toNat = 4 * (pt :: pts').length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk (4 * (pt :: pts').length) 1 := ⟨by omega, hpow2, by omega⟩
    apply SepWPp.of_sepWP (mid := (blkPl_377).base + 180#64)
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
      refine sepWPp_pure_mid fun htr_oom => ?_
      refine SepWPp.seq_clean (mid := (blkPl_377).base + 384#64)
        (P_mid :=
          A.pool ∗
          stackAt sf.sp allocHookStack ∗
          ((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
          (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
          (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt :: pts').length) ∗
          arrayAt ptAt 4 ptr_pts (pt :: pts') ∗
          vecPtTail A cap_pts ptr_pts (pt :: pts').length ∗
          ((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗ ((fsp + 56#64) ↦₆₄ v56) ∗ Frame)
        (Q_mid := fun sm => sm.trace = s0.trace ++ [allocFailedEvent])
        ?_ ?_
      · wp_steps
        wp_done
      · intro sm hpcm hrunm htrm
        exact into_pb_panic_384_placed h_panic s0 sm _ R hpcm hrunm htrm
    · have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hoom
      conv => arg 4; simp only [hoom, ↓reduceIte, htoNat_len, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
      let ptr_c := sf_1.readReg64 (Reg.gpr 0#5)
      refine SepWPp.seq_clean (mid := (blkPl_377).base + 204#64)
        (P_mid :=
          arrayAt ptAt 4 ptr_pts (pt :: pts') ∗
            memRegion (ptr_c + BitVec.ofNat 64 (4 * 0)) (4 * (pt :: pts').length) ∗
            ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
            ((fsp + 56#64) ↦₆₄ 0#64) ∗
            ((fsp + 48#64) ↦₆₄ ptr_c) ∗
            ((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
            (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
            (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt :: pts').length) ∗
            vecPtTail A cap_pts ptr_pts (pt :: pts').length ∗
            A.live ptr_c (4 * (pt :: pts').length) 1 ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q_mid := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x29 = fsp + 64#64 ∧
          sm.readReg64 .x0 = ptr_c ∧
          sm.readReg64 .x1 = BitVec.ofNat 64 (4 * 0) ∧
          sm.readReg64 .x25 = BitVec.ofNat 64 (pt :: pts').length ∧
          sm.readReg64 .x21 = ptr_pts + 2#64 ∧
          sm.readReg64 .x19 = s0.readReg64 .x19 ∧
          sm.readReg64 .x20 = s0.readReg64 .x20 ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 j ∧
          sm.readReg64 .x23 = 24#64 ∧
          sm.readReg64 .x24 = 1#64 ∧
          sm.readReg64 .x28 = s0.readReg64 .x28 ∧
          sm.trace = s0.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0)
        ?_ ?_
      · wp_steps
        have hz : ptr_c + BitVec.ofNat 64 (4 * 0) = ptr_c := by simp
        rw [hz]
        wp_done
      · intro s_in hpc_in hrun_in ⟨hsp_in, hx29_in, hx0_in, hx1_in, hx25_in, hx21_in,
          hx19_in, hx20_in, hx22_in, hx23_in, hx24_in, hx28_in, htr_in, hvregs_in⟩
        have hloop := pts_inner_loop_placed (ext := ext) s_in fsp ptr_c
          (pt :: pts').length hmax (pt :: pts') (List.cons_ne_nil pt pts') 0 (by omega)
          s_in ptr_pts 0#64
          (((fsp + 48#64) ↦₆₄ ptr_c) ∗
            ((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
            (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
            (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt :: pts').length) ∗
            vecPtTail A cap_pts ptr_pts (pt :: pts').length ∗
            A.live ptr_c (4 * (pt :: pts').length) 1 ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          hpc_in hrun_in hsp_in hx29_in hx0_in hx1_in hx25_in hx21_in
          rfl rfl rfl rfl rfl rfl rfl rfl
        refine SepWPp.seq_clean hloop ?_
        intro s_out hpc_out hrun_out ⟨hsp_out, hx29_out, hx19_out, hx20_out,
          hx22_out, hx23_out, hx24_out, hx28_out, htr_out, hvregs_out⟩
        rw [hx19_in] at hx19_out
        rw [hx20_in] at hx20_out
        rw [hx22_in] at hx22_out
        rw [hx23_in] at hx23_out
        rw [hx24_in] at hx24_out
        rw [hx28_in] at hx28_out
        rw [htr_in] at htr_out
        rw [hvregs_in] at hvregs_out
        have hz : ptr_c + BitVec.ofNat 64 (4 * 0) = ptr_c := by simp
        have hser_len : (serializePtList (pt :: pts')).length = 4 * (pt :: pts').length :=
          length_serializePtList (pt :: pts')
        have hbuf := vecU8Buf_of_exact_alloc A ptr_c (serializePtList (pt :: pts'))
          (by rw [hser_len]; omega) (by rw [hser_len]; omega) hoom
        have hfold_pt := vecPtOf_intro A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) cap_pts ptr_pts (pt :: pts')
        have hent :
            (arrayAt ptAt 4 ptr_pts (pt :: pts') ∗
              ((ptr_c + BitVec.ofNat 64 (4 * 0)) ↦ₛ serializePtList (pt :: pts')) ∗
              ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
              ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
              ((fsp + 48#64) ↦₆₄ ptr_c) ∗
              ((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
              (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
              (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt :: pts').length) ∗
              vecPtTail A cap_pts ptr_pts (pt :: pts').length ∗
              A.live ptr_c (4 * (pt :: pts').length) 1 ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ⊢
            (((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
              ((fsp + 48#64) ↦₆₄ ptr_c) ∗
              ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (serializePtList (pt :: pts')).length) ∗
              vecU8Buf A (BitVec.ofNat 64 (4 * (pt :: pts').length)) ptr_c (serializePtList (pt :: pts')) ∗
              vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) (pt :: pts') ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame) := by
          rw [hz]
          rw [hser_len] at hbuf ⊢
          have hg1 :
              (arrayAt ptAt 4 ptr_pts (pt :: pts') ∗
                (ptr_c ↦ₛ serializePtList (pt :: pts')) ∗
                ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
                ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
                ((fsp + 48#64) ↦₆₄ ptr_c) ∗
                ((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
                (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
                (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt :: pts').length) ∗
                vecPtTail A cap_pts ptr_pts (pt :: pts').length ∗
                A.live ptr_c (4 * (pt :: pts').length) 1 ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame) =
              (((ptr_c ↦ₛ serializePtList (pt :: pts')) ∗
                A.live ptr_c (4 * (pt :: pts').length) 1) ∗
                ((((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_pts) ∗
                  (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_pts) ∗
                  (((s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt :: pts').length) ∗
                  arrayAt ptAt 4 ptr_pts (pt :: pts') ∗
                  vecPtTail A cap_pts ptr_pts (pt :: pts').length) ∗
                  (((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
                    ((fsp + 48#64) ↦₆₄ ptr_c) ∗
                    ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (4 * (pt :: pts').length)) ∗
                    A.pool ∗ stackAt fsp allocHookStack ∗ Frame))) := by ac_rfl
          rw [hg1]
          refine Entails.trans (sepConj_mono hbuf (sepConj_mono_left hfold_pt)) ?_
          exact Entails.of_eq (by ac_rfl)
        exact SepWPp.weaken_pre hent
          (hnext s_out (BitVec.ofNat 64 (4 * (pt :: pts').length)) ptr_c
            hpc_out hrun_out hsp_out hx29_out hx19_out hx20_out hx22_out hx23_out hx24_out hx28_out htr_out hvregs_out)

theorem pts_outer_loop_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    {Q : State → SepProp → Prop} {R : SepProp}
    (s0 : State) (fsp ptr_pts : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (rem : List (List Pt)) (hne : rem ≠ [])
    (j : Nat) (htot : j + rem.length = 16)
    (v40 v48 v56 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_377).base + 148#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 64#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 j)
    (hx23 : s.readReg64 .x23 = 24#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (sm : State) (w40 w48 w56 : BitVec 64),
      sm.pc = (blkPl_377).base + 328#64 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.readReg64 .x29 = fsp + 64#64 →
      sm.readReg64 .x19 = s0.readReg64 .x19 →
      sm.readReg64 .x20 = s0.readReg64 .x20 →
      sm.readReg64 .x28 = s0.readReg64 .x28 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
        ((fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
          ((fsp + 16#64) ↦₆₄ 16#64) ∗
          ((fsp + 40#64) ↦₆₄ w40) ∗
          ((fsp + 48#64) ↦₆₄ w48) ∗
          ((fsp + 56#64) ↦₆₄ w56) ∗
          arrayAt (fun pts addr => vecPtOf A addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) rem ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptr_pts + BitVec.ofNat 64 (24 * j)) (rem.map serializePtList) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 40#64) ↦₆₄ v40) ∗
        ((fsp + 48#64) ↦₆₄ v48) ∗
        ((fsp + 56#64) ↦₆₄ v56) ∗
        arrayAt (fun pts addr => vecPtOf A addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) rem ∗
        memRegion (ptr_pts + BitVec.ofNat 64 (24 * j)) (24 * rem.length) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  induction rem generalizing j v40 v48 v56 s Frame with
  | nil => exact (hne rfl).elim
  | cons pts rem' ih =>
    have htot' : j + (rem'.length + 1) = 16 := by
      simpa [List.length_cons] using htot
    rw [arrayAt_24_off_cons]
    conv => arg 4; rw [List.length_cons]
    refine SepWPp.weaken_pre (P' :=
      vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
        ((fsp + 40#64) ↦₆₄ v40) ∗
        ((fsp + 48#64) ↦₆₄ v48) ∗
        ((fsp + 56#64) ↦₆₄ v56) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        ((fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
          ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
          arrayAt (fun pts addr => vecPtOf A addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * (j + 1))) rem' ∗
          memRegion (ptr_pts + BitVec.ofNat 64 (24 * j)) (24 * (rem'.length + 1)) ∗
          Frame))
      (Entails.of_eq (by ac_rfl)) ?_
    refine pts_outer_alloc_and_copy_placed h_panic hshim_sat halloc_sat s0 fsp hfsp_align j pts v40 v48 v56 s _
      hpc hrun hsp hx29 hx19 hx20 hx22 hx23 hx24 hx28 htrace hvregs ?_
    intro sm1 cap_c ptr_c hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1 hvregs1
    refine SepWPp.weaken_pre (P' :=
      (fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 40#64) ↦₆₄ cap_c) ∗
        ((fsp + 48#64) ↦₆₄ ptr_c) ∗
        ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (serializePtList pts).length) ∗
        vecU8Buf A cap_c ptr_c (serializePtList pts) ∗
        memRegion (ptr_pts + BitVec.ofNat 64 (24 * j)) (24 * (rem'.length + 1)) ∗
        (vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
          arrayAt (fun pts addr => vecPtOf A addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * (j + 1))) rem' ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame))
      (Entails.of_eq (by ac_rfl)) ?_
    have hfin := pts_outer_finish_iter_placed (A := A) (ext := ext)
      s0 fsp ptr_pts hfsp_align j rem'.length htot'
      (serializePtList pts) cap_c ptr_c sm1
      (vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
        arrayAt (fun pts addr => vecPtOf A addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * (j + 1))) rem' ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1 hvregs1
    refine SepWPp.seq_clean hfin ?_
    intro sm2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx28_2, htr2, hvregs2⟩
    cases rem' with
    | nil =>
      have hj1 : j + 1 = 16 := by simp at htot'; omega
      simp only [hj1, ↓reduceIte] at hpc2
      have h16 : BitVec.ofNat 64 (j + 1) = 16#64 := by rw [hj1]
      refine SepWPp.weaken_pre ?_ (hnext sm2 cap_c ptr_c (BitVec.ofNat 64 (serializePtList pts).length)
        hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx28_2 htr2 hvregs2)
      simp only [List.length_nil, List.map_cons, List.map_nil, arrayAt_nil, arrayAt_24_off_singleton,
        Nat.mul_zero, memRegion_zero, sepConj_emp, h16]
      exact Entails.of_eq (by ac_rfl)
    | cons pts2 rem'' =>
      have hj1 : j + 1 ≠ 16 := by simp at htot'; omega
      simp only [hj1, ↓reduceIte] at hpc2
      refine SepWPp.weaken_pre (P' :=
        (fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
          ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 40#64) ↦₆₄ cap_c) ∗
          ((fsp + 48#64) ↦₆₄ ptr_c) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (serializePtList pts).length) ∗
          arrayAt (fun pts addr => vecPtOf A addr pts) 24 (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * (j + 1))) (pts2 :: rem'') ∗
          memRegion (ptr_pts + BitVec.ofNat 64 (24 * (j + 1))) (24 * (pts2 :: rem'').length) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
            vecU8 A (ptr_pts + BitVec.ofNat 64 (24 * j)) (serializePtList pts) ∗
            Frame))
        (Entails.of_eq (by ac_rfl)) ?_
      refine ih (List.cons_ne_nil pts2 rem'') (j + 1) (by simp at htot' ⊢; omega)
        cap_c ptr_c (BitVec.ofNat 64 (serializePtList pts).length)
        sm2
        (vecPtOf A (s0.readReg64 .x19 + BitVec.ofNat 64 (24 * j)) pts ∗
          vecU8 A (ptr_pts + BitVec.ofNat 64 (24 * j)) (serializePtList pts) ∗
          Frame)
        hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx22_2 hx23_2 hx24_2 hx28_2 htr2 hvregs2 ?_
      intro sm3 w40 w48 w56 hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 hx28_3 htr3 hvregs3
      refine SepWPp.weaken_pre ?_
        (hnext sm3 w40 w48 w56 hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 hx28_3 htr3 hvregs3)
      simp only [List.map_cons, arrayAt_24_off_cons]
      exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Poly.DecoderPb
