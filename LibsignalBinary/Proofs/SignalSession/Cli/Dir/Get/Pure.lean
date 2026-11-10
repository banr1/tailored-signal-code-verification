/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Fs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Specs
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Pure, Layout, `.rodata`, and Non-I/O Callee Helpers for `<signal_session::stores::Dir>::get`
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.Get.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SpqrV1.Alloc

/-! ## 1. Pure `DirGhost.get` & `FsInv` Lemmas -/

/-- Prefix entries whose names all differ from `name` do not affect `DirGhost.get`. -/
theorem dirGhost_get_append_of_ne
    (pre suf : List (List (BitVec 8) × List (BitVec 8)))
    (p : List (BitVec 8)) (rd : ReadRule) (F : FsFiles) (name : List (BitVec 8))
    (hne : ∀ e ∈ pre, e.1 ≠ name) :
    (DirGhost.mk p (pre ++ suf)).get rd F name =
      (DirGhost.mk p suf).get rd F name := by
  induction pre with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : (hd.1 == name) = false :=
      beq_false_of_ne (hne hd List.mem_cons_self)
    unfold DirGhost.get at *
    change (match List.find? (fun e => e.1 == name) (hd :: (tl ++ suf)) with
      | some e => Except.ok e.2 | none => rd F (pathOf p name)) = _
    rw [List.find?_cons, hhd]
    exact ih (fun e he => hne e (List.mem_cons_of_mem hd he))

/-- Base case: empty `changed` reads from the backing filesystem at `pathOf p name`. -/
theorem dirGhost_get_nil
    (p : List (BitVec 8)) (rd : ReadRule) (F : FsFiles) (name : List (BitVec 8)) :
    (DirGhost.mk p []).get rd F name = rd F (pathOf p name) := rfl

/-- Matching head entry returns `.ok bs` immediately. -/
theorem dirGhost_get_cons_eq
    (bs : List (BitVec 8)) (rest : List (List (BitVec 8) × List (BitVec 8)))
    (p : List (BitVec 8)) (rd : ReadRule) (F : FsFiles) (name : List (BitVec 8)) :
    (DirGhost.mk p ((name, bs) :: rest)).get rd F name = .ok bs := by
  simp [DirGhost.get]

theorem fsInv_of_files_trace_eq {F0 : FsFiles} {T0 : List TraceEvent} {s : State}
    (hf : s.fs.files = F0) (ht : s.trace = T0) : FsInv F0 T0 s := by
  rw [← hf, ← ht]
  exact withFsInv_entry s

theorem files_eq_of_fsInv_trace_eq {F0 : FsFiles} {T0 : List TraceEvent} {s : State}
    (hinv : FsInv F0 T0 s) (ht : s.trace = T0) : s.fs.files = F0 :=
  hinv.files_eq (evs := []) (by simp [ht]) NoFsEv.nil

/-- Commute `withFsInv` inside `Spec.inImage` for any trace-sound program `P`. -/
theorem subroutine_ok_inImage_withFsInv {α : Type} {P : Program} {e : BitVec 64}
    {spec : Spec α} {img : Obj.Image}
    (hP : TraceFsSound P) (h : subroutine_ok P e (spec.inImage img))
    (F0 : FsFiles) (T0 : List TraceEvent) :
    subroutine_ok P e ((withFsInv spec F0 T0).inImage img) := by
  have hfs := subroutine_ok_withFsInv hP h F0 T0
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withFsInv (spec.inImage img) F0 T0).pre x s0 ∗ R := by
    simp only [Spec.inImage, withFsInv, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨hpre.2.1, hpre.1, hpre.2.2⟩
  exact hfs.mono_outcome x R s0 hpc hrun hpre' hal fun _ hout => hout

/-! ## 2. BitVec, String, & Arithmetic Lemmas -/

theorem utf8_read : utf8 "read" = [0x72#8, 0x65#8, 0x61#8, 0x64#8] := by
  decide +kernel

theorem utf8_read_length : (utf8 "read").length = 4 := by
  rw [utf8_read]; rfl

theorem ofNat_getLsbD_63_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Nat.testBit_lt_two_pow h

theorem ofNat_getElem_63_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false :=
  ofNat_getLsbD_63_false h

theorem ofNat_beq_zero_false {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

theorem cap_cmn1_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  apply beq_false_of_ne
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change cap.toNat + 1 = 0 at ht
  omega

/-! ## 3. Stack Frame & Callee Budget Helpers (`sub sp, sp, #0x70`) -/

/-- Callee stack budget required below `Dir::get`'s `0x70`-byte frame. -/
abbrev dirGetCalleeStk (pathStk callBgt : Nat) : Nat :=
  max (max pathStk callBgt) extHookStack

/-- The 8 saved 64-bit register slots at `[sp + 48 .. sp + 112)` in `Dir::get`'s frame. -/
def savedRegsAt (sp : BitVec 64) (s0 : State) : SepProp :=
  ((sp + 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp + 56#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp + 64#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp + 72#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp + 80#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp + 88#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp + 96#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp + 104#64) ↦₆₄ s0.readReg64 .x19)

theorem stackAt_sub_split (sp : BitVec 64) {sub full : Nat}
    (hle : sub ≤ full) (hfull : full ≤ 2 ^ 64) :
    stackAt sp full =
      memRegion (sp - BitVec.ofNat 64 full) (full - sub) ∗ stackAt sp sub := by
  have h := stackAt_split_bottom sp sub (full - sub) (by omega)
  rwa [Nat.add_sub_of_le hle] at h

/-- Split `0x70` frame bytes at `sp = sp0 - 0x70` into `[0..24)`, `[24..48)`, and 8 saved slots. -/
theorem frame_0x70_split (sp : BitVec 64) :
    memRegion sp 112 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        memRegion sp 24 ∗ memRegion (sp + 24#64) 24 ∗
        ((sp + 48#64) ↦₆₄ v7) ∗ ((sp + 56#64) ↦₆₄ v6) ∗
        ((sp + 64#64) ↦₆₄ v5) ∗ ((sp + 72#64) ↦₆₄ v4) ∗
        ((sp + 80#64) ↦₆₄ v3) ∗ ((sp + 88#64) ↦₆₄ v2) ∗
        ((sp + 96#64) ↦₆₄ v1) ∗ ((sp + 104#64) ↦₆₄ v0) := by
  rw [memRegion_split sp 24 88 (by decide),
      memRegion_split (sp + 24#64) 24 64 (by decide),
      memRegion_split (sp + 24#64 + 24#64) 8 56 (by decide),
      memRegion_split (sp + 24#64 + 24#64 + 8#64) 8 48 (by decide),
      memRegion_split (sp + 24#64 + 24#64 + 8#64 + 8#64) 8 40 (by decide),
      memRegion_split (sp + 24#64 + 24#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
      memRegion_split (sp + 24#64 + 24#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
      memRegion_split (sp + 24#64 + 24#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
      memRegion_split (sp + 24#64 + 24#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
      ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
      ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

/-- Reassemble `memRegion sp 112` from `[sp..sp+24)`, `[sp+24..sp+48)`, and `savedRegsAt sp s0`. -/
theorem frame_0x70_join (sp : BitVec 64) (s0 : State) :
    memRegion sp 24 ∗ memRegion (sp + 24#64) 24 ∗ savedRegsAt sp s0 ⊢
      memRegion sp 112 := by
  unfold savedRegsAt
  rw [memRegion_split sp 24 88 (by decide),
      memRegion_split (sp + 24#64) 24 64 (by decide),
      memRegion_split (sp + 24#64 + 24#64) 8 56 (by decide),
      memRegion_split (sp + 24#64 + 24#64 + 8#64) 8 48 (by decide),
      memRegion_split (sp + 24#64 + 24#64 + 8#64 + 8#64) 8 40 (by decide),
      memRegion_split (sp + 24#64 + 24#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
      memRegion_split (sp + 24#64 + 24#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
      memRegion_split (sp + 24#64 + 24#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
      memRegion_split (sp + 24#64 + 24#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (pointsTo64_entails_memRegion _ _)))))))))

/-- Split `stackAt sp0 stk` into bottom spare, `stackAt (sp0 - 112#64) cstk`, and `memRegion (sp0 - 112#64) 112`. -/
theorem stackAt_dirGet_split (sp0 : BitVec 64) {cstk stk : Nat}
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64) :
    stackAt sp0 stk =
      memRegion (sp0 - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗
      stackAt (sp0 - 112#64) cstk ∗
      memRegion (sp0 - 112#64) 112 := by
  rw [stackAt_sub_split sp0 hstk hfull,
      stackAt_split_bottom sp0 112 cstk (by omega)]
  have hsub : sp0 - BitVec.ofNat 64 (112 + cstk) = sp0 - 112#64 - BitVec.ofNat 64 cstk := by
    rw [show (112#64 : BitVec 64) = BitVec.ofNat 64 112 from rfl,
        Nat.add_comm 112 cstk, BitVec.ofNat_add, BitVec.sub_sub, BitVec.add_comm]
  unfold stackAt
  have h112 : BitVec.ofNat 64 112 = 112#64 := rfl
  rw [hsub, h112]

theorem stackAt_dirGet_join (sp0 : BitVec 64) {cstk stk : Nat}
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64) :
    memRegion (sp0 - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗
      stackAt (sp0 - 112#64) cstk ∗
      memRegion (sp0 - 112#64) 112 ⊢
      stackAt sp0 stk := by
  rw [stackAt_dirGet_split sp0 hstk hfull]
  exact Entails.refl _

/-- Any `memRegion r 48` separated from `stackAt sp0 stk` forces `stk ≤ 2 ^ 64`. -/
theorem stk_le_of_memRegion_sep {m : Memory} {r sp0 : BitVec 64} {stk : Nat} {F : SepProp}
    (hsat : m ⊨ memRegion r 48 ∗ stackAt sp0 stk ∗ F) :
    stk ≤ 2 ^ 64 := by
  by_contra hgt
  have hdisj :=
    (IsBlock.memRegion r 48).disjoint (IsBlock.memRegion (sp0 - BitVec.ofNat 64 stk) stk)
      (by decide) (by omega) hsat
  have hlt := (r - (sp0 - BitVec.ofNat 64 stk)).isLt
  exact absurd hdisj.2 (by omega)

/-- Expose the 3 header cells and `(ptr ↦ₛ bs)` of any `vecU8At` uniformly for both `cap = 0` and `cap ≠ 0`. -/
theorem vecU8At_expose (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗
      (if cap = 0 then emp
       else A.live ptr cap.toNat 1 ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  unfold vecU8At vecHeader
  by_cases hcap : cap = 0
  · subst hcap
    by_cases hnil : bs = []
    · subst hnil
      simp only [↓reduceIte, pointsToBytes_nil, sepConj_emp]
      ac_rfl
    · have hfalse : ¬ (bs.length ≤ (0 : BitVec 64).toNat ∧
          (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0) := by
        rcases List.exists_cons_of_ne_nil hnil with ⟨_, _, rfl⟩
        simp
      apply Entails.antisymm
      · rw [← sepConj_assoc, sepConj_comm _ ⌜_⌝, sepConj_assoc]
        exact Entails.pure_left fun h => False.elim (hfalse h)
      · exact Entails.pure_left fun h => False.elim (hfalse h)
  · simp only [hcap, ↓reduceIte]
    ac_rfl

/-- Combine `(ptr ↦ₛ bs)` and spare capacity back into `if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat`. -/
theorem vecU8At_drop_buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) :
    (ptr ↦ₛ bs) ∗
      (if cap = 0 then emp
       else A.live ptr cap.toNat 1 ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ⊢
      (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  by_cases hc : cap = 0
  · subst hc
    have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hnil
    simp only [↓reduceIte, pointsToBytes_nil, sepConj_emp]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte]
    have hsplit := memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)
    rw [Nat.add_sub_of_le hle] at hsplit
    rw [hsplit]
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)))
    ac_rfl

/-! ## 4. `Vec<u8>` & `getResultAt` Construction Helpers -/

theorem vecU8_of_zero (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      vecU8 A v [] := by
  unfold vecU8 vecU8At vecHeader
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
  refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.le_refl, true_and, ↓reduceIte, sepConj_emp, sepConj_assoc]
  rw [show (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
        ⌜(0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ =
      ⌜(0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ ∗
        ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) by ac_rfl]
  exact Entails.pure_right ⟨by decide, by decide⟩ (Entails.refl _)

theorem vecU8_of_pos (A : RustAlloc) (v p' : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hp' : p' ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      A.live p' bs.length 1 ∗ (p' ↦ₛ bs) ⊢
      vecU8 A v bs := by
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    change bs.length = 0 at ht
    omega
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold vecU8 vecU8At vecHeader
  refine Entails.trans ?_ (Entails.sepExists_intro (BitVec.ofNat 64 bs.length))
  refine Entails.trans ?_ (Entails.sepExists_intro p')
  simp only [hne0, htoNat, Nat.le_refl, hlt, ↓reduceIte,
    Nat.sub_self, memRegion_zero, sepConj_emp, sepConj_assoc]
  rw [show (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ⌜True ∧ True ∧ p' ≠ 0⌝ ∗
        A.live p' bs.length 1 ∗ (p' ↦ₛ bs) =
      ⌜True ∧ True ∧ p' ≠ 0⌝ ∗ ((v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live p' bs.length 1 ∗ (p' ↦ₛ bs)) by ac_rfl]
  exact Entails.pure_right ⟨trivial, trivial, hp'⟩ (Entails.refl _)

theorem memRegion_48_split6 (r : BitVec 64) :
    memRegion r 48 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
       ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        (r ↦₆₄ w5) ∗ ((r + 8#64) ↦₆₄ w4) ∗ ((r + 16#64) ↦₆₄ w3) ∗
        ((r + 24#64) ↦₆₄ w2) ∗ ((r + 32#64) ↦₆₄ w1) ∗ ((r + 40#64) ↦₆₄ w0)) := by
  rw [memRegion_split r 8 40 (by decide),
      memRegion_split (r + 8#64) 8 32 (by decide),
      memRegion_split (r + 8#64 + 8#64) 8 24 (by decide),
      memRegion_split (r + 8#64 + 8#64 + 8#64) 8 16 (by decide),
      memRegion_split (r + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
      ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem getResultAt_ok_of_vec (A : RustAlloc) (r w4 w5 : BitVec 64)
    (bs : List (BitVec 8)) :
    (r ↦₆₄ 0xfffffffffffffffe#64) ∗ vecU8 A (r + 8#64) bs ∗
      ((r + 32#64) ↦₆₄ w4) ∗ ((r + 40#64) ↦₆₄ w5) ⊢
      getResultAt A r (.ok bs) := by
  dsimp only [getResultAt, vecResultAt]
  have h16 : ((r + 32#64) ↦₆₄ w4) ∗ ((r + 40#64) ↦₆₄ w5) ⊢ memRegion (r + 32#64) 16 := by
    rw [memRegion_split (r + 32#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
  have htag : (0xfffffffffffffffe#64 : BitVec 64) = okTagVec := rfl
  rw [htag]
  refine Entails.trans (Entails.of_eq ?_)
    (sepConj_mono_right (sepConj_mono_right h16))
  ac_rfl

theorem getResultAt_err_of_ro (A : RustAlloc) (r buf pRead : BitVec 64)
    (errBs : List (BitVec 8))
    (hlen : errBs.length = 22) (hbuf : buf ≠ 0#64) :
    (r ↦₆₄ 9223372036854775809#64) ∗ ((r + 8#64) ↦₆₄ 22#64) ∗
      ((r + 16#64) ↦₆₄ buf) ∗ ((r + 24#64) ↦₆₄ 22#64) ∗
      ((r + 32#64) ↦₆₄ pRead) ∗ ((r + 40#64) ↦₆₄ 4#64) ∗
      A.live buf 22 1 ∗ (buf ↦ₛ errBs) ∗ (pRead ↦ᵣ utf8 "read") ⊢
      getResultAt A r (.error ()) := by
  dsimp only [getResultAt, speAt]
  have hv0 := vecU8_of_pos A (r + 8#64) buf errBs (by omega) (by omega) hbuf
  simp only [hlen, BitVec.add_assoc, BitVec.reduceAdd] at hv0
  have hv : ((r + 8#64) ↦₆₄ 22#64) ∗ ((r + 16#64) ↦₆₄ buf) ∗ ((r + 24#64) ↦₆₄ 22#64) ∗
      A.live buf 22 1 ∗ (buf ↦ₛ errBs) ⊢
      (∃∗ bs : List (BitVec 8), vecU8 A (r + 8#64) bs) :=
    Entails.trans hv0 (Entails.sepExists_intro errBs)
  have hstr : ((r + 32#64) ↦₆₄ pRead) ∗ ((r + 40#64) ↦₆₄ 4#64) ∗ (pRead ↦ᵣ utf8 "read") ⊢
      strRefAt (r + 32#64) (utf8 "read") := by
    unfold strRefAt
    refine Entails.trans ?_ (Entails.sepExists_intro pRead)
    rw [utf8_read_length]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.refl _
  have htag : (9223372036854775809#64 : BitVec 64) = speWord 1 := rfl
  rw [htag]
  refine Entails.trans (Entails.of_eq ?_)
    (sepConj_mono_right (sepConj_mono hv hstr))
  ac_rfl

/-! ## 5. Layout-Independent `.rodata` Bundle & `Obj.Loads` Witness -/

/-- Address of the 22-byte `"file could not be read"` `.rodata` slice relative to `b`. -/
abbrev unreadableStrAddr (b : BitVec 64) : BitVec 64 :=
  b + bv% (ls_xref%
    (ls_off% "<libsignal_cli::stores::Dir>::get" + 400)
    (ls_off% "<libsignal_cli::stores::Dir>::get" + 404))

/-- Address of the 4-byte `"read"` `.rodata` slice relative to `b`. -/
abbrev readOpStrAddr (b : BitVec 64) : BitVec 64 :=
  b + bv% (ls_xref%
    (ls_off% "<libsignal_cli::stores::Dir>::get" + 444)
    (ls_off% "<libsignal_cli::stores::Dir>::get" + 448))

/-- Read-only spatial bundle carried across `Dir::get`. -/
def dirGetRoBundle (b : BitVec 64) (w0 w1 wTail : BitVec 64) : SepProp :=
  ((unreadableStrAddr b) ↦₆₄ᵣ w0) ∗
  ((unreadableStrAddr b + 8#64) ↦₆₄ᵣ w1) ∗
  ((unreadableStrAddr b + 14#64) ↦₆₄ᵣ wTail) ∗
  ((readOpStrAddr b) ↦ᵣ utf8 "read")

/-- Minimal `.rodata` assumption needed by `<signal_session::stores::Dir>::get`:
    any `img.FrozenLoaded` state holds the three 64-bit read-only words read at `+412/+416`
    and the 4-byte `"read"` literal referenced at `+444/+448`. -/
def DirGetRoData (img : Obj.Image) : Prop :=
  ∀ {s : State} {P : SepProp},
    img.FrozenLoaded s → (s.mem ⊨ P) →
    ∃ w0 w1 wTail : BitVec 64,
      s.mem ⊨ dirGetRoBundle img.base w0 w1 wTail ∗ P

/-! ## 6. Layout-Independent `ADRP + ADD` Resolution for `+400` and `+444` -/

theorem adrp_add_unreadable_eq {b fnStart : BitVec 64}
    (hb : (b &&& 0xfff#64) = 0#64)
    (he : fnStart = b + bv% (ls_off% "<libsignal_cli::stores::Dir>::get")) :
    (((fnStart + 400#64) &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_xref%
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 400)
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 404)) -
           page% (ls_off% "<libsignal_cli::stores::Dir>::get" + 400))) +
      bv% (ls_xref%
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 400)
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 404) % 4096) =
    unreadableStrAddr b := by
  subst he
  have hpage :
      ((bv% (ls_off% "<libsignal_cli::stores::Dir>::get") + 400#64 : BitVec 64) &&&
        0xfffffffffffff000#64) =
      bv% (page% (ls_off% "<libsignal_cli::stores::Dir>::get" + 400)) := by decide
  have hsum :
      bv% (page% (ls_off% "<libsignal_cli::stores::Dir>::get" + 400)) +
      bv% (page% (ls_xref%
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 400)
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 404)) -
           page% (ls_off% "<libsignal_cli::stores::Dir>::get" + 400)) +
      bv% (ls_xref%
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 400)
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 404) % 4096) =
      bv% (ls_xref%
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 400)
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 404)) := by decide
  rw [BitVec.add_assoc b, ProofLib.ObjectLoad.adrp_page_of_aligned hb, hpage]
  unfold unreadableStrAddr
  rw [← hsum]
  bv_omega

theorem adrp_add_readOp_eq {b fnStart : BitVec 64}
    (hb : (b &&& 0xfff#64) = 0#64)
    (he : fnStart = b + bv% (ls_off% "<libsignal_cli::stores::Dir>::get")) :
    (((fnStart + 444#64) &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_xref%
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 444)
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 448)) -
           page% (ls_off% "<libsignal_cli::stores::Dir>::get" + 444))) +
      bv% (ls_xref%
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 444)
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 448) % 4096) =
    readOpStrAddr b := by
  subst he
  have hpage :
      ((bv% (ls_off% "<libsignal_cli::stores::Dir>::get") + 444#64 : BitVec 64) &&&
        0xfffffffffffff000#64) =
      bv% (page% (ls_off% "<libsignal_cli::stores::Dir>::get" + 444)) := by decide
  have hsum :
      bv% (page% (ls_off% "<libsignal_cli::stores::Dir>::get" + 444)) +
      bv% (page% (ls_xref%
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 444)
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 448)) -
           page% (ls_off% "<libsignal_cli::stores::Dir>::get" + 444)) +
      bv% (ls_xref%
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 444)
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 448) % 4096) =
      bv% (ls_xref%
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 444)
            (ls_off% "<libsignal_cli::stores::Dir>::get" + 448)) := by decide
  rw [BitVec.add_assoc b, ProofLib.ObjectLoad.adrp_page_of_aligned hb, hpage]
  unfold readOpStrAddr
  rw [← hsum]
  bv_omega

/-! ## 7. Writable 22-Byte Overlap Decomposition (`[0..16)` + `[14..22)`) -/

theorem write_22_overlap_mid (buf w1 : BitVec 64) :
    ((buf + 8#64) ↦₆₄ w1) ∗ memRegion (buf + 16#64) 6 ⊢
      ((buf + 8#64) ↦ₛ (unpack64 w1).take 6) ∗ memRegion (buf + 14#64) 8 := by
  have h1 : (unpack64 w1).length = 8 := unpack64_length w1
  have h6 : ((unpack64 w1).take 6).length = 6 := by simp [h1]
  have h2 : ((unpack64 w1).drop 6).length = 2 := by simp [h1]
  rw [pointsTo64_eq_pointsToBytes, ← List.take_append_drop 6 (unpack64 w1),
      pointsToBytes_append, h6]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine sepConj_mono_right ?_
  rw [memRegion_split (buf + 14#64) 2 6 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono
    (by have := pointsToBytes_entails_memRegion (buf + 14#64) ((unpack64 w1).drop 6)
        rwa [h2] at this)
    (Entails.refl _)

theorem write_22_overlap_done (buf w0 w1 wTail : BitVec 64) :
    (buf ↦₆₄ w0) ∗ ((buf + 8#64) ↦ₛ (unpack64 w1).take 6) ∗ ((buf + 14#64) ↦₆₄ wTail) ⊢
      (buf ↦ₛ (unpack64 w0 ++ (unpack64 w1).take 6 ++ unpack64 wTail)) := by
  have h0 : (unpack64 w0).length = 8 := unpack64_length w0
  have h6 : ((unpack64 w1).take 6).length = 6 := by simp [unpack64_length]
  rw [List.append_assoc, pointsToBytes_append, h0, pointsToBytes_append, h6,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

/-! ## 8. `arrayAt` Prefix/Suffix Split & Non-I/O Callee Relocation Helpers -/

theorem arrayAt_dirEntry_append (A : RustAlloc) (ptr : BitVec 64)
    (pre suf : List (List (BitVec 8) × List (BitVec 8))) :
    RustHeap.arrayAt (dirEntryAt A) 48 ptr (pre ++ suf) =
      RustHeap.arrayAt (dirEntryAt A) 48 ptr pre ∗
        RustHeap.arrayAt (dirEntryAt A) 48 (ptr + BitVec.ofNat 64 (48 * pre.length)) suf := by
  induction pre generalizing ptr with
  | nil =>
    simp [RustHeap.arrayAt]
  | cons hd tl ih =>
    simp only [List.cons_append, RustHeap.arrayAt, ih, List.length_cons, sepConj_assoc]
    have hmul : ptr + 48#64 + BitVec.ofNat 64 (48 * tl.length) =
        ptr + BitVec.ofNat 64 (48 * (tl.length + 1)) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
      omega
    rw [hmul]

theorem fnAddr_add_rel {b : BitVec 64} {ext : String → Option (State → State)}
    (n1 n2 : String) {k : Nat}
    (hk : libsignalSessionCode.fnOff n1 + k = libsignalSessionCode.fnOff n2) :
    (tripleRatchetProgAtExt b ext).fnAddr n1 + BitVec.ofNat 64 k =
      (tripleRatchetProgAtExt b ext).fnAddr n2 := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, hk]

ls_attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

theorem bcmp_ok_at {b : BitVec 64} {ext : String → Option (State → State)}
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dirGetName +
        bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "bcmp"))
      cliBcmpSpec :=
  hook_ok_at (hname := cliBcmpName) rfl
    (k := ls_rel% "<libsignal_cli::stores::Dir>::get" "bcmp")
    (by rw [dirGet_fnOff, ls_lemma% stubOff "bcmp"])
    (by rw [ls_lemma% stubOff "bcmp"]; decide)
    (fun H => Eq.trans (congrArg (libsignalSessionCode.rebase 0 H).hookAtOff?
        (ls_lemma% stubOff "bcmp"))
      (ls_lemma% hookAtOff "bcmp" H))
    (by decide +kernel) hBcmp

theorem path_ok_at {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {pathStk : Nat}
    (hPath : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img pathStk)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName +
        bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "libsignal_cli::stores::path"))
      (pathSpec A img pathStk) := by
  rw [fnAddr_add_rel dirGetName pathName (by rw [dirGet_fnOff, path_fnOff])]
  exact hPath

theorem sessionMemcpyBytesAtInImage_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec)
    (ro : Bool) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName +
        bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "memcpy"))
      ((withStack (sessionMemcpyBytesAtSpec ro) extHookStack).inImage img) := by
  cases ro
  · have hmc := hC.session_memcpy_region_ok_at dirGetName
      (ls_rel% "<libsignal_cli::stores::Dir>::get" "memcpy")
      (hk := by rw [dirGet_fnOff]; simp only [arm64_norm])
    refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp => ?_
    have hpre' : s0.mem ⊨ ((withStack sessionMemcpyRegionSpec extHookStack).inImage img).pre
        (dst, src, bs) s0 ∗ R := by
      simp only [Spec.inImage, withStack, sessionMemcpyBytesAtSpec,
        SpqrV1.ChainProofs.bytesAt_false, sessionMemcpyRegionSpec, memcpyRegionSpec,
        sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      exact ⟨hpre.1, ⟨hpre.2.1.1, hpre.2.1.2.1, hpre.2.1.2.2.1⟩, hpre.2.2⟩
    exact hmc.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hsp fun _ hout => hout
  · have hmc_ro := session_memcpy_region_ro_ok_at (b := img.base) hRO dirGetName
      (ls_rel% "<libsignal_cli::stores::Dir>::get" "memcpy")
      (hk := by rw [dirGet_fnOff]; simp only [arm64_norm])
    exact subroutine_ok_inImage_of_subroutine_ok img
      (subroutine_ok_withStack_of_subroutine_ok hmc_ro extHookStack)

theorem sessionMemcpyBytesAtInImage_ok_at_false {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName +
        bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "memcpy"))
      ((withStack (sessionMemcpyBytesAtSpec false) extHookStack).inImage img) := by
  have hmc := hC.session_memcpy_region_ok_at dirGetName
    (ls_rel% "<libsignal_cli::stores::Dir>::get" "memcpy")
    (hk := by rw [dirGet_fnOff]; simp only [arm64_norm])
  refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ ((withStack sessionMemcpyRegionSpec extHookStack).inImage img).pre
      (dst, src, bs) s0 ∗ R := by
    simp only [Spec.inImage, withStack, sessionMemcpyBytesAtSpec,
      SpqrV1.ChainProofs.bytesAt_false, sessionMemcpyRegionSpec, memcpyRegionSpec,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨hpre.1, ⟨hpre.2.1.1, hpre.2.1.2.1, hpre.2.1.2.2.1⟩, hpre.2.2⟩
  exact hmc.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hsp fun _ hout => hout

theorem memcpyROOkExtX_of_withStack {img : Obj.Image}
    {ext : String → Option (State → State)} {roStk : Nat}
    (hro : roStk ≤ extHookStack)
    (hRO : HookSat ext memcpyName (sessionMemcpyRegionROSpecWithStack roStk)) :
    MemcpyROOkExtX img ext := by
  have hfn : libsignalSessionCode.fnOff memcpyName = num% (ls_off% "memcpy") :=
    Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "memcpy")
  have h0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName)
      (sessionMemcpyRegionROSpecWithStack roStk) := by
    have h := ProofLib.hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := ext)
      (name := memcpyName) (hname := memcpyName) (k := 0)
      hfn (Nat.add_zero _) (by decide) (ls_hook% "memcpy")
      (by simp [Rust.isPanicSymbol, memcpyName]) hRO
    simpa only [tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  have hlt : extHookStack ≤ 2 ^ 64 := by decide
  let btm := fun sp => memRegion (sp - BitVec.ofNat 64 extHookStack) (extHookStack - roStk)
  apply SpqrV1.Alloc.subroutine_ok_inImage img
  refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ (sessionMemcpyRegionROSpecWithStack roStk).pre (dst, src, bs) s0 ∗
      (btm s0.sp ∗ R) := by
    dsimp only [sessionMemcpyRegionROSpecX, sessionMemcpyRegionROSpecWithStack, btm] at hpre ⊢
    rw [stackAt_sub_split s0.sp hro hlt] at hpre
    simp only [sepConj_assoc] at hpre ⊢
    rwa [← sepConj_assoc (memRegion _ _) (stackAt s0.sp roStk) R,
      sepConj_comm (memRegion _ _) (stackAt s0.sp roStk), sepConj_assoc] at hpre
  refine h0.mono_outcome (dst, src, bs) (btm s0.sp ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hmem⟩ | ⟨code, _, hmem⟩ | ⟨_, hmem⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionMemcpyRegionROSpecX, sessionMemcpyRegionROSpecWithStack, btm] at hpost ⊢
    rw [stackAt_sub_split s0.sp hro hlt]
    simp only [sepConj_assoc] at hpost ⊢
    rwa [← sepConj_assoc (stackAt s0.sp roStk) (memRegion _ _) R,
      sepConj_comm (stackAt s0.sp roStk) (memRegion _ _), sepConj_assoc] at hpost
  · rw [show (sessionMemcpyRegionROSpecWithStack roStk).onPanic (dst, src, bs) s0 sf = ⌜False⌝ from rfl,
      satisfies_pure_sepConj] at hmem
    exact False.elim hmem.1
  · rw [show (sessionMemcpyRegionROSpecWithStack roStk).onExit (dst, src, bs) code s0 sf = ⌜False⌝ from rfl,
      satisfies_pure_sepConj] at hmem
    exact False.elim hmem.1
  · rw [show (sessionMemcpyRegionROSpecWithStack roStk).onOom (dst, src, bs) s0 sf = ⌜False⌝ from rfl,
      satisfies_pure_sepConj] at hmem
    exact False.elim hmem.1

theorem sessionMemcpyBytesAtInImage_ok_at_roX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext)
    (hRO : MemcpyROOkExtX img ext)
    (ro : Bool) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName +
        bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "memcpy"))
      ((withStack (sessionMemcpyBytesAtSpec ro) extHookStack).inImage img) := by
  cases ro
  · exact sessionMemcpyBytesAtInImage_ok_at_false hC
  · have hmc_ro := session_memcpy_region_ro_ok_at_x_of_roX hRO dirGetName
      (ls_rel% "<libsignal_cli::stores::Dir>::get" "memcpy")
      (hk := by rw [dirGet_fnOff]; simp only [arm64_norm])
    refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp => ?_
    have hpre' : s0.mem ⊨ (sessionMemcpyRegionROSpecX.inImage img).pre (dst, src, bs) s0 ∗ R := by
      simpa only [Spec.inImage, withStack, sessionMemcpyBytesAtSpec,
        sessionMemcpyRegionROSpecX, SpqrV1.ChainProofs.bytesAt_true, sepConj_assoc] using hpre
    refine hmc_ro.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simpa only [Spec.inImage, withStack, sessionMemcpyBytesAtSpec,
        sessionMemcpyRegionROSpecX, SpqrV1.ChainProofs.bytesAt_true, sepConj_assoc] using hpost
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr hex)

theorem sessionMemcpyBytesAtInImage_ok_at_withStack {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {roStk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName (sessionMemcpyRegionROSpecWithStack roStk))
    (ro : Bool)
    (hro : roStk ≤ extHookStack := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName +
        bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "memcpy"))
      ((withStack (sessionMemcpyBytesAtSpec ro) extHookStack).inImage img) :=
  sessionMemcpyBytesAtInImage_ok_at_roX hC (memcpyROOkExtX_of_withStack hro hRO) ro

theorem panic_at_handle_error_dirGet (b : BitVec 64) (ext : String → Option (State → State)) :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).externAt?
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dirGetName +
        bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "alloc::raw_vec::handle_error")) =
      some Rust.panicked :=
  panic_at_handle_error_ext b ext dirGetName
    (ls_rel% "<libsignal_cli::stores::Dir>::get" "alloc::raw_vec::handle_error")
    (by rw [dirGet_fnOff]; simp only [arm64_norm])

/-- Abstract post-call contract for the `+0x14c` → `+0x150` `read_file` call site. -/
def PathIoContract (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (ioStk : Nat) : Prop :=
  ∀ (s0 s : State) (pathPtr : BitVec 64) (pth : List (BitVec 8)) (F : SepProp)
    (Q : State → SepProp → Prop) (Qp : State → SepProp → Prop),
    let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
    let fnStart := prog.fnAddr dirGetName
    img.FrozenLoaded s →
    s.symtab = img.symtab →
    s.pc = fnStart + 332#64 →
    s.status = .Running →
    s.spAligned = true →
    FsInv s0.fs.files s0.trace s →
    s.trace = s0.trace →
    s.readReg64 .x0 = pathPtr →
    (s.readReg64 .x1).toNat = pth.length →
    s.readReg64 .x8 = s.sp →
    pth.length < 2 ^ 32 →
    pathOk pth →
    (∀ (sc sf : State) (F' : SepProp), sc.trace = s0.trace →
      Qp sf ((⌜allocFailedIn sc sf ∧ sc.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F')) →
    (∀ sf : State,
      sf.pc = fnStart + 336#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      SepWPp prog (s0.readReg64 .x30) sf
        (((∃∗ r : Except Unit (List (BitVec 8)),
            ⌜r = rd s0.fs.files pth ∧ sf.trace = s0.trace⌝ ∗
            ioVecAt A s.sp r) ∗
          (pathPtr ↦ₛ pth) ∗ stackAt s.sp ioStk ∗ A.pool) ∗ F)
        Q Qp (fun _ => ⌜False⌝)) →
    SepWPp prog (s0.readReg64 .x30) s
      (((pathPtr ↦ₛ pth) ∗ memRegion s.sp 24 ∗ stackAt s.sp ioStk ∗ A.pool) ∗ F)
      Q Qp (fun _ => ⌜False⌝)

end CryptoVerification.SignalSession.Cli.Get.Helpers

