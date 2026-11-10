/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp

/-!
# Prologue (`+0x000..+0x0f0`), epilogue (`+0x440..+0x45c`), and loop composition for `SignalMessage::try_from`
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Wire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "tryFrom_fetches2 " b:term:max _C:term:max _ctl:term:max abs:term:max
    k0:num len:num : tactic =>
  `(tactic| tryFrom_fetches $b (Rust.withPanics $abs) $k0 $len)

/-- State invariant at the shared epilogue entry `+0x440` (`0x25ca8`, `entry + 1088#64`). -/
def EpilogueState (img : Obj.Image) (s0 : State) (sp' : BitVec 64) (s : State) : Prop :=
  s.sp = sp' ∧ s.spAligned = true ∧ img.FrozenLoaded s ∧ s.symtab = img.symtab ∧ s.trace = s0.trace

theorem EpilogueState.of_steps {img : Obj.Image} {s0 s1 s2 : State} {sp' : BitVec 64}
    (hF : img.FrozenLoaded s2) (hsym : s2.symtab = img.symtab)
    (hsp : s2.sp = sp') (hsp0 : s1.sp = sp') (hal : s1.spAligned = true)
    (htr : s2.trace = s0.trace) :
    EpilogueState img s0 sp' s2 := by
  refine ⟨hsp, ?_, hF, hsym, htr⟩
  rw [State.spAligned, hsp, ← hsp0, ← State.spAligned]
  exact hal

theorem spAligned_sub448 {s0 : State} (hsp0 : s0.spAligned = true) :
    ((s0.sp - 448#64) &&& 15#64 == 0#64) = true := by
  rw [State.spAligned] at hsp0
  revert hsp0
  generalize s0.sp = sp
  intro hsp0
  bv_kernel

/-- Saved callee-saved registers and FP/LR at `sp' + 352 .. sp' + 448` (96 bytes). -/
def calleeSavedAt (sp' : BitVec 64) (s0 : State) : SepProp :=
  ((sp' + 352#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp' + 360#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp' + 368#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp' + 376#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp' + 384#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp' + 392#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp' + 400#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp' + 408#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp' + 416#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp' + 424#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp' + 432#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp' + 440#64) ↦₆₄ s0.readReg64 .x19)

theorem calleeSavedAt_entails_memRegion96 (sp' : BitVec 64) (s0 : State) :
    calleeSavedAt sp' s0 ⊢ memRegion (sp' + 352#64) 96 := by
  unfold calleeSavedAt
  rw [show (96 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + 8)))))))))) by decide,
    memRegion_split (sp' + 352#64) 8 88 (by decide),
    memRegion_split (sp' + 352#64 + 8#64) 8 80 (by decide),
    memRegion_split (sp' + 352#64 + 8#64 + 8#64) 8 72 (by decide),
    memRegion_split (sp' + 352#64 + 8#64 + 8#64 + 8#64) 8 64 (by decide),
    memRegion_split (sp' + 352#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 56 (by decide),
    memRegion_split (sp' + 352#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
    memRegion_split (sp' + 352#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    memRegion_split (sp' + 352#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    memRegion_split (sp' + 352#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    memRegion_split (sp' + 352#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (sp' + 352#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (pointsTo64_entails_memRegion _ _)
                      (sepConj_mono (pointsTo64_entails_memRegion _ _)
                        (pointsTo64_entails_memRegion _ _)))))))))))

theorem memRegion96_cells (sp' : BitVec 64) :
    memRegion (sp' + 352#64) 96 ⊢
      ∃∗ w19 : BitVec 64, ∃∗ w20 : BitVec 64, ∃∗ w21 : BitVec 64, ∃∗ w22 : BitVec 64,
      ∃∗ w23 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w25 : BitVec 64, ∃∗ w26 : BitVec 64,
      ∃∗ w27 : BitVec 64, ∃∗ w28 : BitVec 64, ∃∗ w30 : BitVec 64, ∃∗ w29 : BitVec 64,
        ((sp' + 352#64) ↦₆₄ w29) ∗ ((sp' + 360#64) ↦₆₄ w30) ∗
        ((sp' + 368#64) ↦₆₄ w28) ∗ ((sp' + 376#64) ↦₆₄ w27) ∗
        ((sp' + 384#64) ↦₆₄ w26) ∗ ((sp' + 392#64) ↦₆₄ w25) ∗
        ((sp' + 400#64) ↦₆₄ w24) ∗ ((sp' + 408#64) ↦₆₄ w23) ∗
        ((sp' + 416#64) ↦₆₄ w22) ∗ ((sp' + 424#64) ↦₆₄ w21) ∗
        ((sp' + 432#64) ↦₆₄ w20) ∗ ((sp' + 440#64) ↦₆₄ w19) := by
  rw [show (96 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + 8)))))))))) by decide,
    memRegion_split (sp' + 352#64) 8 88 (by decide),
    memRegion_split (sp' + 352#64 + 8#64) 8 80 (by decide),
    memRegion_split (sp' + 352#64 + 8#64 + 8#64) 8 72 (by decide),
    memRegion_split (sp' + 352#64 + 8#64 + 8#64 + 8#64) 8 64 (by decide),
    memRegion_split (sp' + 352#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 56 (by decide),
    memRegion_split (sp' + 352#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
    memRegion_split (sp' + 352#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    memRegion_split (sp' + 352#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    memRegion_split (sp' + 352#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    memRegion_split (sp' + 352#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (sp' + 352#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight,
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight,
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

/-- Remaining stack below `sp' = sp - 448` inside `smallRootStack` (`65536 - 448 = 65088`). -/
abbrev tryFromSubStack : Nat := smallRootStack - 448

theorem stackAt_smallRoot_split (sp : BitVec 64) :
    stackAt sp smallRootStack =
      stackAt (sp - 448#64) tryFromSubStack ∗
        memRegion (sp - 448#64) 352 ∗ memRegion (sp - 448#64 + 352#64) 96 := by
  have h1 := stackAt_sub_split sp 448 smallRootStack (by decide) (by decide)
  have h2 : memRegion (sp - BitVec.ofNat 64 smallRootStack) tryFromSubStack =
      stackAt (sp - 448#64) tryFromSubStack := by
    unfold stackAt
    have ha : sp - BitVec.ofNat 64 smallRootStack =
        sp - 448#64 - BitVec.ofNat 64 tryFromSubStack := by
      change sp - 65536#64 = sp - 448#64 - 65088#64
      bv_omega
    rw [ha]
  have h3 : stackAt sp 448 =
      memRegion (sp - 448#64) 352 ∗ memRegion (sp - 448#64 + 352#64) 96 := by
    unfold stackAt
    exact memRegion_split (sp - 448#64) 352 96 (by decide)
  rw [h1, h2, h3]

theorem stackAt_smallRoot_unsplit (sp : BitVec 64) (s0 : State) :
    stackAt (sp - 448#64) tryFromSubStack ∗
      memRegion (sp - 448#64) 352 ∗ calleeSavedAt (sp - 448#64) s0 ⊢
      stackAt sp smallRootStack := by
  rw [stackAt_smallRoot_split sp]
  exact sepConj_mono_right (sepConj_mono_right (calleeSavedAt_entails_memRegion96 (sp - 448#64) s0))

/-- Epilogue `+0x440..+0x45c` (`1088..1116` → `s0.readReg64 .x30`): restores `x19..x30`,
adds `448` to `sp`, and executes `ret`. -/
theorem epilogue_440_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    {x : TryFromGhost} {s0 s : State}
    (hst : EpilogueState img s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x440#64)
    (hrun : s.status = .Running) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      (s0.readReg64 .x30) s
      (stackAt (s0.sp - 448#64) tryFromSubStack ∗
        memRegion (s0.sp - 448#64) 352 ∗
        calleeSavedAt (s0.sp - 448#64) s0 ∗
        signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
        (x.bytesA ↦ₛ x.bytes) ∗ logOff img ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (tryFromSpec A img).post x s0 sf))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  unfold calleeSavedAt
  simp only [sepConj_assoc]
  tryFrom_fetches2 img.base C ctl abs 1088 32
  generalize_entry (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨by simp [arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], hv⟩
  · dsimp only [tryFromSpec, Spec.inImage]
    rw [pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
    have hstk := stackAt_smallRoot_unsplit s0.sp s0
    unfold calleeSavedAt at hstk
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk))))
    apply entails_of_eq
    ac_rfl

/-! ## Error result intro lemmas for prologue and `len = 9` fast paths -/

theorem memRegion120_split24 (x19 : BitVec 64) :
    memRegion x19 120 ⊢
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ ((x19 + 16#64) ↦₆₄ w2) ∗
          memRegion (x19 + 24#64) 96 := by
  rw [show (120 : Nat) = 8 + (8 + (8 + 96)) by decide,
    memRegion_split x19 8 112 (by decide),
    memRegion_split (x19 + 8#64) 8 104 (by decide),
    memRegion_split (x19 + 8#64 + 8#64) 8 96 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem memRegion120_split17 (x19 : BitVec 64) :
    memRegion x19 120 ⊢
      ∃∗ b16 : BitVec 8, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ ((x19 + 16#64) ↦₈ b16) ∗
          memRegion (x19 + 17#64) 103 := by
  rw [show (120 : Nat) = 8 + (8 + (1 + 103)) by decide,
    memRegion_split x19 8 112 (by decide),
    memRegion_split (x19 + 8#64) 8 104 (by decide),
    memRegion_split (x19 + 8#64 + 8#64) 1 103 (by decide),
    memRegion_eight, memRegion_eight, memRegion_one]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem spe_tooShort_intro (A : RustAlloc) (x19 : BitVec 64) (n : Nat)
    {out : Except SignalProtocolError SignalMessage}
    (herr : out = .error (.ciphertextMessageTooShort n)) :
    (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 3) ∗
      ((x19 + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (x19 + 24#64) 96 ⊢
      signalMessageResultAt A [] x19 out := by
  rw [herr]
  dsimp only [signalMessageResultAt, errResultAt, speAt]
  have h64 : (120 : Nat) - 56 = 64 := rfl
  have ha16 : x19 + 8#64 + 8#64 = x19 + 16#64 := by bv_omega
  have ha24 : x19 + 8#64 + 16#64 = x19 + 24#64 := by bv_omega
  have h96 : memRegion (x19 + 24#64) 96 =
      memRegion (x19 + 24#64) 32 ∗ memRegion (x19 + 56#64) 64 := by
    have hs := memRegion_split (x19 + 24#64) 32 64 (by decide)
    have ha : x19 + 24#64 + 32#64 = x19 + 56#64 := by bv_omega
    rw [← ha]; exact hs
  rw [h64, ha16, ha24, h96]
  apply entails_of_eq; ac_rfl

theorem spe_legacyVer_intro (A : RustAlloc) (x19 : BitVec 64) (v : BitVec 8)
    {out : Except SignalProtocolError SignalMessage}
    (herr : out = .error (.legacyCiphertextVersion v)) :
    (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 4) ∗
      ((x19 + 16#64) ↦₈ v) ∗ memRegion (x19 + 17#64) 103 ⊢
      signalMessageResultAt A [] x19 out := by
  rw [herr]
  dsimp only [signalMessageResultAt, errResultAt, speAt]
  have h64 : (120 : Nat) - 56 = 64 := rfl
  have ha16 : x19 + 8#64 + 8#64 = x19 + 16#64 := by bv_omega
  have ha17 : x19 + 8#64 + 9#64 = x19 + 17#64 := by bv_omega
  have h103 : memRegion (x19 + 17#64) 103 =
      memRegion (x19 + 17#64) 39 ∗ memRegion (x19 + 56#64) 64 := by
    have hs := memRegion_split (x19 + 17#64) 39 64 (by decide)
    have ha : x19 + 17#64 + 39#64 = x19 + 56#64 := by bv_omega
    rw [← ha]; exact hs
  rw [h64, ha16, ha17, h103]
  apply entails_of_eq; ac_rfl

theorem spe_unrecognizedVer_intro (A : RustAlloc) (x19 : BitVec 64) (v : BitVec 8)
    {out : Except SignalProtocolError SignalMessage}
    (herr : out = .error (.unrecognizedCiphertextVersion v)) :
    (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 5) ∗
      ((x19 + 16#64) ↦₈ v) ∗ memRegion (x19 + 17#64) 103 ⊢
      signalMessageResultAt A [] x19 out := by
  rw [herr]
  dsimp only [signalMessageResultAt, errResultAt, speAt]
  have h64 : (120 : Nat) - 56 = 64 := rfl
  have ha16 : x19 + 8#64 + 8#64 = x19 + 16#64 := by bv_omega
  have ha17 : x19 + 8#64 + 9#64 = x19 + 17#64 := by bv_omega
  have h103 : memRegion (x19 + 17#64) 103 =
      memRegion (x19 + 17#64) 39 ∗ memRegion (x19 + 56#64) 64 := by
    have hs := memRegion_split (x19 + 17#64) 39 64 (by decide)
    have ha : x19 + 17#64 + 39#64 = x19 + 56#64 := by bv_omega
    rw [← ha]; exact hs
  rw [h64, ha16, ha17, h103]
  apply entails_of_eq; ac_rfl

/-! ## Condition-flag and bitfield helpers for the prologue -/

theorem cond_hi_len_of_lt9 {n : Nat} (hlt9 : n < 9) :
    ConditionHolds .HI (subsPState64 (BitVec.ofNat 64 n) 8#64) = false := by
  have hle : BitVec.ofNat 64 n ≤ 8#64 := by
    rw [BitVec.le_def]
    have h1 : (BitVec.ofNat 64 n).toNat = n := Nat.mod_eq_of_lt (by omega)
    have h2 : (8#64 : BitVec 64).toNat = 8 := rfl
    omega
  unfold ConditionHolds subsPState64 AddWithCarry64
  dsimp only
  bv_kernel

theorem cond_hi_len_of_ge9 {n : Nat} (hge9 : 9 ≤ n) (hlt : n < 2 ^ 63) :
    ConditionHolds .HI (subsPState64 (BitVec.ofNat 64 n) 8#64) = true := by
  have hgt : 8#64 < BitVec.ofNat 64 n := by
    rw [BitVec.lt_def]
    have h1 : (BitVec.ofNat 64 n).toNat = n := Nat.mod_eq_of_lt (by omega)
    have h2 : (8#64 : BitVec 64).toNat = 8 := rfl
    omega
  unfold ConditionHolds subsPState64 AddWithCarry64
  dsimp only
  bv_kernel

theorem cond_cs_ver_of_lt3 {b0 : BitVec 8} (h : (b0 >>> 4) < 3#8) :
    ConditionHolds .CS (subsPState32 (b0.zeroExtend 32) 48#32) = false := by
  unfold ConditionHolds subsPState32 AddWithCarry32
  dsimp only
  bv_kernel

theorem cond_cs_ver_of_ge3 {b0 : BitVec 8} (h : ¬ (b0 >>> 4) < 3#8) :
    ConditionHolds .CS (subsPState32 (b0.zeroExtend 32) 48#32) = true := by
  unfold ConditionHolds subsPState32 AddWithCarry32
  dsimp only
  bv_kernel

theorem cond_ls_ver_of_gt4 {b0 : BitVec 8} (h : 4#8 < (b0 >>> 4)) :
    ConditionHolds .LS (subsPState32 (b0.zeroExtend 32) 79#32) = false := by
  unfold ConditionHolds subsPState32 AddWithCarry32
  dsimp only
  bv_kernel

theorem cond_ls_ver_of_le4 {b0 : BitVec 8} (h : ¬ 4#8 < (b0 >>> 4)) :
    ConditionHolds .LS (subsPState32 (b0.zeroExtend 32) 79#32) = true := by
  unfold ConditionHolds subsPState32 AddWithCarry32
  dsimp only
  bv_kernel

theorem speWord2_add2 : (2#64 ||| 0x8000000000000000#64) + 2#64 = speWord 4 := by decide
theorem speWord2_add3 : (2#64 ||| 0x8000000000000000#64) + 3#64 = speWord 5 := by decide

theorem tryFrom_eq_tooShort {bs : List (BitVec 8)} (hlt9 : bs.length < 9) :
    SignalMessage.tryFrom protoSignalCodec bs =
      .error (.ciphertextMessageTooShort bs.length) := by
  have hlt : bs.length < macLength + 1 := hlt9
  simp [SignalMessage.tryFrom, hlt, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

theorem tryFrom_eq_legacyVer {b0 : BitVec 8} {rest : List (BitVec 8)}
    (hge9 : 9 ≤ (b0 :: rest).length) (hlt3 : (b0 >>> 4) < 3#8) :
    SignalMessage.tryFrom protoSignalCodec (b0 :: rest) =
      .error (.legacyCiphertextVersion (b0 >>> 4)) := by
  have hle : macLength ≤ rest.length := by
    change 8 ≤ rest.length
    simp at hge9
    omega
  have hv : (b0 >>> 4) < preKyberVersion := hlt3
  simp [SignalMessage.tryFrom, hle, hv, bind, Except.bind,
    throw, throwThe, MonadExceptOf.throw]

theorem tryFrom_eq_unrecognizedVer {b0 : BitVec 8} {rest : List (BitVec 8)}
    (hge9 : 9 ≤ (b0 :: rest).length) (hge3 : ¬ (b0 >>> 4) < 3#8) (hgt4 : 4#8 < (b0 >>> 4)) :
    SignalMessage.tryFrom protoSignalCodec (b0 :: rest) =
      .error (.unrecognizedCiphertextVersion (b0 >>> 4)) := by
  have hle : macLength ≤ rest.length := by
    change 8 ≤ rest.length
    simp at hge9
    omega
  have hv3 : ¬ (b0 >>> 4) < preKyberVersion := hge3
  have hv4 : currentVersion < (b0 >>> 4) := hgt4
  simp [SignalMessage.tryFrom, hle, hv3, hv4, bind, Except.bind,
    throw, throwThe, MonadExceptOf.throw]

theorem tryFrom_eq_len9 {bs : List (BitVec 8)} (hlen9 : bs.length = 9)
    (hge3 : ¬ ((bs.headD 0#8) >>> 4) < 3#8) (hle4 : ¬ 4#8 < ((bs.headD 0#8) >>> 4)) :
    SignalMessage.tryFrom protoSignalCodec bs = .error .invalidProtobufEncoding := by
  have hnotlt : ¬ bs.length < macLength + 1 := by
    change ¬ bs.length < 9
    omega
  have hv3 : ¬ ((bs.head?.getD 0#8) >>> 4) < preKyberVersion := by
    rw [← List.headD_eq_head?_getD]
    exact hge3
  have hv4 : ¬ currentVersion < ((bs.head?.getD 0#8) >>> 4) := by
    rw [← List.headD_eq_head?_getD]
    exact hle4
  have hsub : bs.length - macLength = 1 := by
    change bs.length - 8 = 1
    omega
  have hdrop : (bs.take 1).drop 1 = [] := by
    have hle : (bs.take 1).length ≤ 1 := List.length_take_le 1 bs
    exact List.drop_eq_nil_of_le hle
  have hdec : protoSignalCodec.decode [] = some emptyProtoSignalMessage := rfl
  have hrk : emptyProtoSignalMessage.ratchetKey = none := rfl
  unfold SignalMessage.tryFrom
  simp [hnotlt, hv3, hv4, hsub, hdrop, hdec, hrk,
    throw, throwThe, MonadExceptOf.throw]

/-! ## Prologue fast error path 1: `x.bytes.length < 9` (`+0x000..+0x040` → `+0x440`) -/

theorem prologue_tooShort_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    {x : TryFromGhost} {s0 : State}
    (hlt9 : x.bytes.length < 9)
    (hpc : s0.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (_hx0 : s0.readReg64 .x0 = x.bytesA)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x440#64) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ logOff img ∗
        stackAt s0.sp smallRootStack ∗ A.pool)
      (fun sf Pf => EpilogueState img s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ stackAt (s0.sp - 448#64) tryFromSubStack ∗
          memRegion (s0.sp - 448#64) 352 ∗
          calleeSavedAt (s0.sp - 448#64) s0 ∗
          signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff img ∗ A.pool))
      (tryFromQp s0) := by
  have hcond := cond_hi_len_of_lt9 hlt9
  have hout := tryFrom_eq_tooShort hlt9
  rw [stackAt_smallRoot_split s0.sp]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono (memRegion120_split24 x.ret)
      (sepConj_mono_right (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (memRegion96_cells (s0.sp - 448#64)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w19 => SepWPp.exists_pre fun w20 =>
    SepWPp.exists_pre fun w21 => SepWPp.exists_pre fun w22 =>
    SepWPp.exists_pre fun w23 => SepWPp.exists_pre fun w24 =>
    SepWPp.exists_pre fun w25 => SepWPp.exists_pre fun w26 =>
    SepWPp.exists_pre fun w27 => SepWPp.exists_pre fun w28 =>
    SepWPp.exists_pre fun w30 => SepWPp.exists_pre fun w29 =>
    SepWPp.exists_pre fun r2 => SepWPp.exists_pre fun r1 =>
    SepWPp.exists_pre fun r0 => ?_
  tryFrom_fetches2 img.base C ctl abs 0 68
  generalize_entry (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨⟨by simp [arm64_norm], ?_, hF1, hsym1, by simp [arm64_norm]⟩, ?_⟩
  · rw [State.spAligned]
    simpa [arm64_norm] using spAligned_sub448 hsp
  · have hmsg := spe_tooShort_intro A x.ret x.bytes.length hout
    simp only [errTag, speWord] at hmsg
    have hcs :
        ((s0.sp - 448#64 + 352#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 448#64 + 360#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 448#64 + 368#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
        ((s0.sp - 448#64 + 376#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
        ((s0.sp - 448#64 + 384#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
        ((s0.sp - 448#64 + 392#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 448#64 + 400#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 448#64 + 408#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 448#64 + 416#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 448#64 + 424#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 448#64 + 432#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 448#64 + 440#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
        calleeSavedAt (s0.sp - 448#64) s0 := Entails.refl _
    refine Entails.trans (Q := stackAt (s0.sp - 448#64) tryFromSubStack ∗
        memRegion (s0.sp - 448#64) 352 ∗
        (((s0.sp - 448#64 + 352#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 448#64 + 360#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 448#64 + 368#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
          ((s0.sp - 448#64 + 376#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
          ((s0.sp - 448#64 + 384#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
          ((s0.sp - 448#64 + 392#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
          ((s0.sp - 448#64 + 400#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
          ((s0.sp - 448#64 + 408#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
          ((s0.sp - 448#64 + 416#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((s0.sp - 448#64 + 424#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 448#64 + 432#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((s0.sp - 448#64 + 440#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) ∗
        ((x.ret ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
          ((x.ret + 8#64) ↦₆₄ 9223372036854775811#64) ∗
          ((x.ret + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          memRegion (x.ret + 24#64) 96) ∗
        (x.bytesA ↦ₛ x.bytes) ∗ logOff img ∗ A.pool)
      (by apply entails_of_eq; ac_rfl) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono hcs (sepConj_mono_left hmsg)))

/-! ## Prologue entry `+0x000..+0x02c` → `+0x044` when `9 ≤ x.bytes.length` -/

theorem prologue_entry_ge9_wp {img : Obj.Image} {C : Crypto}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    {x : TryFromGhost} {s0 : State}
    (hge9 : 9 ≤ x.bytes.length) (hlt : x.bytes.length < 2 ^ 63)
    (hpc : s0.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (hx0 : s0.readReg64 .x0 = x.bytesA)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x044#64) s0
      (memRegion (s0.sp - 448#64 + 352#64) 96)
      (fun s1 P1 =>
        EpilogueState img s0 (s0.sp - 448#64) s1 ∧
        s1.readReg64 .x0 = x.bytesA ∧
        s1.readReg64 .x19 = x.ret ∧
        s1.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧
        s1.readReg64 .x29 = s0.sp - 448#64 + 352#64 ∧
        (P1 ⊢ calleeSavedAt (s0.sp - 448#64) s0))
      (tryFromQp s0) := by
  have hcond := cond_hi_len_of_ge9 hge9 hlt
  refine SepWPp.mono_pre (memRegion96_cells (s0.sp - 448#64)) ?_
  refine SepWPp.exists_pre fun w19 => SepWPp.exists_pre fun w20 =>
    SepWPp.exists_pre fun w21 => SepWPp.exists_pre fun w22 =>
    SepWPp.exists_pre fun w23 => SepWPp.exists_pre fun w24 =>
    SepWPp.exists_pre fun w25 => SepWPp.exists_pre fun w26 =>
    SepWPp.exists_pre fun w27 => SepWPp.exists_pre fun w28 =>
    SepWPp.exists_pre fun w30 => SepWPp.exists_pre fun w29 => ?_
  tryFrom_fetches2 img.base C ctl abs 0 48
  generalize_entry (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨⟨by simp [arm64_norm], ?_, hF1, hsym1, by simp [arm64_norm]⟩,
    by simp [hx0, arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], Entails.refl _⟩
  rw [State.spAligned]
  simpa [arm64_norm] using spAligned_sub448 hsp

/-! ## Prologue version-check paths at `+0x044` (`68`) -/

/-- Fast error path 2 (`+0x044..+0x064` + `+0x078..+0x084` → `+0x440`): `(b0 >>> 4) < 3#8`
returns `Err(SignalProtocolError::LegacyCiphertextVersion(b0 >>> 4))`. -/
theorem prologue_44_legacyVer_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8} {rest : List (BitVec 8)}
    (hbs : x.bytes = b0 :: rest)
    (hge9 : 9 ≤ x.bytes.length)
    (hlt3 : (b0 >>> 4) < 3#8)
    (hst : EpilogueState img s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x044#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = x.bytesA)
    (hx19 : s.readReg64 .x19 = x.ret) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x440#64) s
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120)
      (fun sf Pf => EpilogueState img s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcond := cond_cs_ver_of_lt3 hlt3
  have hout : SignalMessage.tryFrom protoSignalCodec x.bytes =
      .error (.legacyCiphertextVersion (b0 >>> 4)) := by
    rw [hbs]
    exact tryFrom_eq_legacyVer (hbs ▸ hge9) hlt3
  have hbytes : (x.bytesA ↦ₛ x.bytes) = (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) := by
    rw [hbs, pointsToBytes_cons]
  rw [hbytes]
  refine SepWPp.mono_pre (sepConj_mono_right (memRegion120_split17 x.ret)) ?_
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun b16 => SepWPp.exists_pre fun r1 =>
    SepWPp.exists_pre fun r0 => ?_
  tryFrom_fetches2 img.base C ctl abs 68 36
  tryFrom_fetches2 img.base C ctl abs 120 16
  generalize_entry (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨EpilogueState.of_steps hF1 hsym1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
    (by simp [htr, arm64_norm]), ?_⟩
  have hmsg := spe_legacyVer_intro A x.ret (b0 >>> 4) hout
  simp only [errTag, speWord, BitVec.reduceAdd] at hmsg
  refine Entails.trans (Q := ((x.ret ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
      ((x.ret + 8#64) ↦₆₄ 9223372036854775812#64) ∗
      ((x.ret + 16#64) ↦₈ (b0 >>> 4)) ∗
      memRegion (x.ret + 17#64) 103) ∗
      ((x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest)))
    (by apply entails_of_eq; ac_rfl) ?_
  rw [← hbytes]
  exact sepConj_mono_left hmsg

/-- Fast error path 3 (`+0x044..+0x058` + `+0x068..+0x084` → `+0x440`): `4#8 < (b0 >>> 4)`
returns `Err(SignalProtocolError::UnrecognizedCiphertextVersion(b0 >>> 4))`. -/
theorem prologue_44_unrecognizedVer_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8} {rest : List (BitVec 8)}
    (hbs : x.bytes = b0 :: rest)
    (hge9 : 9 ≤ x.bytes.length)
    (hge3 : ¬ (b0 >>> 4) < 3#8) (hgt4 : 4#8 < (b0 >>> 4))
    (hst : EpilogueState img s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x044#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = x.bytesA)
    (hx19 : s.readReg64 .x19 = x.ret) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x440#64) s
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120)
      (fun sf Pf => EpilogueState img s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcond1 := cond_cs_ver_of_ge3 hge3
  have hcond2 := cond_ls_ver_of_gt4 hgt4
  have hout : SignalMessage.tryFrom protoSignalCodec x.bytes =
      .error (.unrecognizedCiphertextVersion (b0 >>> 4)) := by
    rw [hbs]
    exact tryFrom_eq_unrecognizedVer (hbs ▸ hge9) hge3 hgt4
  have hbytes : (x.bytesA ↦ₛ x.bytes) = (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) := by
    rw [hbs, pointsToBytes_cons]
  rw [hbytes]
  refine SepWPp.mono_pre (sepConj_mono_right (memRegion120_split17 x.ret)) ?_
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun b16 => SepWPp.exists_pre fun r1 =>
    SepWPp.exists_pre fun r0 => ?_
  tryFrom_fetches2 img.base C ctl abs 68 24
  tryFrom_fetches2 img.base C ctl abs 104 32
  generalize_entry (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨EpilogueState.of_steps hF1 hsym1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
    (by simp [htr, arm64_norm]), ?_⟩
  have hmsg := spe_unrecognizedVer_intro A x.ret (b0 >>> 4) hout
  simp only [errTag, speWord, BitVec.reduceAdd] at hmsg
  refine Entails.trans (Q := ((x.ret ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
      ((x.ret + 8#64) ↦₆₄ 9223372036854775813#64) ∗
      ((x.ret + 16#64) ↦₈ (b0 >>> 4)) ∗
      memRegion (x.ret + 17#64) 103) ∗
      ((x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest)))
    (by apply entails_of_eq; ac_rfl) ?_
  rw [← hbytes]
  exact sepConj_mono_left hmsg

/-- Valid version path (`+0x044..+0x058` + `+0x068..+0x06c` → `+0x088`):
when `3#8 ≤ b0 >>> 4 ≤ 4#8`, loads `x23 = b0.zeroExtend 64`, `x21 = x.bytesA`,
`x26 = speWord 2`, and reaches `+0x088` (`136`). -/
theorem prologue_44_validVer_wp {img : Obj.Image} {C : Crypto}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8}
    (hge3 : ¬ (b0 >>> 4) < 3#8) (hle4 : ¬ 4#8 < (b0 >>> 4))
    (hst : EpilogueState img s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x044#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = x.bytesA)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x088#64) s
      (x.bytesA ↦₈ b0)
      (fun s2 P2 =>
        EpilogueState img s0 (s0.sp - 448#64) s2 ∧
        s2.readReg64 .x19 = x.ret ∧
        s2.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧
        s2.readReg64 .x21 = x.bytesA ∧
        s2.readReg64 .x23 = b0.zeroExtend 64 ∧
        s2.readReg64 .x26 = 0x8000000000000002#64 ∧
        s2.readReg64 .x29 = s0.sp - 448#64 + 352#64 ∧
        (P2 ⊢ (x.bytesA ↦₈ b0)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcond1 := cond_cs_ver_of_ge3 hge3
  have hcond2 := cond_ls_ver_of_le4 hle4
  tryFrom_fetches2 img.base C ctl abs 68 24
  tryFrom_fetches2 img.base C ctl abs 104 8
  generalize_entry (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨EpilogueState.of_steps hF1 hsym1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
    (by simp [htr, arm64_norm]),
    by simp [hx19, arm64_norm], by simp [hx20, arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [hx29, arm64_norm], Entails.refl _⟩

/-! ## Prologue stack-frame initialization (`+0x088..+0x0b4` → `+0x0b8`) -/

theorem memRegion16_split8_8' (a : BitVec 64) :
    memRegion a 16 ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64, (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) := by
  rw [show (16 : Nat) = 8 + 8 by decide,
    memRegion_split a 8 8 (by decide), memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem memRegion24_split8_16 (a : BitVec 64) :
    memRegion a 24 ⊢
      ∃∗ w : BitVec 64, (a ↦₆₄ w) ∗ memRegion (a + 8#64) 16 := by
  rw [show (24 : Nat) = 8 + 16 by decide,
    memRegion_split a 8 16 (by decide), memRegion_eight]
  simp only [sepExists_sepConj_left]
  exact Entails.refl _

theorem memRegion8_split4_4 (a : BitVec 64) :
    memRegion a 8 ⊢
      ∃∗ w : BitVec 32, (a ↦₃₂ w) ∗ memRegion (a + 4#64) 4 := by
  rw [memRegion_eight a]
  refine Entails.sepExists_elim fun w64 => ?_
  rw [pointsTo64_split32 a w64]
  refine Entails.trans (sepConj_mono_right (pointsTo32_entails_memRegion (a + 4#64) _)) ?_
  exact sepExists_intro (fun w => (a ↦₃₂ w) ∗ memRegion (a + 4#64) 4) (w64.extractLsb' 0 32)

theorem memRegion112_emptyMsg_cells (sp' : BitVec 64) :
    memRegion (sp' + 176#64) 112 ⊢
      ∃∗ w280 : BitVec 32, ∃∗ w272 : BitVec 32,
      ∃∗ w248 : BitVec 64, ∃∗ w224 : BitVec 64,
      ∃∗ w200 : BitVec 64, ∃∗ w176 : BitVec 64,
        ((sp' + 176#64) ↦₆₄ w176) ∗ memRegion (sp' + 184#64) 16 ∗
        ((sp' + 200#64) ↦₆₄ w200) ∗ memRegion (sp' + 208#64) 16 ∗
        ((sp' + 224#64) ↦₆₄ w224) ∗ memRegion (sp' + 232#64) 16 ∗
        ((sp' + 248#64) ↦₆₄ w248) ∗ memRegion (sp' + 256#64) 16 ∗
        ((sp' + 272#64) ↦₃₂ w272) ∗ memRegion (sp' + 276#64) 4 ∗
        ((sp' + 280#64) ↦₃₂ w280) ∗ memRegion (sp' + 284#64) 4 := by
  rw [show (112 : Nat) = 24 + (24 + (24 + (24 + (8 + 8)))) by decide,
    memRegion_split (sp' + 176#64) 24 88 (by decide),
    memRegion_split (sp' + 176#64 + 24#64) 24 64 (by decide),
    memRegion_split (sp' + 176#64 + 24#64 + 24#64) 24 40 (by decide),
    memRegion_split (sp' + 176#64 + 24#64 + 24#64 + 24#64) 24 16 (by decide),
    memRegion_split (sp' + 176#64 + 24#64 + 24#64 + 24#64 + 24#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans
    (sepConj_mono (memRegion24_split8_16 (sp' + 176#64))
      (sepConj_mono (memRegion24_split8_16 (sp' + 200#64))
        (sepConj_mono (memRegion24_split8_16 (sp' + 224#64))
          (sepConj_mono (memRegion24_split8_16 (sp' + 248#64))
            (sepConj_mono (memRegion8_split4_4 (sp' + 272#64))
              (memRegion8_split4_4 (sp' + 280#64))))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _

theorem emptyMsg_cells_entails_wireSignalMessageOf (A : RustAlloc) (sp' : BitVec 64) :
    ((sp' + 176#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 184#64) 16 ∗
    ((sp' + 200#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 208#64) 16 ∗
    ((sp' + 224#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 232#64) 16 ∗
    ((sp' + 248#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 256#64) 16 ∗
    ((sp' + 272#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 276#64) 4 ∗
    ((sp' + 280#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 284#64) 4 ⊢
      wireSignalMessageOf A (sp' + 176#64) emptyProtoSignalMessage := by
  refine Entails.trans ?_
    (wireSignalMessageAt_entails_of A
      ⟨⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩⟩ (sp' + 176#64) emptyProtoSignalMessage)
  unfold wireSignalMessageAt emptyProtoSignalMessage optVecU8At optU32At
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

/-- Prologue stack-frame initialization (`+0x088..+0x0b4` → `+0x0b8`):
initializes `[sp' + 160..176]` to `(x.bytesA + 1, x.bytes.length - 9)`,
`[sp' + 176..288]` to `wireSignalMessageOf A (sp' + 176) emptyProtoSignalMessage`,
and `[sp' + 288]` to `sp' + 160`, setting `pstate = subsPState64 (BitVec.ofNat 64 x.bytes.length) 9#64`. -/
theorem prologue_88_init_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8}
    (hst : EpilogueState img s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x088#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx21 : s.readReg64 .x21 = x.bytesA)
    (hx23 : s.readReg64 .x23 = b0.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x0b8#64) s
      (memRegion (s0.sp - 448#64 + 160#64) 16 ∗
        memRegion (s0.sp - 448#64 + 176#64) 112 ∗
        memRegion (s0.sp - 448#64 + 288#64) 8)
      (fun s3 P3 =>
        EpilogueState img s0 (s0.sp - 448#64) s3 ∧
        s3.pstate = subsPState64 (BitVec.ofNat 64 x.bytes.length) 9#64 ∧
        s3.readReg64 .x2 = BitVec.ofNat 64 x.bytes.length - 9#64 ∧
        s3.readReg64 .x8 = s0.sp - 448#64 + 160#64 ∧
        s3.readReg64 .x19 = x.ret ∧
        s3.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧
        s3.readReg64 .x21 = x.bytesA ∧
        s3.readReg64 .x23 = b0.zeroExtend 64 ∧
        s3.readReg64 .x26 = 0x8000000000000002#64 ∧
        s3.readReg64 .x29 = s0.sp - 448#64 + 352#64 ∧
        (P3 ⊢ ((s0.sp - 448#64 + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
          ((s0.sp - 448#64 + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64)) ∗
          wireSignalMessageOf A (s0.sp - 448#64 + 176#64) emptyProtoSignalMessage ∗
          ((s0.sp - 448#64 + 288#64) ↦₆₄ (s0.sp - 448#64 + 160#64))))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  set sp' := s0.sp - 448#64
  rw [memRegion_eight (sp' + 288#64)]
  refine SepWPp.mono_pre
    (sepConj_mono (memRegion16_split8_8' (sp' + 160#64))
      (sepConj_mono_left (memRegion112_emptyMsg_cells sp'))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w288 =>
    SepWPp.exists_pre fun w280 => SepWPp.exists_pre fun w272 =>
    SepWPp.exists_pre fun w248 => SepWPp.exists_pre fun w224 =>
    SepWPp.exists_pre fun w200 => SepWPp.exists_pre fun w176 =>
    SepWPp.exists_pre fun c1 => SepWPp.exists_pre fun c0 => ?_
  tryFrom_fetches2 img.base C ctl abs 136 48
  generalize_entry (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨EpilogueState.of_steps hF1 hsym1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
    (by simp [htr, arm64_norm]),
    by simp [arm64_norm],
    by simp [BitVec.sub_eq_add_neg, arm64_norm],
    by simp [arm64_norm],
    by simp [hx19, arm64_norm],
    by simp [hx20, arm64_norm],
    by simp [hx21, arm64_norm],
    by simp [hx23, arm64_norm],
    by simp [hx26, arm64_norm],
    by simp [hx29, arm64_norm], ?_⟩
  have hempty := emptyMsg_cells_entails_wireSignalMessageOf A sp'
  simp only [noneCap] at hempty
  refine Entails.trans (Q := ((sp' + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
      ((sp' + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64)) ∗
      (((sp' + 176#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (sp' + 184#64) 16 ∗
        ((sp' + 200#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (sp' + 208#64) 16 ∗
        ((sp' + 224#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (sp' + 232#64) 16 ∗
        ((sp' + 248#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (sp' + 256#64) 16 ∗
        ((sp' + 272#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 276#64) 4 ∗
        ((sp' + 280#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 284#64) 4) ∗
      ((sp' + 288#64) ↦₆₄ (sp' + 160#64)))
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hempty))

/-- Frame `F` around the first segment `h1` and sequence with `h2`. -/
theorem SepWPp.bind_frame_entails {prog : Program} {mid ret : BitVec 64} {s0 s : Arm64.State}
    {P F : SepProp} {Qm : Arm64.State → SepProp} {φm : Arm64.State → Prop}
    {Q : Arm64.State → SepProp → Prop}
    (h1 : SepWPp prog mid s P (fun sm Pm => φm sm ∧ (Pm ⊢ Qm sm)) (tryFromQp s0))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φm sm →
      SepWPp prog ret sm (Qm sm ∗ F) Q (tryFromQp s0)) :
    SepWPp prog ret s (P ∗ F) Q (tryFromQp s0) := by
  have hf : SepWPp prog mid s (P ∗ F) (fun sm Pm => φm sm ∧ (Pm ⊢ Qm sm ∗ F)) (tryFromQp s0) :=
    SepWPp.frame_tryFrom h1 (fun _ _ ⟨hφ, hent⟩ => ⟨hφ, sepConj_mono_left hent⟩)
  refine SepWPp.bind hf ?_
  intro sm Pm hpc hrun ⟨hφ, hent⟩
  exact SepWPp.mono_pre hent (h2 sm hpc hrun hφ)

/-! ## Branch at `+0x0b8`: `9 < x.bytes.length` (`+0x0b8..+0x0cc` → `+0x0f0` → `+0x3b0`) -/

@[local simp, local arm64_norm, local wp_norm]
theorem cond_eq_len_of_gt9 {n : Nat} (hgt9 : 9 < n) (hlt : n < 2 ^ 63) :
    ConditionHolds .EQ (subsPState64 (BitVec.ofNat 64 n) 9#64) = false := by
  have h1 : 9#64 < BitVec.ofNat 64 n := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat]
    omega
  unfold ConditionHolds subsPState64 AddWithCarry64
  dsimp only
  bv_kernel

/-- Steps `+0x0b8..+0x0cc` → `+0x0f0` when `9 < x.bytes.length`: sets up `LoopRegs` and
loop cursor registers `x28 = sp' + 160`, `x27 = sp' + 168`, `x2 = x.bytes.length - 9`. -/
theorem prologue_b8_gt9_to_f0_wp {img : Obj.Image} {C : Crypto}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8}
    (hgt9 : 9 < x.bytes.length) (hlt : x.bytes.length < 2 ^ 63)
    (hst : EpilogueState img s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x0b8#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState64 (BitVec.ofNat 64 x.bytes.length) 9#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 x.bytes.length - 9#64)
    (hx8 : s.readReg64 .x8 = s0.sp - 448#64 + 160#64)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx21 : s.readReg64 .x21 = x.bytesA)
    (hx23 : s.readReg64 .x23 = b0.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x0f0#64) s
      emp
      (fun s4 P4 =>
        (LoopRegs (s0.sp - 448#64) x.ret (BitVec.ofNat 64 x.bytes.length)
          x.bytesA (b0.zeroExtend 64) s4 ∧
        EpilogueState img s0 (s0.sp - 448#64) s4 ∧
        s4.readReg64 .x28 = s0.sp - 448#64 + 160#64 ∧
        s4.readReg64 .x27 = s0.sp - 448#64 + 168#64 ∧
        s4.readReg64 .x2 = BitVec.ofNat 64 x.bytes.length - 9#64) ∧
        (P4 ⊢ emp))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcond := cond_eq_len_of_gt9 hgt9 hlt
  tryFrom_fetches2 img.base C ctl abs 184 24
  generalize_entry (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨⟨⟨by simp [hsp_eq, arm64_norm], by simp [hx29, arm64_norm],
      by simp [hx26, arm64_norm], by simp [arm64_norm],
      by simp [hx23, arm64_norm], by simp [arm64_norm],
      by simp [hx21, arm64_norm], by simp [hx20, arm64_norm],
      by simp [hx19, arm64_norm]⟩,
    EpilogueState.of_steps hF1 hsym1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
      (by simp [htr, arm64_norm]),
    by simp [arm64_norm],
    by simp [arm64_norm],
    by simp [hx2, arm64_norm]⟩,
    Entails.refl _⟩

/-! ## Branch at `+0x0b8`: `x.bytes.length = 9` (`+0x0b8` → `+0x440`) -/

@[local simp, local arm64_norm, local wp_norm]
theorem cond_eq_len9 :
    ConditionHolds .EQ (subsPState64 9#64 9#64) = true := by
  unfold ConditionHolds subsPState64 AddWithCarry64
  decide

@[local simp, local arm64_norm, local wp_norm]
theorem cond_ne_noneCap_add2 :
    ConditionHolds .NE (addsPState64 (bv% (2 ^ 64 - 1)) 2#64) = true := by
  unfold ConditionHolds addsPState64 AddWithCarry64
  decide

@[local simp, local arm64_norm, local wp_norm]
theorem cond_eq_noneCap_add1 :
    ConditionHolds .EQ (addsPState64 (bv% (2 ^ 64 - 1)) 1#64) = true := by
  unfold ConditionHolds addsPState64 AddWithCarry64
  decide

@[local simp, local arm64_norm, local wp_norm]
theorem cond_hi_noneCap_sub1_add3 :
    ConditionHolds .HI (addsPState64 (bv% (2 ^ 64 - 2)) 3#64) = true := by
  unfold ConditionHolds addsPState64 AddWithCarry64
  decide

theorem memRegion_four_entails' (a : BitVec 64) :
    memRegion a 4 ⊢ ∃∗ v : BitVec 32, a ↦₃₂ v := by
  rw [memRegion_eq_exists_bytes a 4 (by decide)]
  refine Entails.sepExists_elim fun bs => Entails.pure_left fun hlen => ?_
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> try simp at hlen
  rw [pointsToBytes4_eq_pointsTo32]
  exact Entails.sepExists_intro (b3 ++ b2 ++ b1 ++ b0)

theorem wireSignalMessageOf_emptyMsg_cells (A : RustAlloc) (sp' : BitVec 64) :
    wireSignalMessageOf A (sp' + 176#64) emptyProtoSignalMessage ⊢
      ∃∗ pcVal : BitVec 32, ∃∗ cVal : BitVec 32,
      ∃∗ adLen : BitVec 64, ∃∗ adPtr : BitVec 64,
      ∃∗ pqLen : BitVec 64, ∃∗ pqPtr : BitVec 64,
      ∃∗ ctLen : BitVec 64, ∃∗ ctPtr : BitVec 64,
      ∃∗ rkLen : BitVec 64, ∃∗ rkPtr : BitVec 64,
        ((sp' + 176#64) ↦₆₄ noneCap) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗ ((sp' + 192#64) ↦₆₄ rkLen) ∗
        ((sp' + 200#64) ↦₆₄ noneCap) ∗ ((sp' + 208#64) ↦₆₄ ctPtr) ∗ ((sp' + 216#64) ↦₆₄ ctLen) ∗
        ((sp' + 224#64) ↦₆₄ noneCap) ∗ ((sp' + 232#64) ↦₆₄ pqPtr) ∗ ((sp' + 240#64) ↦₆₄ pqLen) ∗
        ((sp' + 248#64) ↦₆₄ noneCap) ∗ ((sp' + 256#64) ↦₆₄ adPtr) ∗ ((sp' + 264#64) ↦₆₄ adLen) ∗
        ((sp' + 272#64) ↦₃₂ 0#32) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
        ((sp' + 280#64) ↦₃₂ 0#32) ∗ ((sp' + 284#64) ↦₃₂ pcVal) := by
  unfold wireSignalMessageOf
  refine Entails.sepExists_elim fun g => ?_
  unfold wireSignalMessageAt emptyProtoSignalMessage optVecU8At optU32At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans
    (sepConj_mono (sepConj_mono_right (memRegion16_split8_8' (sp' + 184#64)))
      (sepConj_mono (sepConj_mono_right (memRegion16_split8_8' (sp' + 208#64)))
        (sepConj_mono (sepConj_mono_right (memRegion16_split8_8' (sp' + 232#64)))
          (sepConj_mono (sepConj_mono_right (memRegion16_split8_8' (sp' + 256#64)))
            (sepConj_mono (sepConj_mono_right (memRegion_four_entails' (sp' + 276#64)))
              (sepConj_mono_right (memRegion_four_entails' (sp' + 284#64)))))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _

/-- First half of `x.bytes.length = 9` after `+0x0b8`: steps `+0x0b8 → +0x298 → +0x3b0 → +0x424 → +0x460`. -/
theorem prologue_b8_len9_to_460_wp {img : Obj.Image} {C : Crypto}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    {x : TryFromGhost} {s0 s : State}
    {s88 s96 rkPtr ctPtr pqPtr adPtr : BitVec 64}
    (hst : EpilogueState img s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x0b8#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState64 9#64 9#64)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x460#64) s
      (((s0.sp - 448#64 + 88#64) ↦₆₄ s88) ∗ ((s0.sp - 448#64 + 96#64) ↦₆₄ s96) ∗
        ((s0.sp - 448#64 + 176#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 184#64) ↦₆₄ rkPtr) ∗
        ((s0.sp - 448#64 + 200#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 208#64) ↦₆₄ ctPtr) ∗
        ((s0.sp - 448#64 + 224#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 232#64) ↦₆₄ pqPtr) ∗
        ((s0.sp - 448#64 + 248#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 256#64) ↦₆₄ adPtr))
      (fun s4 P4 =>
        (EpilogueState img s0 (s0.sp - 448#64) s4 ∧
        s4.readReg64 .x1 = noneCap ∧
        s4.readReg64 .x19 = x.ret ∧
        s4.readReg64 .x22 = noneCap ∧
        s4.readReg64 .x25 = noneCap ∧
        s4.readReg64 .x26 = 0x8000000000000002#64 ∧
        s4.readReg64 .x27 = noneCap) ∧
        (P4 ⊢ memRegion (s0.sp - 448#64 + 88#64) 16 ∗
          ((s0.sp - 448#64 + 176#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 184#64) ↦₆₄ rkPtr) ∗
          ((s0.sp - 448#64 + 200#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 208#64) ↦₆₄ ctPtr) ∗
          ((s0.sp - 448#64 + 224#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 232#64) ↦₆₄ pqPtr) ∗
          ((s0.sp - 448#64 + 248#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 256#64) ↦₆₄ adPtr)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  set sp' := s0.sp - 448#64
  dsimp only [noneCap]
  tryFrom_fetches2 img.base C ctl abs 184 4
  tryFrom_fetches2 img.base C ctl abs 664 8
  tryFrom_fetches2 img.base C ctl abs 944 24
  tryFrom_fetches2 img.base C ctl abs 1060 8
  generalize_entry (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨⟨EpilogueState.of_steps hF1 hsym1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
    (by simp [htr, arm64_norm]),
    by simp [arm64_norm],
    by simp [hx19, arm64_norm],
    by simp [arm64_norm],
    by simp [arm64_norm],
    by simp [hx26, arm64_norm],
    by simp [arm64_norm]⟩, ?_⟩
  have h16 := pointsTo64_pair_entails_memRegion16 (sp' + 88#64) adPtr pqPtr
  have ha96 : sp' + 88#64 + 8#64 = sp' + 96#64 := by bv_omega
  rw [ha96] at h16
  rw [← sepConj_assoc ((sp' + 88#64) ↦₆₄ adPtr)]
  exact sepConj_mono_left h16

theorem pointsTo64_triple_entails_memRegion24 (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [show (24 : Nat) = 8 + (8 + 8) by decide,
    memRegion_split a 8 16 (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion a w0)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) w1)
      (pointsTo64_entails_memRegion (a + 16#64) w2))

theorem pointsTo32_pair_entails_memRegion8' (a : BitVec 64) (w0 w1 : BitVec 32) :
    (a ↦₃₂ w0) ∗ ((a + 4#64) ↦₃₂ w1) ⊢ memRegion a 8 := by
  rw [pointsTo32_pair]
  exact pointsTo64_entails_memRegion a (w1 ++ w0)

theorem cells112_entails_memRegion112 (sp' : BitVec 64)
    (rkCap rkPtr rkLen ctCap ctPtr ctLen pqCap pqPtr pqLen adCap adPtr adLen : BitVec 64)
    (cTag cVal pcTag pcVal : BitVec 32) :
    ((sp' + 176#64) ↦₆₄ rkCap) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗ ((sp' + 192#64) ↦₆₄ rkLen) ∗
    ((sp' + 200#64) ↦₆₄ ctCap) ∗ ((sp' + 208#64) ↦₆₄ ctPtr) ∗ ((sp' + 216#64) ↦₆₄ ctLen) ∗
    ((sp' + 224#64) ↦₆₄ pqCap) ∗ ((sp' + 232#64) ↦₆₄ pqPtr) ∗ ((sp' + 240#64) ↦₆₄ pqLen) ∗
    ((sp' + 248#64) ↦₆₄ adCap) ∗ ((sp' + 256#64) ↦₆₄ adPtr) ∗ ((sp' + 264#64) ↦₆₄ adLen) ∗
    ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
    ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ⊢
      memRegion (sp' + 176#64) 112 := by
  rw [show (112 : Nat) = 24 + (24 + (24 + (24 + (8 + 8)))) by decide,
    memRegion_split (sp' + 176#64) 24 88 (by decide),
    memRegion_split (sp' + 176#64 + 24#64) 24 64 (by decide),
    memRegion_split (sp' + 176#64 + 24#64 + 24#64) 24 40 (by decide),
    memRegion_split (sp' + 176#64 + 24#64 + 24#64 + 24#64) 24 16 (by decide),
    memRegion_split (sp' + 176#64 + 24#64 + 24#64 + 24#64 + 24#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h1 := pointsTo64_triple_entails_memRegion24 (sp' + 176#64) rkCap rkPtr rkLen
  have h2 := pointsTo64_triple_entails_memRegion24 (sp' + 200#64) ctCap ctPtr ctLen
  have h3 := pointsTo64_triple_entails_memRegion24 (sp' + 224#64) pqCap pqPtr pqLen
  have h4 := pointsTo64_triple_entails_memRegion24 (sp' + 248#64) adCap adPtr adLen
  have h5 := pointsTo32_pair_entails_memRegion8' (sp' + 272#64) cTag cVal
  have h6 := pointsTo32_pair_entails_memRegion8' (sp' + 280#64) pcTag pcVal
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2 h3 h4 h5 h6
  refine Entails.trans (Q :=
      (((sp' + 176#64) ↦₆₄ rkCap) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗ ((sp' + 192#64) ↦₆₄ rkLen)) ∗
      (((sp' + 200#64) ↦₆₄ ctCap) ∗ ((sp' + 208#64) ↦₆₄ ctPtr) ∗ ((sp' + 216#64) ↦₆₄ ctLen)) ∗
      (((sp' + 224#64) ↦₆₄ pqCap) ∗ ((sp' + 232#64) ↦₆₄ pqPtr) ∗ ((sp' + 240#64) ↦₆₄ pqLen)) ∗
      (((sp' + 248#64) ↦₆₄ adCap) ∗ ((sp' + 256#64) ↦₆₄ adPtr) ∗ ((sp' + 264#64) ↦₆₄ adLen)) ∗
      (((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal)) ∗
      (((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal)))
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4 (sepConj_mono h5 h6))))

theorem memRegion120_split16' (x19 : BitVec 64) :
    memRegion x19 120 ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 := by
  rw [show (120 : Nat) = 8 + (8 + 104) by decide,
    memRegion_split x19 8 112 (by decide),
    memRegion_split (x19 + 8#64) 8 104 (by decide),
    memRegion_eight, memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem spe_invalidProto_intro' (A : RustAlloc) (x19 : BitVec 64)
    {out : Except SignalProtocolError SignalMessage}
    (herr : out = .error .invalidProtobufEncoding) :
    (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗ memRegion (x19 + 16#64) 104 ⊢
      signalMessageResultAt A [] x19 out := by
  rw [herr]
  dsimp only [signalMessageResultAt, errResultAt, speAt]
  have h64 : (120 : Nat) - 56 = 64 := rfl
  rw [h64]
  have hsplit : memRegion (x19 + 16#64) 104 =
      memRegion (x19 + 8#64 + 8#64) 40 ∗ memRegion (x19 + 56#64) 64 := by
    have hs := memRegion_split (x19 + 16#64) 40 64 (by decide)
    have h104 : (40 : Nat) + 64 = 104 := rfl
    have ha1 : x19 + 8#64 + 8#64 = x19 + 16#64 := by bv_omega
    have ha2 : x19 + 16#64 + 40#64 = x19 + 56#64 := by bv_omega
    rw [h104, ha2] at hs
    rw [ha1]
    exact hs
  rw [hsplit]
  apply entails_of_eq; ac_rfl

/-- Second half of `x.bytes.length = 9`: steps `+0x460 → +0x4f0 → +0x64c → +0x668 → +0x684 → +0x440`. -/
theorem prologue_460_len9_to_440_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    {x : TryFromGhost} {s0 s : State}
    {rkPtr rkLen ctPtr ctLen pqPtr pqLen adPtr adLen : BitVec 64}
    {cVal pcVal : BitVec 32}
    {out : Except SignalProtocolError SignalMessage}
    (hout : out = .error .invalidProtobufEncoding)
    (hst : EpilogueState img s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x460#64)
    (hrun : s.status = .Running)
    (hx1 : s.readReg64 .x1 = noneCap)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx22 : s.readReg64 .x22 = noneCap)
    (hx25 : s.readReg64 .x25 = noneCap)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx27 : s.readReg64 .x27 = noneCap) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x440#64) s
      (memRegion x.ret 120 ∗
        ((s0.sp - 448#64 + 176#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 184#64) ↦₆₄ rkPtr) ∗
        ((s0.sp - 448#64 + 192#64) ↦₆₄ rkLen) ∗
        ((s0.sp - 448#64 + 200#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 208#64) ↦₆₄ ctPtr) ∗
        ((s0.sp - 448#64 + 216#64) ↦₆₄ ctLen) ∗
        ((s0.sp - 448#64 + 224#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 232#64) ↦₆₄ pqPtr) ∗
        ((s0.sp - 448#64 + 240#64) ↦₆₄ pqLen) ∗
        ((s0.sp - 448#64 + 248#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 256#64) ↦₆₄ adPtr) ∗
        ((s0.sp - 448#64 + 264#64) ↦₆₄ adLen) ∗
        ((s0.sp - 448#64 + 272#64) ↦₃₂ 0#32) ∗ ((s0.sp - 448#64 + 276#64) ↦₃₂ cVal) ∗
        ((s0.sp - 448#64 + 280#64) ↦₃₂ 0#32) ∗ ((s0.sp - 448#64 + 284#64) ↦₃₂ pcVal))
      (fun sf Pf =>
        EpilogueState img s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 448#64 + 176#64) 112 ∗
          signalMessageResultAt A [] x.ret out))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  set sp' := s0.sp - 448#64
  dsimp only [noneCap] at hx1 hx22 hx25 hx27 ⊢
  refine SepWPp.mono_pre (sepConj_mono_left (memRegion120_split16' x.ret)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun r1 => SepWPp.exists_pre fun r0 => ?_
  tryFrom_fetches2 img.base C ctl abs 1120 44
  tryFrom_fetches2 img.base C ctl abs 1264 12
  tryFrom_fetches2 img.base C ctl abs 1612 12
  tryFrom_fetches2 img.base C ctl abs 1640 12
  tryFrom_fetches2 img.base C ctl abs 1668 12
  generalize_entry (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨EpilogueState.of_steps hF1 hsym1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
    (by simp [htr, arm64_norm]), ?_⟩
  have h112 := cells112_entails_memRegion112 sp'
    9223372036854775810#64 rkPtr rkLen
    (bv% (2 ^ 64 - 1)) ctPtr ctLen
    (bv% (2 ^ 64 - 1)) pqPtr pqLen
    (bv% (2 ^ 64 - 1)) adPtr adLen
    0#32 cVal 0#32 pcVal
  have hmsg := spe_invalidProto_intro' A x.ret hout
  simp only [errTag, speWord] at hmsg
  refine Entails.trans (Q :=
      (((sp' + 176#64) ↦₆₄ 9223372036854775810#64) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗ ((sp' + 192#64) ↦₆₄ rkLen) ∗
        ((sp' + 200#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ ((sp' + 208#64) ↦₆₄ ctPtr) ∗ ((sp' + 216#64) ↦₆₄ ctLen) ∗
        ((sp' + 224#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ ((sp' + 232#64) ↦₆₄ pqPtr) ∗ ((sp' + 240#64) ↦₆₄ pqLen) ∗
        ((sp' + 248#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ ((sp' + 256#64) ↦₆₄ adPtr) ∗ ((sp' + 264#64) ↦₆₄ adLen) ∗
        ((sp' + 272#64) ↦₃₂ 0#32) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
        ((sp' + 280#64) ↦₃₂ 0#32) ∗ ((sp' + 284#64) ↦₃₂ pcVal)) ∗
      ((x.ret ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ ((x.ret + 8#64) ↦₆₄ 9223372036854775810#64) ∗
        memRegion (x.ret + 16#64) 104))
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono h112 hmsg

/-- Full `+0x0b8 → +0x440` segment when `x.bytes.length = 9`. -/
theorem prologue_b8_len9_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    {x : TryFromGhost} {s0 s : State}
    {out : Except SignalProtocolError SignalMessage}
    (hout : out = .error .invalidProtobufEncoding)
    (hst : EpilogueState img s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x0b8#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState64 9#64 9#64)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x440#64) s
      (memRegion (s0.sp - 448#64 + 88#64) 16 ∗
        wireSignalMessageOf A (s0.sp - 448#64 + 176#64) emptyProtoSignalMessage ∗
        memRegion x.ret 120)
      (fun sf Pf =>
        EpilogueState img s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 448#64 + 88#64) 16 ∗
          memRegion (s0.sp - 448#64 + 176#64) 112 ∗
          signalMessageResultAt A [] x.ret out))
      (tryFromQp s0) := by
  set sp' := s0.sp - 448#64
  refine SepWPp.mono_pre
    (sepConj_mono (memRegion16_split8_8' (sp' + 88#64))
      (sepConj_mono_left (wireSignalMessageOf_emptyMsg_cells A sp'))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun pcVal => SepWPp.exists_pre fun cVal =>
    SepWPp.exists_pre fun adLen => SepWPp.exists_pre fun adPtr =>
    SepWPp.exists_pre fun pqLen => SepWPp.exists_pre fun pqPtr =>
    SepWPp.exists_pre fun ctLen => SepWPp.exists_pre fun ctPtr =>
    SepWPp.exists_pre fun rkLen => SepWPp.exists_pre fun rkPtr =>
    SepWPp.exists_pre fun s96 => SepWPp.exists_pre fun s88 => ?_
  set F1 := ((sp' + 192#64) ↦₆₄ rkLen) ∗ ((sp' + 216#64) ↦₆₄ ctLen) ∗
    ((sp' + 240#64) ↦₆₄ pqLen) ∗ ((sp' + 264#64) ↦₆₄ adLen) ∗
    ((sp' + 272#64) ↦₃₂ 0#32) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
    ((sp' + 280#64) ↦₃₂ 0#32) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ∗
    memRegion x.ret 120
  refine SepWPp.mono_pre (P' :=
      (((sp' + 88#64) ↦₆₄ s88) ∗ ((sp' + 96#64) ↦₆₄ s96) ∗
        ((sp' + 176#64) ↦₆₄ noneCap) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗
        ((sp' + 200#64) ↦₆₄ noneCap) ∗ ((sp' + 208#64) ↦₆₄ ctPtr) ∗
        ((sp' + 224#64) ↦₆₄ noneCap) ∗ ((sp' + 232#64) ↦₆₄ pqPtr) ∗
        ((sp' + 248#64) ↦₆₄ noneCap) ∗ ((sp' + 256#64) ↦₆₄ adPtr)) ∗ F1)
    (by dsimp only [F1]; apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_entails
    (prologue_b8_len9_to_460_wp ctl hst hpc hrun hpstate hx19 hx26) ?_
  intro s4 hpc4 hrun4 ⟨hst4, hx1_4, hx19_4, hx22_4, hx25_4, hx26_4, hx27_4⟩
  dsimp only [F1]
  refine SepWPp.mono_pre (P' :=
      (memRegion x.ret 120 ∗
        ((sp' + 176#64) ↦₆₄ noneCap) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗
        ((sp' + 192#64) ↦₆₄ rkLen) ∗
        ((sp' + 200#64) ↦₆₄ noneCap) ∗ ((sp' + 208#64) ↦₆₄ ctPtr) ∗
        ((sp' + 216#64) ↦₆₄ ctLen) ∗
        ((sp' + 224#64) ↦₆₄ noneCap) ∗ ((sp' + 232#64) ↦₆₄ pqPtr) ∗
        ((sp' + 240#64) ↦₆₄ pqLen) ∗
        ((sp' + 248#64) ↦₆₄ noneCap) ∗ ((sp' + 256#64) ↦₆₄ adPtr) ∗
        ((sp' + 264#64) ↦₆₄ adLen) ∗
        ((sp' + 272#64) ↦₃₂ 0#32) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
        ((sp' + 280#64) ↦₃₂ 0#32) ∗ ((sp' + 284#64) ↦₃₂ pcVal)) ∗ memRegion (sp' + 88#64) 16)
    (by dsimp only [sp']; apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.frame_tryFrom
    (prologue_460_len9_to_440_wp (A := A) ctl hout hst4 hpc4 hrun4
      hx1_4 hx19_4 hx22_4 hx25_4 hx26_4 hx27_4)
    fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  dsimp only [sp']
  apply entails_of_eq; ac_rfl

theorem prologue_88_init_wp' {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8}
    (hst : EpilogueState img s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x088#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx21 : s.readReg64 .x21 = x.bytesA)
    (hx23 : s.readReg64 .x23 = b0.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x0b8#64) s
      (memRegion (s0.sp - 448#64 + 160#64) 16 ∗
        memRegion (s0.sp - 448#64 + 176#64) 112 ∗
        memRegion (s0.sp - 448#64 + 288#64) 8)
      (fun s3 P3 =>
        (EpilogueState img s0 (s0.sp - 448#64) s3 ∧
        s3.pstate = subsPState64 (BitVec.ofNat 64 x.bytes.length) 9#64 ∧
        s3.readReg64 .x2 = BitVec.ofNat 64 x.bytes.length - 9#64 ∧
        s3.readReg64 .x8 = s0.sp - 448#64 + 160#64 ∧
        s3.readReg64 .x19 = x.ret ∧
        s3.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧
        s3.readReg64 .x21 = x.bytesA ∧
        s3.readReg64 .x23 = b0.zeroExtend 64 ∧
        s3.readReg64 .x26 = 0x8000000000000002#64 ∧
        s3.readReg64 .x29 = s0.sp - 448#64 + 352#64) ∧
        (P3 ⊢ ((s0.sp - 448#64 + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
          ((s0.sp - 448#64 + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64)) ∗
          wireSignalMessageOf A (s0.sp - 448#64 + 176#64) emptyProtoSignalMessage ∗
          ((s0.sp - 448#64 + 288#64) ↦₆₄ (s0.sp - 448#64 + 160#64))))
      (tryFromQp s0) := by
  intro R hm hL
  obtain ⟨sf, hsteps, hex⟩ :=
    prologue_88_init_wp ctl hst hpc hrun hx19 hx20 hx21 hx23 hx26 hx29 R hm hL
  rcases hex with ⟨hpc1, hrun1, Pf, hmf, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hent⟩, hv⟩ | hpan
  · exact ⟨sf, hsteps, Or.inl ⟨hpc1, hrun1, Pf, hmf, ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, hent⟩, hv⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-- Full `+0x088 → +0x440` segment when `x.bytes.length = 9` and `3#8 ≤ b0 >>> 4 ≤ 4#8`. -/
theorem prologue_88_len9_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8} {rest : List (BitVec 8)}
    (hbs : x.bytes = b0 :: rest)
    (hlen9 : x.bytes.length = 9)
    (hge3 : ¬ (b0 >>> 4) < 3#8) (hle4 : ¬ 4#8 < (b0 >>> 4))
    (hst : EpilogueState img s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x088#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx21 : s.readReg64 .x21 = x.bytesA)
    (hx23 : s.readReg64 .x23 = b0.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x440#64) s
      (memRegion (s0.sp - 448#64 + 88#64) 16 ∗
        memRegion (s0.sp - 448#64 + 160#64) 16 ∗
        memRegion (s0.sp - 448#64 + 176#64) 112 ∗
        memRegion (s0.sp - 448#64 + 288#64) 8 ∗
        memRegion x.ret 120)
      (fun sf Pf =>
        EpilogueState img s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 448#64 + 88#64) 16 ∗
          memRegion (s0.sp - 448#64 + 160#64) 16 ∗
          memRegion (s0.sp - 448#64 + 176#64) 112 ∗
          memRegion (s0.sp - 448#64 + 288#64) 8 ∗
          signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes)))
      (tryFromQp s0) := by
  set sp' := s0.sp - 448#64
  have hhead : x.bytes.headD 0#8 = b0 := by simp [hbs]
  have hout := tryFrom_eq_len9 hlen9 (hhead ▸ hge3) (hhead ▸ hle4)
  refine SepWPp.mono_pre (P' :=
      (memRegion (sp' + 160#64) 16 ∗ memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 8) ∗
      (memRegion (sp' + 88#64) 16 ∗ memRegion x.ret 120))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_entails
    (prologue_88_init_wp' (A := A) ctl hst hpc hrun hx19 hx20 hx21 hx23 hx26 hx29) ?_
  intro s3 hpc3 hrun3 ⟨hst3, hpstate3, _, _, hx19_3, _, _, _, hx26_3, _⟩
  have hpstate9 : s3.pstate = subsPState64 9#64 9#64 := by
    rw [hpstate3, hlen9]
  have h160 : ((sp' + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
      ((sp' + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64)) ⊢
      memRegion (sp' + 160#64) 16 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      pointsTo64_pair_entails_memRegion16 (sp' + 160#64)
        (x.bytesA + 1#64) (BitVec.ofNat 64 x.bytes.length - 9#64)
  have h288 := pointsTo64_entails_memRegion (sp' + 288#64) (sp' + 160#64)
  refine SepWPp.mono_pre (P' :=
      (memRegion (sp' + 88#64) 16 ∗ wireSignalMessageOf A (sp' + 176#64) emptyProtoSignalMessage ∗
        memRegion x.ret 120) ∗
      (memRegion (sp' + 160#64) 16 ∗ memRegion (sp' + 288#64) 8))
    (by
      refine Entails.trans (Q :=
          (memRegion (sp' + 88#64) 16 ∗ wireSignalMessageOf A (sp' + 176#64) emptyProtoSignalMessage ∗
            memRegion x.ret 120) ∗
          ((((sp' + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
            ((sp' + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64))) ∗
            ((sp' + 288#64) ↦₆₄ (sp' + 160#64))))
        (by dsimp only [sp']; apply entails_of_eq; ac_rfl) ?_
      exact sepConj_mono_right (sepConj_mono h160 h288)) ?_
  refine SepWPp.frame_tryFrom
    (prologue_b8_len9_wp ctl hout hst3 hpc3 hrun3 hpstate9 hx19_3 hx26_3)
    fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  dsimp only [sp']
  apply entails_of_eq; ac_rfl

/-! ## Branch `+0x088 → +0x0b8 → +0x0f0 → +0x3b0` when `9 < x.bytes.length` -/

theorem tryFrom_loop_slice_eq {b0 : BitVec 8} {rest : List (BitVec 8)}
    (hgt8 : 8 < rest.length) :
    ((b0 :: rest).take ((b0 :: rest).length - 8)).drop 1 = rest.take (rest.length - 8) := by
  have hk : (b0 :: rest).length - 8 = (rest.length - 8) + 1 := by
    simp only [List.length_cons]; omega
  rw [hk, List.take_succ_cons, List.drop_succ_cons, List.drop_zero]

theorem bv_ofNat_sub9 {n : Nat} (hge9 : 9 ≤ n) :
    BitVec.ofNat 64 (n - 9) = BitVec.ofNat 64 n - 9#64 := by
  have h1 : BitVec.ofNat 64 n = BitVec.ofNat 64 (n - 9) + 9#64 := by
    rw [show (9#64 : BitVec 64) = BitVec.ofNat 64 9 from rfl,
      ← BitVec.ofNat_add, Nat.sub_add_cancel hge9]
  rw [h1, BitVec.add_sub_cancel]

/-- Memory state at `+0x3b0` after recombining the cursor/scratch stack slots and input slice. -/
def loopPostMem (A : RustAlloc) (sp' : BitVec 64) (x : TryFromGhost) (x24 : BitVec 64) : SepProp :=
  memRegion sp' 176 ∗
    memRegion (sp' + 288#64) 64 ∗
    (x.bytesA ↦ₛ x.bytes) ∗
    A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
    match decode ((x.bytes.take (x.bytes.length - 8)).drop 1) with
    | some m' =>
      ⌜x24 = 0#64⌝ ∗ wireSignalMessageOf A (sp' + 176#64) m'
    | none =>
      ⌜x24 ≠ 0#64⌝ ∗ decodeErrorAt A x24 ∗
        (∃∗ mErr, wireSignalMessageOf A (sp' + 176#64) mErr)

/-- Full `+0x088 → +0x0b8 → +0x0f0 → +0x3b0` segment when `9 < x.bytes.length`. -/
theorem prologue_88_gt9_loop_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    (hS : TripleRatchetHooksW img C A S abs)
    (hvarint : DecodeVarintSliceOkW img C A ctl abs)
    (hint32 : Int32MergeOkW img C A ctl abs)
    (hskip : SkipFieldOkW img C A ctl abs)
    (hbytes : BytesMergeOkW img C A ctl abs)
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8} {rest : List (BitVec 8)}
    (hbs : x.bytes = b0 :: rest)
    (hgt9 : 9 < x.bytes.length) (hlt : x.bytes.length < 2 ^ 63)
    (hst : EpilogueState img s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x088#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx21 : s.readReg64 .x21 = x.bytesA)
    (hx23 : s.readReg64 .x23 = b0.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x3b0#64) s
      (memRegion (s0.sp - 448#64) 176 ∗
        memRegion (s0.sp - 448#64 + 176#64) 112 ∗
        memRegion (s0.sp - 448#64 + 288#64) 64 ∗
        (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) ∗
        A.pool ∗ stackAt (s0.sp - 448#64) (skipFieldStackX 100))
      (fun sf Pf =>
        LoopExitState img s0 (s0.sp - 448#64) x.ret
          (BitVec.ofNat 64 x.bytes.length) x.bytesA (b0.zeroExtend 64) sf ∧
        (Pf ⊢ loopPostMem A (s0.sp - 448#64) x (sf.readReg64 .x24)))
      (tryFromQp s0) := by
  set sp' := s0.sp - 448#64
  set bs := (x.bytes.take (x.bytes.length - 8)).drop 1
  have hrest_len : rest.length + 1 = x.bytes.length := by
    have := congrArg List.length hbs; simpa using this.symm
  have hrest_gt8 : 8 < rest.length := by omega
  have hbs_eq : bs = rest.take (rest.length - 8) := by
    dsimp only [bs]; rw [hbs]; exact tryFrom_loop_slice_eq hrest_gt8
  have hbs_len : bs.length = x.bytes.length - 9 := by
    rw [hbs_eq, List.length_take, Nat.min_eq_left (by omega)]; omega
  have hbs_pos : 0 < bs.length := by omega
  rcases hcons : bs with _ | ⟨b1, bs1⟩
  · simp [hcons] at hbs_pos
  have hlen_cons : (b1 :: bs1).length = x.bytes.length - 9 := hcons ▸ hbs_len
  have hbv_len : BitVec.ofNat 64 (b1 :: bs1).length = BitVec.ofNat 64 x.bytes.length - 9#64 := by
    rw [hlen_cons]; exact bv_ofNat_sub9 (by omega)
  have h176_split : memRegion sp' 176 = memRegion sp' 160 ∗ memRegion (sp' + 160#64) 16 :=
    memRegion_split' (n := 160) (k := 16) rfl rfl (by decide)
  have h64_split : memRegion (sp' + 288#64) 64 =
      memRegion (sp' + 288#64) 8 ∗ memRegion (sp' + 296#64) 48 ∗ memRegion (sp' + 344#64) 8 := by
    rw [memRegion_split' (n := 8) (k := 56) rfl rfl (by decide),
      memRegion_split' (b := sp' + 288#64 + 8#64) (n := 48) (k := 8) rfl rfl (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [h176_split, h64_split]
  set F1 := memRegion sp' 160 ∗ memRegion (sp' + 296#64) 48 ∗ memRegion (sp' + 344#64) 8 ∗
    (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) ∗
    A.pool ∗ stackAt sp' (skipFieldStackX 100)
  refine SepWPp.mono_pre (P' :=
      (memRegion (sp' + 160#64) 16 ∗ memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 8) ∗ F1)
    (by dsimp only [F1, sp']; apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_entails
    (prologue_88_init_wp' (A := A) ctl hst hpc hrun hx19 hx20 hx21 hx23 hx26 hx29) ?_
  intro s3 hpc3 hrun3 ⟨hst3, hpstate3, hx2_3, hx8_3, hx19_3, hx20_3, hx21_3, hx23_3, hx26_3, hx29_3⟩
  set P3 := ((sp' + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
    ((sp' + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64)) ∗
    wireSignalMessageOf A (sp' + 176#64) emptyProtoSignalMessage ∗
    ((sp' + 288#64) ↦₆₄ (sp' + 160#64))
  refine SepWPp.mono_pre (P' := emp ∗ (P3 ∗ F1))
    (by rw [emp_sepConj]; exact Entails.refl _) ?_
  refine SepWPp.bind_frame_entails
    (prologue_b8_gt9_to_f0_wp ctl hgt9 hlt hst3 hpc3 hrun3
      hpstate3 hx2_3 hx8_3 hx19_3 hx20_3 hx21_3 hx23_3 hx26_3 hx29_3) ?_
  intro s4 hpc4 hrun4 ⟨hregs4, ⟨_, hsp4, hF4, hsym4, htr4⟩, hx28_4, hx27_4, hx2_4⟩
  rw [emp_sepConj]
  dsimp only [P3, F1]
  have hrest_split : ((x.bytesA + 1#64) ↦ₛ rest) =
      ((x.bytesA + 1#64) ↦ₛ (b1 :: bs1)) ∗
        ((x.bytesA + 1#64 + BitVec.ofNat 64 (rest.length - 8)) ↦ₛ rest.drop (rest.length - 8)) := by
    have hs := (pointsToBytes_take_drop (x.bytesA + 1#64) rest (rest.length - 8) (by omega)).symm
    rw [← hbs_eq, hcons] at hs
    exact hs
  have hcursor : sliceCursorAt (sp' + 160#64) (x.bytesA + 1#64) (b1 :: bs1) =
      ((sp' + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
        ((sp' + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64)) ∗
        ((x.bytesA + 1#64) ↦ₛ (b1 :: bs1)) := by
    unfold sliceCursorAt
    rw [hbv_len]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  set F2 := memRegion sp' 160 ∗ memRegion (sp' + 344#64) 8 ∗
    (x.bytesA ↦₈ b0) ∗
    ((x.bytesA + 1#64 + BitVec.ofNat 64 (rest.length - 8)) ↦ₛ rest.drop (rest.length - 8))
  refine SepWPp.mono_pre (P' :=
      (sliceCursorAt (sp' + 160#64) (x.bytesA + 1#64) (b1 :: bs1) ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageOf A (sp' + 176#64) emptyProtoSignalMessage) ∗ F2)
    (by
      rw [hrest_split, hcursor]
      dsimp only [F2]
      apply entails_of_eq; ac_rfl) ?_
  have hx2_4' : s4.readReg64 .x2 = BitVec.ofNat 64 (b1 :: bs1).length := by
    rw [hx2_4, hbv_len]
  have hloop := decodeLoop_f0_wp hS hvarint hint32 hskip hbytes (fuel := bs1.length)
    (m := emptyProtoSignalMessage) (ptr := x.bytesA + 1#64)
    hpc4 hrun4 hregs4 hx28_4 hx27_4 hx2_4' hsp4 hF4 hsym4 htr4
    (Nat.le_refl _) (by omega)
  refine SepWPp.frame_tryFrom hloop fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  have hdec : decodeLoop (bs1.length + 1) emptyProtoSignalMessage (b1 :: bs1) = decode bs := by
    rw [hcons]; rfl
  rw [hdec]
  dsimp only [loopExitMem, loopPostMem, bs, F2]
  have hbytes_eq : (x.bytesA ↦ₛ x.bytes) =
      (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ (b1 :: bs1)) ∗
        ((x.bytesA + 1#64 + BitVec.ofNat 64 (rest.length - 8)) ↦ₛ rest.drop (rest.length - 8)) := by
    rw [hbs, pointsToBytes_cons, hrest_split]
  rw [h176_split, h64_split, hbytes_eq]
  have h288 := pointsTo64_entails_memRegion (sp' + 288#64) (sp' + 160#64)
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left h288)))
  dsimp only [sp']
  apply entails_of_eq; ac_rfl

/-! ## Full assembly: `+0x088 → +0x440`, `+0x044 → +0x440`, `+0x000 → +0x440`, and `subroutine_ok` -/

/-- Specification of the post-loop block (`+0x3b0..+0x764` → `+0x440`) when `9 < x.bytes.length`
and `3#8 ≤ (x.bytes.headD 0#8) >>> 4 ≤ 4#8`. -/
def TryFromPostOk (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ∀ {x : TryFromGhost} {s0 s : State},
    9 < x.bytes.length →
    x.bytes.length < 2 ^ 32 →
    ¬ ((x.bytes.headD 0#8) >>> 4) < 3#8 →
    ¬ 4#8 < ((x.bytes.headD 0#8) >>> 4) →
    s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x3b0#64 →
    s.status = .Running →
    LoopExitState img s0 (s0.sp - 448#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.bytesA ((x.bytes.headD 0#8).zeroExtend 64) s →
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x440#64) s
      (loopPostMem A (s0.sp - 448#64) x (s.readReg64 .x24) ∗ memRegion x.ret 120 ∗ logOff img)
      (fun sf Pf =>
        EpilogueState img s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 448#64) 352 ∗
          signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff img ∗ A.pool ∗
          stackAt (s0.sp - 448#64) (skipFieldStackX 100)))
      (tryFromQp s0)

theorem memRegion352_split_len9 (sp' : BitVec 64) :
    memRegion sp' 352 =
      memRegion sp' 88 ∗ memRegion (sp' + 88#64) 16 ∗ memRegion (sp' + 104#64) 56 ∗
        memRegion (sp' + 160#64) 16 ∗ memRegion (sp' + 176#64) 112 ∗
        memRegion (sp' + 288#64) 8 ∗ memRegion (sp' + 296#64) 56 := by
  rw [memRegion_split' (n := 88) (k := 264) rfl rfl (by decide),
    memRegion_split' (b := sp' + 88#64) (n := 16) (k := 248) rfl rfl (by decide),
    memRegion_split' (b := sp' + 88#64 + 16#64) (n := 56) (k := 192) rfl rfl (by decide),
    memRegion_split' (b := sp' + 88#64 + 16#64 + 56#64) (n := 16) (k := 176) rfl rfl (by decide),
    memRegion_split' (b := sp' + 88#64 + 16#64 + 56#64 + 16#64) (n := 112) (k := 64) rfl rfl (by decide),
    memRegion_split' (b := sp' + 88#64 + 16#64 + 56#64 + 16#64 + 112#64) (n := 8) (k := 56) rfl rfl (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion352_split_loop (sp' : BitVec 64) :
    memRegion sp' 352 =
      memRegion sp' 176 ∗ memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 64 := by
  rw [memRegion_split' (n := 176) (k := 176) rfl rfl (by decide),
    memRegion_split' (b := sp' + 176#64) (n := 112) (k := 64) rfl rfl (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-- Unified `+0x088 → +0x440` segment when `9 ≤ x.bytes.length` and `3#8 ≤ b0 >>> 4 ≤ 4#8`. -/
theorem prologue_88_to_440_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    (hS : TripleRatchetHooksW img C A S abs)
    (hvarint : DecodeVarintSliceOkW img C A ctl abs)
    (hint32 : Int32MergeOkW img C A ctl abs)
    (hskip : SkipFieldOkW img C A ctl abs)
    (hbytes : BytesMergeOkW img C A ctl abs)
    (hpost : TryFromPostOk img C A ctl abs)
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8} {rest : List (BitVec 8)}
    (hbs : x.bytes = b0 :: rest)
    (hge9 : 9 ≤ x.bytes.length) (hlt : x.bytes.length < 2 ^ 32)
    (hge3 : ¬ (b0 >>> 4) < 3#8) (hle4 : ¬ 4#8 < (b0 >>> 4))
    (hst : EpilogueState img s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x088#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx21 : s.readReg64 .x21 = x.bytesA)
    (hx23 : s.readReg64 .x23 = b0.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x440#64) s
      (memRegion (s0.sp - 448#64) 352 ∗
        memRegion x.ret 120 ∗
        (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) ∗
        logOff img ∗ A.pool ∗ stackAt (s0.sp - 448#64) (skipFieldStackX 100))
      (fun sf Pf =>
        EpilogueState img s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 448#64) 352 ∗
          signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff img ∗
          A.pool ∗ stackAt (s0.sp - 448#64) (skipFieldStackX 100)))
      (tryFromQp s0) := by
  set sp' := s0.sp - 448#64
  by_cases hlen9 : x.bytes.length = 9
  · have hbytes_eq : (x.bytesA ↦ₛ x.bytes) = (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) := by
      rw [hbs, pointsToBytes_cons]
    set F9 := memRegion sp' 88 ∗ memRegion (sp' + 104#64) 56 ∗ memRegion (sp' + 296#64) 56 ∗
      (x.bytesA ↦ₛ x.bytes) ∗ logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)
    refine SepWPp.mono_pre (P' :=
        (memRegion (sp' + 88#64) 16 ∗
          memRegion (sp' + 160#64) 16 ∗
          memRegion (sp' + 176#64) 112 ∗
          memRegion (sp' + 288#64) 8 ∗
          memRegion x.ret 120) ∗ F9)
      (by
        dsimp only [F9, sp']
        rw [memRegion352_split_len9, hbytes_eq]
        apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (prologue_88_len9_wp (A := A) ctl hbs hlen9 hge3 hle4 hst hpc hrun
        hx19 hx20 hx21 hx23 hx26 hx29)
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    rw [memRegion352_split_len9 sp']
    dsimp only [F9, sp']
    apply entails_of_eq; ac_rfl
  · have hgt9 : 9 < x.bytes.length := by omega
    have hhead : x.bytes.headD 0#8 = b0 := by simp [hbs]
    refine SepWPp.mono_pre (P' :=
        (memRegion sp' 176 ∗
          memRegion (sp' + 176#64) 112 ∗
          memRegion (sp' + 288#64) 64 ∗
          (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗
        (memRegion x.ret 120 ∗ logOff img))
      (by
        rw [memRegion352_split_loop sp']
        dsimp only [sp']
        apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.bind_frame_entails
      (prologue_88_gt9_loop_wp ctl hS hvarint hint32 hskip hbytes
        hbs hgt9 (by omega) hst hpc hrun hx19 hx20 hx21 hx23 hx26 hx29) ?_
    intro s5 hpc5 hrun5 hst5
    have hst5' : LoopExitState img s0 (s0.sp - 448#64) x.ret
        (BitVec.ofNat 64 x.bytes.length) x.bytesA ((x.bytes.headD 0#8).zeroExtend 64) s5 :=
      hhead.symm ▸ hst5
    exact hpost hgt9 hlt (hhead ▸ hge3) (hhead ▸ hle4) hpc5 hrun5 hst5'

/-- Unified `+0x044 → +0x440` segment when `9 ≤ x.bytes.length`. -/
theorem prologue_44_to_440_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    (hS : TripleRatchetHooksW img C A S abs)
    (hvarint : DecodeVarintSliceOkW img C A ctl abs)
    (hint32 : Int32MergeOkW img C A ctl abs)
    (hskip : SkipFieldOkW img C A ctl abs)
    (hbytes : BytesMergeOkW img C A ctl abs)
    (hpost : TryFromPostOk img C A ctl abs)
    {x : TryFromGhost} {s0 s : State}
    (hge9 : 9 ≤ x.bytes.length) (hlt : x.bytes.length < 2 ^ 32)
    (hst : EpilogueState img s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x044#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = x.bytesA)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x440#64) s
      (memRegion (s0.sp - 448#64) 352 ∗
        memRegion x.ret 120 ∗
        (x.bytesA ↦ₛ x.bytes) ∗ logOff img ∗
        A.pool ∗ stackAt (s0.sp - 448#64) (skipFieldStackX 100))
      (fun sf Pf =>
        EpilogueState img s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 448#64) 352 ∗
          signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff img ∗
          A.pool ∗ stackAt (s0.sp - 448#64) (skipFieldStackX 100)))
      (tryFromQp s0) := by
  set sp' := s0.sp - 448#64
  rcases hbs : x.bytes with _ | ⟨b0, rest⟩
  · simp [hbs] at hge9
  have hge9' : 9 ≤ x.bytes.length := hge9
  rw [ ← hbs ]
  by_cases hlt3 : (b0 >>> 4) < 3#8
  · set Fv := memRegion sp' 352 ∗ logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)
    refine SepWPp.mono_pre (P' := ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120) ∗ Fv)
      (by dsimp only [Fv, sp']; apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (prologue_44_legacyVer_wp (A := A) ctl hbs hge9' hlt3 hst hpc hrun hx0 hx19)
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    dsimp only [Fv, sp']
    apply entails_of_eq; ac_rfl
  · by_cases hgt4 : 4#8 < (b0 >>> 4)
    · set Fv := memRegion sp' 352 ∗ logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)
      refine SepWPp.mono_pre (P' := ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120) ∗ Fv)
        (by dsimp only [Fv, sp']; apply entails_of_eq; ac_rfl) ?_
      refine SepWPp.frame_tryFrom
        (prologue_44_unrecognizedVer_wp (A := A) ctl hbs hge9' hlt3 hgt4 hst hpc hrun hx0 hx19)
        fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
      refine Entails.trans (sepConj_mono_left hentf) ?_
      dsimp only [Fv, sp']
      apply entails_of_eq; ac_rfl
    · have hbytes_eq : (x.bytesA ↦ₛ x.bytes) = (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) := by
        rw [hbs, pointsToBytes_cons]
      have hvalid : SepWPp (tripleRatchetProgAtW img.base C ctl abs)
          ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x088#64) s
          (x.bytesA ↦₈ b0)
          (fun s2 P2 =>
            (EpilogueState img s0 sp' s2 ∧
            s2.readReg64 .x19 = x.ret ∧
            s2.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧
            s2.readReg64 .x21 = x.bytesA ∧
            s2.readReg64 .x23 = b0.zeroExtend 64 ∧
            s2.readReg64 .x26 = 0x8000000000000002#64 ∧
            s2.readReg64 .x29 = sp' + 352#64) ∧
            (P2 ⊢ (x.bytesA ↦₈ b0)))
          (tryFromQp s0) := by
        intro R hm hL
        obtain ⟨sf, hsteps, hex⟩ :=
          prologue_44_validVer_wp ctl hlt3 hgt4 hst hpc hrun hx0 hx19 hx20 hx29 R hm hL
        rcases hex with ⟨hpc1, hrun1, Pf, hmf, ⟨h1, h2, h3, h4, h5, h6, h7, hent⟩, hv⟩ | hpan
        · exact ⟨sf, hsteps, Or.inl ⟨hpc1, hrun1, Pf, hmf, ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hent⟩, hv⟩⟩
        · exact ⟨sf, hsteps, Or.inr hpan⟩
      set Fv := memRegion sp' 352 ∗ memRegion x.ret 120 ∗ ((x.bytesA + 1#64) ↦ₛ rest) ∗
        logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)
      refine SepWPp.mono_pre (P' := (x.bytesA ↦₈ b0) ∗ Fv)
        (by dsimp only [Fv, sp']; rw [hbytes_eq]; apply entails_of_eq; ac_rfl) ?_
      refine SepWPp.bind_frame_entails hvalid ?_
      intro s2 hpc2 hrun2 ⟨hst2, hx19_2, hx20_2, hx21_2, hx23_2, hx26_2, hx29_2⟩
      refine SepWPp.mono_pre (P' :=
          memRegion sp' 352 ∗ memRegion x.ret 120 ∗
          (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) ∗
          logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
        (by dsimp only [Fv, sp']; apply entails_of_eq; ac_rfl) ?_
      exact prologue_88_to_440_wp ctl hS hvarint hint32 hskip hbytes hpost
        hbs hge9' hlt hlt3 hgt4 hst2 hpc2 hrun2 hx19_2 hx20_2 hx21_2 hx23_2 hx26_2 hx29_2

/-- Full `+0x000 → +0x440` segment for all inputs `x.bytes.length < 2 ^ 32`. -/
theorem tryFrom_entry_to_440_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    (hS : TripleRatchetHooksW img C A S abs)
    (hvarint : DecodeVarintSliceOkW img C A ctl abs)
    (hint32 : Int32MergeOkW img C A ctl abs)
    (hskip : SkipFieldOkW img C A ctl abs)
    (hbytes : BytesMergeOkW img C A ctl abs)
    (hpost : TryFromPostOk img C A ctl abs)
    {x : TryFromGhost} {s0 : State}
    (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (hx0 : s0.readReg64 .x0 = x.bytesA)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x440#64) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ logOff img ∗
        stackAt s0.sp smallRootStack ∗ A.pool)
      (fun sf Pf => EpilogueState img s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ stackAt (s0.sp - 448#64) tryFromSubStack ∗
          memRegion (s0.sp - 448#64) 352 ∗
          calleeSavedAt (s0.sp - 448#64) s0 ∗
          signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff img ∗ A.pool))
      (tryFromQp s0) := by
  by_cases hlt9 : x.bytes.length < 9
  · exact prologue_tooShort_wp ctl hlt9 hpc hrun hsp hF hsym hx0 hx1 hx8
  · have hge9 : 9 ≤ x.bytes.length := by omega
    set sp' := s0.sp - 448#64
    have hstk1 := stackAt_smallRoot_split s0.sp
    have hstk2 := stackAt_sub_split sp' (skipFieldStackX 100) tryFromSubStack
    have hentry : SepWPp (tripleRatchetProgAtW img.base C ctl abs)
        ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x044#64) s0
        (memRegion (sp' + 352#64) 96)
        (fun s1 P1 =>
          (EpilogueState img s0 sp' s1 ∧
          s1.readReg64 .x0 = x.bytesA ∧
          s1.readReg64 .x19 = x.ret ∧
          s1.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧
          s1.readReg64 .x29 = sp' + 352#64) ∧
          (P1 ⊢ calleeSavedAt sp' s0))
        (tryFromQp s0) := by
      intro R hm hL
      obtain ⟨sf, hsteps, hex⟩ :=
        prologue_entry_ge9_wp ctl hge9 (by omega) hpc hrun hsp hF hsym hx0 hx1 hx8 R hm hL
      rcases hex with ⟨hpc1, hrun1, Pf, hmf, ⟨h1, h2, h3, h4, h5, hent⟩, hv⟩ | hpan
      · exact ⟨sf, hsteps, Or.inl ⟨hpc1, hrun1, Pf, hmf, ⟨⟨h1, h2, h3, h4, h5⟩, hent⟩, hv⟩⟩
      · exact ⟨sf, hsteps, Or.inr hpan⟩
    set Fe := (memRegion sp' 352 ∗ memRegion x.ret 120 ∗ (x.bytesA ↦ₛ x.bytes) ∗
      logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗
      memRegion (sp' - BitVec.ofNat 64 tryFromSubStack) (tryFromSubStack - skipFieldStackX 100)
    refine SepWPp.mono_pre (P' := memRegion (sp' + 352#64) 96 ∗ Fe)
      (by
        rw [hstk1, hstk2]
        dsimp only [Fe, sp']
        apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.bind_frame_entails hentry ?_
    intro s1 hpc1 hrun1 ⟨hst1, hx0_1, hx19_1, hx20_1, hx29_1⟩
    dsimp only [Fe]
    refine SepWPp.mono_pre (P' :=
        (memRegion sp' 352 ∗ memRegion x.ret 120 ∗ (x.bytesA ↦ₛ x.bytes) ∗
          logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗
        (calleeSavedAt sp' s0 ∗
          memRegion (sp' - BitVec.ofNat 64 tryFromSubStack) (tryFromSubStack - skipFieldStackX 100)))
      (by apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (prologue_44_to_440_wp ctl hS hvarint hint32 hskip hbytes hpost
        hge9 hlt hst1 hpc1 hrun1 hx0_1 hx19_1 hx20_1 hx29_1)
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    rw [hstk2]
    dsimp only [sp']
    apply entails_of_eq; ac_rfl

/-- Main subroutine correctness theorem for `SignalMessage::try_from` (`0x25868`),
parameterized by `TryFromPostOk`. -/
theorem tryFrom_subroutine_ok_of_post {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    (hS : TripleRatchetHooksW img C A S abs)
    (hvarint : DecodeVarintSliceOkW img C A ctl abs)
    (hint32 : Int32MergeOkW img C A ctl abs)
    (hskip : SkipFieldOkW img C A ctl abs)
    (hbytes : BytesMergeOkW img C A ctl abs)
    (hpost : TryFromPostOk img C A ctl abs) :
    subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName)
      (tryFromSpec A img) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hL
  dsimp only [tryFromSpec, Spec.inImage] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hsym⟩, ⟨hx0, hx1_nat, hlt, hx8⟩, hmem⟩
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hmem' : s0.mem ⊨
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ logOff img ∗
        stackAt s0.sp smallRootStack ∗ A.pool) ∗ R := by
    ac_nf at hmem ⊢
  have h1 : SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x440#64) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ logOff img ∗
        stackAt s0.sp smallRootStack ∗ A.pool)
      (fun sm Pm =>
        EpilogueState img s0 (s0.sp - 448#64) sm ∧
        (Pm ⊢ stackAt (s0.sp - 448#64) tryFromSubStack ∗
          memRegion (s0.sp - 448#64) 352 ∗
          calleeSavedAt (s0.sp - 448#64) s0 ∗
          signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff img ∗ A.pool))
      (tryFromQp s0) :=
    tryFrom_entry_to_440_wp ctl hS hvarint hint32 hskip hbytes hpost
      hlt hpc hrun hsp hF hsym hx0 hx1 hx8
  have hfull : SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      (s0.readReg64 .x30) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ logOff img ∗
        stackAt s0.sp smallRootStack ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (tryFromSpec A img).post x s0 sf))
      (tryFromQp s0) := by
    refine SepWPp.bind h1 ?_
    intro sm Pm hpcm hrunm ⟨hstm, hentm⟩
    exact SepWPp.mono_pre hentm
      (epilogue_440_wp (A := A) (x := x) ctl hstm hpcm hrunm)
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ | ⟨hpan, Pf, hmf, htr_f⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩,
      Satisfies.mono (sepConj_mono_left hent_f) hmf⟩
  · exact Or.inr (Or.inl ⟨hpan, htr_f R hmf⟩)
  · exact (allowPanic_not_exited hoom).elim

/-- Root theorem `TryFromRunStmt` derived from `tryFrom_subroutine_ok_of_post` via `root_of_tripleRatchetProgAt`. -/
theorem tryFrom_run_stmt_of_post {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    {img : Obj.Image}
    (hvarint : TripleRatchetHooks C A S abs → DecodeVarintSliceOkW img C A ctl (tripleRatchetExterns C ctl abs))
    (hint32 : TripleRatchetHooks C A S abs → Int32MergeOkW img C A ctl (tripleRatchetExterns C ctl abs))
    (hskip : TripleRatchetHooks C A S abs → SkipFieldOkW img C A ctl (tripleRatchetExterns C ctl abs))
    (hbytes : TripleRatchetHooks C A S abs → BytesMergeOkW img C A ctl (tripleRatchetExterns C ctl abs))
    (hpost : TripleRatchetHooks C A S abs → TryFromPostOk img C A ctl (tripleRatchetExterns C ctl abs)) :
    TryFromRunStmt C A ctl S abs img :=
  fun hS himg =>
    root_of_tripleRatchetProgAt himg
      (tryFrom_subroutine_ok_of_post ctl
        (TripleRatchetHooksW.of_tripleRatchetProgAt img C A ctl S abs hS)
        (hvarint hS) (hint32 hS)
        (hskip hS) (hbytes hS) (hpost hS))

/-! ## Relocatable `[LibsignalPlacement]` Prologue, Epilogue, and Subroutine Theorems (Block `85`) -/

def EpilogueStatePlaced [LibsignalPlacement] (s0 : State) (sp' : BitVec 64) (s : State) : Prop :=
  s.sp = sp' ∧ s.spAligned = true ∧ LibsignalCodeRoLoaded lsmpl s.mem ∧ s.trace = s0.trace

theorem EpilogueStatePlaced.of_steps [LibsignalPlacement] {s0 s1 s2 : State} {sp' : BitVec 64}
    (hcl : LibsignalCodeRoLoaded lsmpl s2.mem)
    (hsp : s2.sp = sp') (hsp0 : s1.sp = sp') (hal : s1.spAligned = true)
    (htr : s2.trace = s0.trace) :
    EpilogueStatePlaced s0 sp' s2 := by
  refine ⟨hsp, ?_, hcl, htr⟩
  rw [State.spAligned, hsp, ← hsp0, ← State.spAligned]
  exact hal

def tryFromPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec TryFromGhost :=
  { pre := fun x s =>
      ⌜s.readReg64 .x0 = x.bytesA ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
        x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret⌝ ∗
        (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ logOff tryFromPlacedImg ∗
        stackAt s.sp smallRootStack ∗ A.pool
    post := fun x s0 sf =>
      ⌜sf.trace = s0.trace⌝ ∗ signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
        (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗ stackAt s0.sp smallRootStack ∗ A.pool
    onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

theorem epilogue_440_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State}
    (hst : EpilogueStatePlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x440#64)
    (hrun : s.status = .Running) :
    SepWPp (tryFromPlacedProg H)
      (s0.readReg64 .x30) s
      (stackAt (s0.sp - 448#64) tryFromSubStack ∗
        memRegion (s0.sp - 448#64) 352 ∗
        calleeSavedAt (s0.sp - 448#64) s0 ∗
        signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
        (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (tryFromPlacedSpec A).post x s0 sf))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  unfold calleeSavedAt
  simp only [sepConj_assoc]
  refine SepWPp.of_sepWP_end_placed hcl ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  refine ⟨by simp [arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], hv⟩
  · dsimp only [tryFromPlacedSpec]
    rw [pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
    have hstk := stackAt_smallRoot_unsplit s0.sp s0
    unfold calleeSavedAt at hstk
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk))))
    apply entails_of_eq
    ac_rfl


theorem prologue_tooShort_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : TryFromGhost} {s0 : State}
    (hlt9 : x.bytes.length < 9)
    (hpc : s0.pc = (blkPl_85).base)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (_hx0 : s0.readReg64 .x0 = x.bytesA)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ logOff tryFromPlacedImg ∗
        stackAt s0.sp smallRootStack ∗ A.pool)
      (fun sf Pf => EpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ stackAt (s0.sp - 448#64) tryFromSubStack ∗
          memRegion (s0.sp - 448#64) 352 ∗
          calleeSavedAt (s0.sp - 448#64) s0 ∗
          signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗ A.pool))
      (tryFromQp s0) := by
  have hcond := cond_hi_len_of_lt9 hlt9
  have hout := tryFrom_eq_tooShort hlt9
  rw [stackAt_smallRoot_split s0.sp]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono (memRegion120_split24 x.ret)
      (sepConj_mono_right (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (memRegion96_cells (s0.sp - 448#64)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w19 => SepWPp.exists_pre fun w20 =>
    SepWPp.exists_pre fun w21 => SepWPp.exists_pre fun w22 =>
    SepWPp.exists_pre fun w23 => SepWPp.exists_pre fun w24 =>
    SepWPp.exists_pre fun w25 => SepWPp.exists_pre fun w26 =>
    SepWPp.exists_pre fun w27 => SepWPp.exists_pre fun w28 =>
    SepWPp.exists_pre fun w30 => SepWPp.exists_pre fun w29 =>
    SepWPp.exists_pre fun r2 => SepWPp.exists_pre fun r1 =>
    SepWPp.exists_pre fun r0 => ?_
  refine SepWPp.of_sepWP_end_placed hcl ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  refine ⟨⟨by simp [arm64_norm], ?_, hcl1, by simp [arm64_norm]⟩, ?_⟩
  · rw [State.spAligned]
    simpa [arm64_norm] using spAligned_sub448 hsp
  · have hmsg := spe_tooShort_intro A x.ret x.bytes.length hout
    simp only [errTag, speWord] at hmsg
    have hcs :
        ((s0.sp - 448#64 + 352#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 448#64 + 360#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 448#64 + 368#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
        ((s0.sp - 448#64 + 376#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
        ((s0.sp - 448#64 + 384#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
        ((s0.sp - 448#64 + 392#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 448#64 + 400#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 448#64 + 408#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 448#64 + 416#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 448#64 + 424#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 448#64 + 432#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 448#64 + 440#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
        calleeSavedAt (s0.sp - 448#64) s0 := Entails.refl _
    refine Entails.trans (Q := stackAt (s0.sp - 448#64) tryFromSubStack ∗
        memRegion (s0.sp - 448#64) 352 ∗
        (((s0.sp - 448#64 + 352#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 448#64 + 360#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 448#64 + 368#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
          ((s0.sp - 448#64 + 376#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
          ((s0.sp - 448#64 + 384#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
          ((s0.sp - 448#64 + 392#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
          ((s0.sp - 448#64 + 400#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
          ((s0.sp - 448#64 + 408#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
          ((s0.sp - 448#64 + 416#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((s0.sp - 448#64 + 424#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 448#64 + 432#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((s0.sp - 448#64 + 440#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) ∗
        ((x.ret ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
          ((x.ret + 8#64) ↦₆₄ 9223372036854775811#64) ∗
          ((x.ret + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          memRegion (x.ret + 24#64) 96) ∗
        (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗ A.pool)
      (by apply entails_of_eq; ac_rfl) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono hcs (sepConj_mono_left hmsg)))


theorem prologue_entry_ge9_wp_placed [LibsignalPlacement] {H : LibsignalHooks}
    {x : TryFromGhost} {s0 : State}
    (hge9 : 9 ≤ x.bytes.length) (hlt : x.bytes.length < 2 ^ 63)
    (hpc : s0.pc = (blkPl_85).base)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.bytesA)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x044#64) s0
      (memRegion (s0.sp - 448#64 + 352#64) 96)
      (fun s1 P1 =>
        EpilogueStatePlaced s0 (s0.sp - 448#64) s1 ∧
        s1.readReg64 .x0 = x.bytesA ∧
        s1.readReg64 .x19 = x.ret ∧
        s1.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧
        s1.readReg64 .x29 = s0.sp - 448#64 + 352#64 ∧
        (P1 ⊢ calleeSavedAt (s0.sp - 448#64) s0))
      (tryFromQp s0) := by
  have hcond := cond_hi_len_of_ge9 hge9 hlt
  refine SepWPp.mono_pre (memRegion96_cells (s0.sp - 448#64)) ?_
  refine SepWPp.exists_pre fun w19 => SepWPp.exists_pre fun w20 =>
    SepWPp.exists_pre fun w21 => SepWPp.exists_pre fun w22 =>
    SepWPp.exists_pre fun w23 => SepWPp.exists_pre fun w24 =>
    SepWPp.exists_pre fun w25 => SepWPp.exists_pre fun w26 =>
    SepWPp.exists_pre fun w27 => SepWPp.exists_pre fun w28 =>
    SepWPp.exists_pre fun w30 => SepWPp.exists_pre fun w29 => ?_
  refine SepWPp.of_sepWP_end_placed hcl ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  refine ⟨⟨by simp [arm64_norm], ?_, hcl1, by simp [arm64_norm]⟩,
    by simp [hx0, arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], Entails.refl _⟩
  rw [State.spAligned]
  simpa [arm64_norm] using spAligned_sub448 hsp


theorem prologue_44_legacyVer_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8} {rest : List (BitVec 8)}
    (hbs : x.bytes = b0 :: rest)
    (hge9 : 9 ≤ x.bytes.length)
    (hlt3 : (b0 >>> 4) < 3#8)
    (hst : EpilogueStatePlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x044#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = x.bytesA)
    (hx19 : s.readReg64 .x19 = x.ret) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120)
      (fun sf Pf => EpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcond := cond_cs_ver_of_lt3 hlt3
  have hout : SignalMessage.tryFrom protoSignalCodec x.bytes =
      .error (.legacyCiphertextVersion (b0 >>> 4)) := by
    rw [hbs]
    exact tryFrom_eq_legacyVer (hbs ▸ hge9) hlt3
  have hbytes : (x.bytesA ↦ₛ x.bytes) = (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) := by
    rw [hbs, pointsToBytes_cons]
  rw [hbytes]
  refine SepWPp.mono_pre (sepConj_mono_right (memRegion120_split17 x.ret)) ?_
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun b16 => SepWPp.exists_pre fun r1 =>
    SepWPp.exists_pre fun r0 => ?_
  refine SepWPp.of_sepWP_end_placed hcl ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  refine ⟨EpilogueStatePlaced.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
    (by simp [htr, arm64_norm]), ?_⟩
  have hmsg := spe_legacyVer_intro A x.ret (b0 >>> 4) hout
  simp only [errTag, speWord, BitVec.reduceAdd] at hmsg
  refine Entails.trans (Q := ((x.ret ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
      ((x.ret + 8#64) ↦₆₄ 9223372036854775812#64) ∗
      ((x.ret + 16#64) ↦₈ (b0 >>> 4)) ∗
      memRegion (x.ret + 17#64) 103) ∗
      ((x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest)))
    (by apply entails_of_eq; ac_rfl) ?_
  rw [← hbytes]
  exact sepConj_mono_left hmsg


theorem prologue_44_unrecognizedVer_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8} {rest : List (BitVec 8)}
    (hbs : x.bytes = b0 :: rest)
    (hge9 : 9 ≤ x.bytes.length)
    (hge3 : ¬ (b0 >>> 4) < 3#8) (hgt4 : 4#8 < (b0 >>> 4))
    (hst : EpilogueStatePlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x044#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = x.bytesA)
    (hx19 : s.readReg64 .x19 = x.ret) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120)
      (fun sf Pf => EpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcond1 := cond_cs_ver_of_ge3 hge3
  have hcond2 := cond_ls_ver_of_gt4 hgt4
  have hout : SignalMessage.tryFrom protoSignalCodec x.bytes =
      .error (.unrecognizedCiphertextVersion (b0 >>> 4)) := by
    rw [hbs]
    exact tryFrom_eq_unrecognizedVer (hbs ▸ hge9) hge3 hgt4
  have hbytes : (x.bytesA ↦ₛ x.bytes) = (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) := by
    rw [hbs, pointsToBytes_cons]
  rw [hbytes]
  refine SepWPp.mono_pre (sepConj_mono_right (memRegion120_split17 x.ret)) ?_
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun b16 => SepWPp.exists_pre fun r1 =>
    SepWPp.exists_pre fun r0 => ?_
  refine SepWPp.of_sepWP_end_placed hcl ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  refine ⟨EpilogueStatePlaced.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
    (by simp [htr, arm64_norm]), ?_⟩
  have hmsg := spe_unrecognizedVer_intro A x.ret (b0 >>> 4) hout
  simp only [errTag, speWord, BitVec.reduceAdd] at hmsg
  refine Entails.trans (Q := ((x.ret ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
      ((x.ret + 8#64) ↦₆₄ 9223372036854775813#64) ∗
      ((x.ret + 16#64) ↦₈ (b0 >>> 4)) ∗
      memRegion (x.ret + 17#64) 103) ∗
      ((x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest)))
    (by apply entails_of_eq; ac_rfl) ?_
  rw [← hbytes]
  exact sepConj_mono_left hmsg


theorem prologue_44_validVer_wp_placed [LibsignalPlacement] {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8}
    (hge3 : ¬ (b0 >>> 4) < 3#8) (hle4 : ¬ 4#8 < (b0 >>> 4))
    (hst : EpilogueStatePlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x044#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = x.bytesA)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x088#64) s
      (x.bytesA ↦₈ b0)
      (fun s2 P2 =>
        EpilogueStatePlaced s0 (s0.sp - 448#64) s2 ∧
        s2.readReg64 .x19 = x.ret ∧
        s2.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧
        s2.readReg64 .x21 = x.bytesA ∧
        s2.readReg64 .x23 = b0.zeroExtend 64 ∧
        s2.readReg64 .x26 = 0x8000000000000002#64 ∧
        s2.readReg64 .x29 = s0.sp - 448#64 + 352#64 ∧
        (P2 ⊢ (x.bytesA ↦₈ b0)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcond1 := cond_cs_ver_of_ge3 hge3
  have hcond2 := cond_ls_ver_of_le4 hle4
  refine SepWPp.of_sepWP_end_placed hcl ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  refine ⟨EpilogueStatePlaced.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
    (by simp [htr, arm64_norm]),
    by simp [hx19, arm64_norm], by simp [hx20, arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [hx29, arm64_norm], Entails.refl _⟩


theorem prologue_88_init_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8}
    (hst : EpilogueStatePlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x088#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx21 : s.readReg64 .x21 = x.bytesA)
    (hx23 : s.readReg64 .x23 = b0.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x0b8#64) s
      (memRegion (s0.sp - 448#64 + 160#64) 16 ∗
        memRegion (s0.sp - 448#64 + 176#64) 112 ∗
        memRegion (s0.sp - 448#64 + 288#64) 8)
      (fun s3 P3 =>
        EpilogueStatePlaced s0 (s0.sp - 448#64) s3 ∧
        s3.pstate = subsPState64 (BitVec.ofNat 64 x.bytes.length) 9#64 ∧
        s3.readReg64 .x2 = BitVec.ofNat 64 x.bytes.length - 9#64 ∧
        s3.readReg64 .x8 = s0.sp - 448#64 + 160#64 ∧
        s3.readReg64 .x19 = x.ret ∧
        s3.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧
        s3.readReg64 .x21 = x.bytesA ∧
        s3.readReg64 .x23 = b0.zeroExtend 64 ∧
        s3.readReg64 .x26 = 0x8000000000000002#64 ∧
        s3.readReg64 .x29 = s0.sp - 448#64 + 352#64 ∧
        (P3 ⊢ ((s0.sp - 448#64 + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
          ((s0.sp - 448#64 + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64)) ∗
          wireSignalMessageOf A (s0.sp - 448#64 + 176#64) emptyProtoSignalMessage ∗
          ((s0.sp - 448#64 + 288#64) ↦₆₄ (s0.sp - 448#64 + 160#64))))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  set sp' := s0.sp - 448#64
  rw [memRegion_eight (sp' + 288#64)]
  refine SepWPp.mono_pre
    (sepConj_mono (memRegion16_split8_8' (sp' + 160#64))
      (sepConj_mono_left (memRegion112_emptyMsg_cells sp'))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w288 =>
    SepWPp.exists_pre fun w280 => SepWPp.exists_pre fun w272 =>
    SepWPp.exists_pre fun w248 => SepWPp.exists_pre fun w224 =>
    SepWPp.exists_pre fun w200 => SepWPp.exists_pre fun w176 =>
    SepWPp.exists_pre fun c1 => SepWPp.exists_pre fun c0 => ?_
  refine SepWPp.of_sepWP_end_placed hcl ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  refine ⟨EpilogueStatePlaced.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
    (by simp [htr, arm64_norm]),
    by simp [arm64_norm],
    by simp [BitVec.sub_eq_add_neg, arm64_norm],
    by simp [arm64_norm],
    by simp [hx19, arm64_norm],
    by simp [hx20, arm64_norm],
    by simp [hx21, arm64_norm],
    by simp [hx23, arm64_norm],
    by simp [hx26, arm64_norm],
    by simp [hx29, arm64_norm], ?_⟩
  have hempty := emptyMsg_cells_entails_wireSignalMessageOf A sp'
  simp only [noneCap] at hempty
  refine Entails.trans (Q := ((sp' + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
      ((sp' + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64)) ∗
      (((sp' + 176#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (sp' + 184#64) 16 ∗
        ((sp' + 200#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (sp' + 208#64) 16 ∗
        ((sp' + 224#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (sp' + 232#64) 16 ∗
        ((sp' + 248#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (sp' + 256#64) 16 ∗
        ((sp' + 272#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 276#64) 4 ∗
        ((sp' + 280#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 284#64) 4) ∗
      ((sp' + 288#64) ↦₆₄ (sp' + 160#64)))
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hempty))


theorem prologue_b8_gt9_to_f0_wp_placed [LibsignalPlacement] {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8}
    (hgt9 : 9 < x.bytes.length) (hlt : x.bytes.length < 2 ^ 63)
    (hst : EpilogueStatePlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x0b8#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState64 (BitVec.ofNat 64 x.bytes.length) 9#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 x.bytes.length - 9#64)
    (hx8 : s.readReg64 .x8 = s0.sp - 448#64 + 160#64)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx21 : s.readReg64 .x21 = x.bytesA)
    (hx23 : s.readReg64 .x23 = b0.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x0f0#64) s
      emp
      (fun s4 P4 =>
        (LoopRegs (s0.sp - 448#64) x.ret (BitVec.ofNat 64 x.bytes.length)
          x.bytesA (b0.zeroExtend 64) s4 ∧
        EpilogueStatePlaced s0 (s0.sp - 448#64) s4 ∧
        s4.readReg64 .x28 = s0.sp - 448#64 + 160#64 ∧
        s4.readReg64 .x27 = s0.sp - 448#64 + 168#64 ∧
        s4.readReg64 .x2 = BitVec.ofNat 64 x.bytes.length - 9#64) ∧
        (P4 ⊢ emp))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcond := cond_eq_len_of_gt9 hgt9 hlt
  refine SepWPp.of_sepWP_end_placed hcl ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  refine ⟨⟨⟨by simp [hsp_eq, arm64_norm], by simp [hx29, arm64_norm],
      by simp [hx26, arm64_norm], by simp [arm64_norm],
      by simp [hx23, arm64_norm], by simp [arm64_norm],
      by simp [hx21, arm64_norm], by simp [hx20, arm64_norm],
      by simp [hx19, arm64_norm]⟩,
    EpilogueStatePlaced.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
      (by simp [htr, arm64_norm]),
    by simp [arm64_norm],
    by simp [arm64_norm],
    by simp [hx2, arm64_norm]⟩,
    Entails.refl _⟩


theorem prologue_b8_len9_to_460_wp_placed [LibsignalPlacement] {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State}
    {s88 s96 rkPtr ctPtr pqPtr adPtr : BitVec 64}
    (hst : EpilogueStatePlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x0b8#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState64 9#64 9#64)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x460#64) s
      (((s0.sp - 448#64 + 88#64) ↦₆₄ s88) ∗ ((s0.sp - 448#64 + 96#64) ↦₆₄ s96) ∗
        ((s0.sp - 448#64 + 176#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 184#64) ↦₆₄ rkPtr) ∗
        ((s0.sp - 448#64 + 200#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 208#64) ↦₆₄ ctPtr) ∗
        ((s0.sp - 448#64 + 224#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 232#64) ↦₆₄ pqPtr) ∗
        ((s0.sp - 448#64 + 248#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 256#64) ↦₆₄ adPtr))
      (fun s4 P4 =>
        (EpilogueStatePlaced s0 (s0.sp - 448#64) s4 ∧
        s4.readReg64 .x1 = noneCap ∧
        s4.readReg64 .x19 = x.ret ∧
        s4.readReg64 .x22 = noneCap ∧
        s4.readReg64 .x25 = noneCap ∧
        s4.readReg64 .x26 = 0x8000000000000002#64 ∧
        s4.readReg64 .x27 = noneCap) ∧
        (P4 ⊢ memRegion (s0.sp - 448#64 + 88#64) 16 ∗
          ((s0.sp - 448#64 + 176#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 184#64) ↦₆₄ rkPtr) ∗
          ((s0.sp - 448#64 + 200#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 208#64) ↦₆₄ ctPtr) ∗
          ((s0.sp - 448#64 + 224#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 232#64) ↦₆₄ pqPtr) ∗
          ((s0.sp - 448#64 + 248#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 256#64) ↦₆₄ adPtr)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  set sp' := s0.sp - 448#64
  dsimp only [noneCap]
  refine SepWPp.of_sepWP_end_placed hcl ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  refine ⟨⟨EpilogueStatePlaced.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
    (by simp [htr, arm64_norm]),
    by simp [arm64_norm],
    by simp [hx19, arm64_norm],
    by simp [arm64_norm],
    by simp [arm64_norm],
    by simp [hx26, arm64_norm],
    by simp [arm64_norm]⟩, ?_⟩
  have h16 := pointsTo64_pair_entails_memRegion16 (sp' + 88#64) adPtr pqPtr
  have ha96 : sp' + 88#64 + 8#64 = sp' + 96#64 := by bv_omega
  rw [ha96] at h16
  rw [← sepConj_assoc ((sp' + 88#64) ↦₆₄ adPtr)]
  exact sepConj_mono_left h16


theorem prologue_460_len9_to_440_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State}
    {rkPtr rkLen ctPtr ctLen pqPtr pqLen adPtr adLen : BitVec 64}
    {cVal pcVal : BitVec 32}
    {out : Except SignalProtocolError SignalMessage}
    (hout : out = .error .invalidProtobufEncoding)
    (hst : EpilogueStatePlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x460#64)
    (hrun : s.status = .Running)
    (hx1 : s.readReg64 .x1 = noneCap)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx22 : s.readReg64 .x22 = noneCap)
    (hx25 : s.readReg64 .x25 = noneCap)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx27 : s.readReg64 .x27 = noneCap) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      (memRegion x.ret 120 ∗
        ((s0.sp - 448#64 + 176#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 184#64) ↦₆₄ rkPtr) ∗
        ((s0.sp - 448#64 + 192#64) ↦₆₄ rkLen) ∗
        ((s0.sp - 448#64 + 200#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 208#64) ↦₆₄ ctPtr) ∗
        ((s0.sp - 448#64 + 216#64) ↦₆₄ ctLen) ∗
        ((s0.sp - 448#64 + 224#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 232#64) ↦₆₄ pqPtr) ∗
        ((s0.sp - 448#64 + 240#64) ↦₆₄ pqLen) ∗
        ((s0.sp - 448#64 + 248#64) ↦₆₄ noneCap) ∗ ((s0.sp - 448#64 + 256#64) ↦₆₄ adPtr) ∗
        ((s0.sp - 448#64 + 264#64) ↦₆₄ adLen) ∗
        ((s0.sp - 448#64 + 272#64) ↦₃₂ 0#32) ∗ ((s0.sp - 448#64 + 276#64) ↦₃₂ cVal) ∗
        ((s0.sp - 448#64 + 280#64) ↦₃₂ 0#32) ∗ ((s0.sp - 448#64 + 284#64) ↦₃₂ pcVal))
      (fun sf Pf =>
        EpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 448#64 + 176#64) 112 ∗
          signalMessageResultAt A [] x.ret out))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  set sp' := s0.sp - 448#64
  dsimp only [noneCap] at hx1 hx22 hx25 hx27 ⊢
  refine SepWPp.mono_pre (sepConj_mono_left (memRegion120_split16' x.ret)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun r1 => SepWPp.exists_pre fun r0 => ?_
  refine SepWPp.of_sepWP_end_placed hcl ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  refine ⟨EpilogueStatePlaced.of_steps hcl1 (by simp [hsp_eq, arm64_norm]) hsp_eq hsp
    (by simp [htr, arm64_norm]), ?_⟩
  have h112 := cells112_entails_memRegion112 sp'
    9223372036854775810#64 rkPtr rkLen
    (bv% (2 ^ 64 - 1)) ctPtr ctLen
    (bv% (2 ^ 64 - 1)) pqPtr pqLen
    (bv% (2 ^ 64 - 1)) adPtr adLen
    0#32 cVal 0#32 pcVal
  have hmsg := spe_invalidProto_intro' A x.ret hout
  simp only [errTag, speWord] at hmsg
  refine Entails.trans (Q :=
      (((sp' + 176#64) ↦₆₄ 9223372036854775810#64) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗ ((sp' + 192#64) ↦₆₄ rkLen) ∗
        ((sp' + 200#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ ((sp' + 208#64) ↦₆₄ ctPtr) ∗ ((sp' + 216#64) ↦₆₄ ctLen) ∗
        ((sp' + 224#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ ((sp' + 232#64) ↦₆₄ pqPtr) ∗ ((sp' + 240#64) ↦₆₄ pqLen) ∗
        ((sp' + 248#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ ((sp' + 256#64) ↦₆₄ adPtr) ∗ ((sp' + 264#64) ↦₆₄ adLen) ∗
        ((sp' + 272#64) ↦₃₂ 0#32) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
        ((sp' + 280#64) ↦₃₂ 0#32) ∗ ((sp' + 284#64) ↦₃₂ pcVal)) ∗
      ((x.ret ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ ((x.ret + 8#64) ↦₆₄ 9223372036854775810#64) ∗
        memRegion (x.ret + 16#64) 104))
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono h112 hmsg


theorem prologue_b8_len9_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State}
    {out : Except SignalProtocolError SignalMessage}
    (hout : out = .error .invalidProtobufEncoding)
    (hst : EpilogueStatePlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x0b8#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState64 9#64 9#64)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      (memRegion (s0.sp - 448#64 + 88#64) 16 ∗
        wireSignalMessageOf A (s0.sp - 448#64 + 176#64) emptyProtoSignalMessage ∗
        memRegion x.ret 120)
      (fun sf Pf =>
        EpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 448#64 + 88#64) 16 ∗
          memRegion (s0.sp - 448#64 + 176#64) 112 ∗
          signalMessageResultAt A [] x.ret out))
      (tryFromQp s0) := by
  set sp' := s0.sp - 448#64
  refine SepWPp.mono_pre
    (sepConj_mono (memRegion16_split8_8' (sp' + 88#64))
      (sepConj_mono_left (wireSignalMessageOf_emptyMsg_cells A sp'))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun pcVal => SepWPp.exists_pre fun cVal =>
    SepWPp.exists_pre fun adLen => SepWPp.exists_pre fun adPtr =>
    SepWPp.exists_pre fun pqLen => SepWPp.exists_pre fun pqPtr =>
    SepWPp.exists_pre fun ctLen => SepWPp.exists_pre fun ctPtr =>
    SepWPp.exists_pre fun rkLen => SepWPp.exists_pre fun rkPtr =>
    SepWPp.exists_pre fun s96 => SepWPp.exists_pre fun s88 => ?_
  set F1 := ((sp' + 192#64) ↦₆₄ rkLen) ∗ ((sp' + 216#64) ↦₆₄ ctLen) ∗
    ((sp' + 240#64) ↦₆₄ pqLen) ∗ ((sp' + 264#64) ↦₆₄ adLen) ∗
    ((sp' + 272#64) ↦₃₂ 0#32) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
    ((sp' + 280#64) ↦₃₂ 0#32) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ∗
    memRegion x.ret 120
  refine SepWPp.mono_pre (P' :=
      (((sp' + 88#64) ↦₆₄ s88) ∗ ((sp' + 96#64) ↦₆₄ s96) ∗
        ((sp' + 176#64) ↦₆₄ noneCap) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗
        ((sp' + 200#64) ↦₆₄ noneCap) ∗ ((sp' + 208#64) ↦₆₄ ctPtr) ∗
        ((sp' + 224#64) ↦₆₄ noneCap) ∗ ((sp' + 232#64) ↦₆₄ pqPtr) ∗
        ((sp' + 248#64) ↦₆₄ noneCap) ∗ ((sp' + 256#64) ↦₆₄ adPtr)) ∗ F1)
    (by dsimp only [F1]; apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_entails
    (prologue_b8_len9_to_460_wp_placed hst hpc hrun hpstate hx19 hx26) ?_
  intro s4 hpc4 hrun4 ⟨hst4, hx1_4, hx19_4, hx22_4, hx25_4, hx26_4, hx27_4⟩
  dsimp only [F1]
  refine SepWPp.mono_pre (P' :=
      (memRegion x.ret 120 ∗
        ((sp' + 176#64) ↦₆₄ noneCap) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗
        ((sp' + 192#64) ↦₆₄ rkLen) ∗
        ((sp' + 200#64) ↦₆₄ noneCap) ∗ ((sp' + 208#64) ↦₆₄ ctPtr) ∗
        ((sp' + 216#64) ↦₆₄ ctLen) ∗
        ((sp' + 224#64) ↦₆₄ noneCap) ∗ ((sp' + 232#64) ↦₆₄ pqPtr) ∗
        ((sp' + 240#64) ↦₆₄ pqLen) ∗
        ((sp' + 248#64) ↦₆₄ noneCap) ∗ ((sp' + 256#64) ↦₆₄ adPtr) ∗
        ((sp' + 264#64) ↦₆₄ adLen) ∗
        ((sp' + 272#64) ↦₃₂ 0#32) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
        ((sp' + 280#64) ↦₃₂ 0#32) ∗ ((sp' + 284#64) ↦₃₂ pcVal)) ∗ memRegion (sp' + 88#64) 16)
    (by dsimp only [sp']; apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.frame_tryFrom
    (prologue_460_len9_to_440_wp_placed (A := A) hout hst4 hpc4 hrun4
      hx1_4 hx19_4 hx22_4 hx25_4 hx26_4 hx27_4)
    fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  dsimp only [sp']
  apply entails_of_eq; ac_rfl


theorem prologue_88_init_wp'_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8}
    (hst : EpilogueStatePlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x088#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx21 : s.readReg64 .x21 = x.bytesA)
    (hx23 : s.readReg64 .x23 = b0.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x0b8#64) s
      (memRegion (s0.sp - 448#64 + 160#64) 16 ∗
        memRegion (s0.sp - 448#64 + 176#64) 112 ∗
        memRegion (s0.sp - 448#64 + 288#64) 8)
      (fun s3 P3 =>
        (EpilogueStatePlaced s0 (s0.sp - 448#64) s3 ∧
        s3.pstate = subsPState64 (BitVec.ofNat 64 x.bytes.length) 9#64 ∧
        s3.readReg64 .x2 = BitVec.ofNat 64 x.bytes.length - 9#64 ∧
        s3.readReg64 .x8 = s0.sp - 448#64 + 160#64 ∧
        s3.readReg64 .x19 = x.ret ∧
        s3.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧
        s3.readReg64 .x21 = x.bytesA ∧
        s3.readReg64 .x23 = b0.zeroExtend 64 ∧
        s3.readReg64 .x26 = 0x8000000000000002#64 ∧
        s3.readReg64 .x29 = s0.sp - 448#64 + 352#64) ∧
        (P3 ⊢ ((s0.sp - 448#64 + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
          ((s0.sp - 448#64 + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64)) ∗
          wireSignalMessageOf A (s0.sp - 448#64 + 176#64) emptyProtoSignalMessage ∗
          ((s0.sp - 448#64 + 288#64) ↦₆₄ (s0.sp - 448#64 + 160#64))))
      (tryFromQp s0) := by
  intro R hm hL
  obtain ⟨sf, hsteps, hex⟩ :=
    prologue_88_init_wp_placed hst hpc hrun hx19 hx20 hx21 hx23 hx26 hx29 R hm hL
  rcases hex with ⟨hpc1, hrun1, Pf, hmf, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hent⟩, hv⟩ | hpan
  · exact ⟨sf, hsteps, Or.inl ⟨hpc1, hrun1, Pf, hmf, ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, hent⟩, hv⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩


theorem prologue_88_len9_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8} {rest : List (BitVec 8)}
    (hbs : x.bytes = b0 :: rest)
    (hlen9 : x.bytes.length = 9)
    (hge3 : ¬ (b0 >>> 4) < 3#8) (hle4 : ¬ 4#8 < (b0 >>> 4))
    (hst : EpilogueStatePlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x088#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx21 : s.readReg64 .x21 = x.bytesA)
    (hx23 : s.readReg64 .x23 = b0.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      (memRegion (s0.sp - 448#64 + 88#64) 16 ∗
        memRegion (s0.sp - 448#64 + 160#64) 16 ∗
        memRegion (s0.sp - 448#64 + 176#64) 112 ∗
        memRegion (s0.sp - 448#64 + 288#64) 8 ∗
        memRegion x.ret 120)
      (fun sf Pf =>
        EpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 448#64 + 88#64) 16 ∗
          memRegion (s0.sp - 448#64 + 160#64) 16 ∗
          memRegion (s0.sp - 448#64 + 176#64) 112 ∗
          memRegion (s0.sp - 448#64 + 288#64) 8 ∗
          signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes)))
      (tryFromQp s0) := by
  set sp' := s0.sp - 448#64
  have hhead : x.bytes.headD 0#8 = b0 := by simp [hbs]
  have hout := tryFrom_eq_len9 hlen9 (hhead ▸ hge3) (hhead ▸ hle4)
  refine SepWPp.mono_pre (P' :=
      (memRegion (sp' + 160#64) 16 ∗ memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 8) ∗
      (memRegion (sp' + 88#64) 16 ∗ memRegion x.ret 120))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_entails
    (prologue_88_init_wp'_placed (A := A) hst hpc hrun hx19 hx20 hx21 hx23 hx26 hx29) ?_
  intro s3 hpc3 hrun3 ⟨hst3, hpstate3, _, _, hx19_3, _, _, _, hx26_3, _⟩
  have hpstate9 : s3.pstate = subsPState64 9#64 9#64 := by
    rw [hpstate3, hlen9]
  have h160 : ((sp' + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
      ((sp' + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64)) ⊢
      memRegion (sp' + 160#64) 16 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      pointsTo64_pair_entails_memRegion16 (sp' + 160#64)
        (x.bytesA + 1#64) (BitVec.ofNat 64 x.bytes.length - 9#64)
  have h288 := pointsTo64_entails_memRegion (sp' + 288#64) (sp' + 160#64)
  refine SepWPp.mono_pre (P' :=
      (memRegion (sp' + 88#64) 16 ∗ wireSignalMessageOf A (sp' + 176#64) emptyProtoSignalMessage ∗
        memRegion x.ret 120) ∗
      (memRegion (sp' + 160#64) 16 ∗ memRegion (sp' + 288#64) 8))
    (by
      refine Entails.trans (Q :=
          (memRegion (sp' + 88#64) 16 ∗ wireSignalMessageOf A (sp' + 176#64) emptyProtoSignalMessage ∗
            memRegion x.ret 120) ∗
          ((((sp' + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
            ((sp' + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64))) ∗
            ((sp' + 288#64) ↦₆₄ (sp' + 160#64))))
        (by dsimp only [sp']; apply entails_of_eq; ac_rfl) ?_
      exact sepConj_mono_right (sepConj_mono h160 h288)) ?_
  refine SepWPp.frame_tryFrom
    (prologue_b8_len9_wp_placed hout hst3 hpc3 hrun3 hpstate9 hx19_3 hx26_3)
    fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  dsimp only [sp']
  apply entails_of_eq; ac_rfl


theorem prologue_88_gt9_loop_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hvarint : DecodeVarintSliceOkWPlaced A H)
    (hint32 : Int32MergeOkWPlaced A H)
    (hskip : SkipFieldOkWPlaced A H)
    (hbytes : BytesMergeOkWPlaced A H)
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8} {rest : List (BitVec 8)}
    (hbs : x.bytes = b0 :: rest)
    (hgt9 : 9 < x.bytes.length) (hlt : x.bytes.length < 2 ^ 63)
    (hst : EpilogueStatePlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x088#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx21 : s.readReg64 .x21 = x.bytesA)
    (hx23 : s.readReg64 .x23 = b0.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (memRegion (s0.sp - 448#64) 176 ∗
        memRegion (s0.sp - 448#64 + 176#64) 112 ∗
        memRegion (s0.sp - 448#64 + 288#64) 64 ∗
        (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) ∗
        A.pool ∗ stackAt (s0.sp - 448#64) (skipFieldStackX 100))
      (fun sf Pf =>
        LoopExitStatePlaced s0 (s0.sp - 448#64) x.ret
          (BitVec.ofNat 64 x.bytes.length) x.bytesA (b0.zeroExtend 64) sf ∧
        (Pf ⊢ loopPostMem A (s0.sp - 448#64) x (sf.readReg64 .x24)))
      (tryFromQp s0) := by
  set sp' := s0.sp - 448#64
  set bs := (x.bytes.take (x.bytes.length - 8)).drop 1
  have hrest_len : rest.length + 1 = x.bytes.length := by
    have := congrArg List.length hbs; simpa using this.symm
  have hrest_gt8 : 8 < rest.length := by omega
  have hbs_eq : bs = rest.take (rest.length - 8) := by
    dsimp only [bs]; rw [hbs]; exact tryFrom_loop_slice_eq hrest_gt8
  have hbs_len : bs.length = x.bytes.length - 9 := by
    rw [hbs_eq, List.length_take, Nat.min_eq_left (by omega)]; omega
  have hbs_pos : 0 < bs.length := by omega
  rcases hcons : bs with _ | ⟨b1, bs1⟩
  · simp [hcons] at hbs_pos
  have hlen_cons : (b1 :: bs1).length = x.bytes.length - 9 := hcons ▸ hbs_len
  have hbv_len : BitVec.ofNat 64 (b1 :: bs1).length = BitVec.ofNat 64 x.bytes.length - 9#64 := by
    rw [hlen_cons]; exact bv_ofNat_sub9 (by omega)
  have h176_split : memRegion sp' 176 = memRegion sp' 160 ∗ memRegion (sp' + 160#64) 16 :=
    memRegion_split' (n := 160) (k := 16) rfl rfl (by decide)
  have h64_split : memRegion (sp' + 288#64) 64 =
      memRegion (sp' + 288#64) 8 ∗ memRegion (sp' + 296#64) 48 ∗ memRegion (sp' + 344#64) 8 := by
    rw [memRegion_split' (n := 8) (k := 56) rfl rfl (by decide),
      memRegion_split' (b := sp' + 288#64 + 8#64) (n := 48) (k := 8) rfl rfl (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [h176_split, h64_split]
  set F1 := memRegion sp' 160 ∗ memRegion (sp' + 296#64) 48 ∗ memRegion (sp' + 344#64) 8 ∗
    (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) ∗
    A.pool ∗ stackAt sp' (skipFieldStackX 100)
  refine SepWPp.mono_pre (P' :=
      (memRegion (sp' + 160#64) 16 ∗ memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 8) ∗ F1)
    (by dsimp only [F1, sp']; apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_entails
    (prologue_88_init_wp'_placed (A := A) hst hpc hrun hx19 hx20 hx21 hx23 hx26 hx29) ?_
  intro s3 hpc3 hrun3 ⟨hst3, hpstate3, hx2_3, hx8_3, hx19_3, hx20_3, hx21_3, hx23_3, hx26_3, hx29_3⟩
  set P3 := ((sp' + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
    ((sp' + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64)) ∗
    wireSignalMessageOf A (sp' + 176#64) emptyProtoSignalMessage ∗
    ((sp' + 288#64) ↦₆₄ (sp' + 160#64))
  refine SepWPp.mono_pre (P' := emp ∗ (P3 ∗ F1))
    (by rw [emp_sepConj]; exact Entails.refl _) ?_
  refine SepWPp.bind_frame_entails
    (prologue_b8_gt9_to_f0_wp_placed hgt9 hlt hst3 hpc3 hrun3
      hpstate3 hx2_3 hx8_3 hx19_3 hx20_3 hx21_3 hx23_3 hx26_3 hx29_3) ?_
  intro s4 hpc4 hrun4 ⟨hregs4, ⟨_, hsp4, hcl4, htr4⟩, hx28_4, hx27_4, hx2_4⟩
  rw [emp_sepConj]
  dsimp only [P3, F1]
  have hrest_split : ((x.bytesA + 1#64) ↦ₛ rest) =
      ((x.bytesA + 1#64) ↦ₛ (b1 :: bs1)) ∗
        ((x.bytesA + 1#64 + BitVec.ofNat 64 (rest.length - 8)) ↦ₛ rest.drop (rest.length - 8)) := by
    have hs := (pointsToBytes_take_drop (x.bytesA + 1#64) rest (rest.length - 8) (by omega)).symm
    rw [← hbs_eq, hcons] at hs
    exact hs
  have hcursor : sliceCursorAt (sp' + 160#64) (x.bytesA + 1#64) (b1 :: bs1) =
      ((sp' + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
        ((sp' + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64)) ∗
        ((x.bytesA + 1#64) ↦ₛ (b1 :: bs1)) := by
    unfold sliceCursorAt
    rw [hbv_len]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  set F2 := memRegion sp' 160 ∗ memRegion (sp' + 344#64) 8 ∗
    (x.bytesA ↦₈ b0) ∗
    ((x.bytesA + 1#64 + BitVec.ofNat 64 (rest.length - 8)) ↦ₛ rest.drop (rest.length - 8))
  refine SepWPp.mono_pre (P' :=
      (sliceCursorAt (sp' + 160#64) (x.bytesA + 1#64) (b1 :: bs1) ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageOf A (sp' + 176#64) emptyProtoSignalMessage) ∗ F2)
    (by
      rw [hrest_split, hcursor]
      dsimp only [F2]
      apply entails_of_eq; ac_rfl) ?_
  have hx2_4' : s4.readReg64 .x2 = BitVec.ofNat 64 (b1 :: bs1).length := by
    rw [hx2_4, hbv_len]
  have hloop := decodeLoop_f0_wp_placed hS hvarint hint32 hskip hbytes (fuel := bs1.length)
    (m := emptyProtoSignalMessage) (ptr := x.bytesA + 1#64)
    hpc4 hrun4 hregs4 hx28_4 hx27_4 hx2_4' hsp4 hcl4 htr4
    (Nat.le_refl _) (by omega)
  refine SepWPp.frame_tryFrom hloop fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  have hdec : decodeLoop (bs1.length + 1) emptyProtoSignalMessage (b1 :: bs1) = decode bs := by
    rw [hcons]; rfl
  rw [hdec]
  dsimp only [loopExitMem, loopPostMem, bs, F2]
  have hbytes_eq : (x.bytesA ↦ₛ x.bytes) =
      (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ (b1 :: bs1)) ∗
        ((x.bytesA + 1#64 + BitVec.ofNat 64 (rest.length - 8)) ↦ₛ rest.drop (rest.length - 8)) := by
    rw [hbs, pointsToBytes_cons, hrest_split]
  rw [h176_split, h64_split, hbytes_eq]
  have h288 := pointsTo64_entails_memRegion (sp' + 288#64) (sp' + 160#64)
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left h288)))
  dsimp only [sp']
  apply entails_of_eq; ac_rfl


def TryFromPostOk_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  ∀ {x : TryFromGhost} {s0 s : State},
    9 < x.bytes.length →
    x.bytes.length < 2 ^ 32 →
    ¬ ((x.bytes.headD 0#8) >>> 4) < 3#8 →
    ¬ 4#8 < ((x.bytes.headD 0#8) >>> 4) →
    s.pc = (blkPl_85).base + 0x3b0#64 →
    s.status = .Running →
    LoopExitStatePlaced s0 (s0.sp - 448#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.bytesA ((x.bytes.headD 0#8).zeroExtend 64) s →
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      (loopPostMem A (s0.sp - 448#64) x (s.readReg64 .x24) ∗ memRegion x.ret 120 ∗ logOff tryFromPlacedImg)
      (fun sf Pf =>
        EpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 448#64) 352 ∗
          signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗ A.pool ∗
          stackAt (s0.sp - 448#64) (skipFieldStackX 100)))
      (tryFromQp s0)


theorem prologue_88_to_440_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hvarint : DecodeVarintSliceOkWPlaced A H)
    (hint32 : Int32MergeOkWPlaced A H)
    (hskip : SkipFieldOkWPlaced A H)
    (hbytes : BytesMergeOkWPlaced A H)
    (hpost : TryFromPostOk_placed A H)
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8} {rest : List (BitVec 8)}
    (hbs : x.bytes = b0 :: rest)
    (hge9 : 9 ≤ x.bytes.length) (hlt : x.bytes.length < 2 ^ 32)
    (hge3 : ¬ (b0 >>> 4) < 3#8) (hle4 : ¬ 4#8 < (b0 >>> 4))
    (hst : EpilogueStatePlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x088#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx21 : s.readReg64 .x21 = x.bytesA)
    (hx23 : s.readReg64 .x23 = b0.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      (memRegion (s0.sp - 448#64) 352 ∗
        memRegion x.ret 120 ∗
        (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) ∗
        logOff tryFromPlacedImg ∗ A.pool ∗ stackAt (s0.sp - 448#64) (skipFieldStackX 100))
      (fun sf Pf =>
        EpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 448#64) 352 ∗
          signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗
          A.pool ∗ stackAt (s0.sp - 448#64) (skipFieldStackX 100)))
      (tryFromQp s0) := by
  set sp' := s0.sp - 448#64
  by_cases hlen9 : x.bytes.length = 9
  · have hbytes_eq : (x.bytesA ↦ₛ x.bytes) = (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) := by
      rw [hbs, pointsToBytes_cons]
    set F9 := memRegion sp' 88 ∗ memRegion (sp' + 104#64) 56 ∗ memRegion (sp' + 296#64) 56 ∗
      (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)
    refine SepWPp.mono_pre (P' :=
        (memRegion (sp' + 88#64) 16 ∗
          memRegion (sp' + 160#64) 16 ∗
          memRegion (sp' + 176#64) 112 ∗
          memRegion (sp' + 288#64) 8 ∗
          memRegion x.ret 120) ∗ F9)
      (by
        dsimp only [F9, sp']
        rw [memRegion352_split_len9, hbytes_eq]
        apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (prologue_88_len9_wp_placed (A := A) hbs hlen9 hge3 hle4 hst hpc hrun
        hx19 hx20 hx21 hx23 hx26 hx29)
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    rw [memRegion352_split_len9 sp']
    dsimp only [F9, sp']
    apply entails_of_eq; ac_rfl
  · have hgt9 : 9 < x.bytes.length := by omega
    have hhead : x.bytes.headD 0#8 = b0 := by simp [hbs]
    refine SepWPp.mono_pre (P' :=
        (memRegion sp' 176 ∗
          memRegion (sp' + 176#64) 112 ∗
          memRegion (sp' + 288#64) 64 ∗
          (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗
        (memRegion x.ret 120 ∗ logOff tryFromPlacedImg))
      (by
        rw [memRegion352_split_loop sp']
        dsimp only [sp']
        apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.bind_frame_entails
      (prologue_88_gt9_loop_wp_placed hS hvarint hint32 hskip hbytes
        hbs hgt9 (by omega) hst hpc hrun hx19 hx20 hx21 hx23 hx26 hx29) ?_
    intro s5 hpc5 hrun5 hst5
    have hst5' : LoopExitStatePlaced s0 (s0.sp - 448#64) x.ret
        (BitVec.ofNat 64 x.bytes.length) x.bytesA ((x.bytes.headD 0#8).zeroExtend 64) s5 :=
      hhead.symm ▸ hst5
    exact hpost hgt9 hlt (hhead ▸ hge3) (hhead ▸ hle4) hpc5 hrun5 hst5'


theorem prologue_44_to_440_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hvarint : DecodeVarintSliceOkWPlaced A H)
    (hint32 : Int32MergeOkWPlaced A H)
    (hskip : SkipFieldOkWPlaced A H)
    (hbytes : BytesMergeOkWPlaced A H)
    (hpost : TryFromPostOk_placed A H)
    {x : TryFromGhost} {s0 s : State}
    (hge9 : 9 ≤ x.bytes.length) (hlt : x.bytes.length < 2 ^ 32)
    (hst : EpilogueStatePlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x044#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = x.bytesA)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      (memRegion (s0.sp - 448#64) 352 ∗
        memRegion x.ret 120 ∗
        (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗
        A.pool ∗ stackAt (s0.sp - 448#64) (skipFieldStackX 100))
      (fun sf Pf =>
        EpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 448#64) 352 ∗
          signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗
          A.pool ∗ stackAt (s0.sp - 448#64) (skipFieldStackX 100)))
      (tryFromQp s0) := by
  set sp' := s0.sp - 448#64
  rcases hbs : x.bytes with _ | ⟨b0, rest⟩
  · simp [hbs] at hge9
  have hge9' : 9 ≤ x.bytes.length := hge9
  rw [ ← hbs ]
  by_cases hlt3 : (b0 >>> 4) < 3#8
  · set Fv := memRegion sp' 352 ∗ logOff tryFromPlacedImg ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)
    refine SepWPp.mono_pre (P' := ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120) ∗ Fv)
      (by dsimp only [Fv, sp']; apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (prologue_44_legacyVer_wp_placed (A := A) hbs hge9' hlt3 hst hpc hrun hx0 hx19)
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    dsimp only [Fv, sp']
    apply entails_of_eq; ac_rfl
  · by_cases hgt4 : 4#8 < (b0 >>> 4)
    · set Fv := memRegion sp' 352 ∗ logOff tryFromPlacedImg ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)
      refine SepWPp.mono_pre (P' := ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120) ∗ Fv)
        (by dsimp only [Fv, sp']; apply entails_of_eq; ac_rfl) ?_
      refine SepWPp.frame_tryFrom
        (prologue_44_unrecognizedVer_wp_placed (A := A) hbs hge9' hlt3 hgt4 hst hpc hrun hx0 hx19)
        fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
      refine Entails.trans (sepConj_mono_left hentf) ?_
      dsimp only [Fv, sp']
      apply entails_of_eq; ac_rfl
    · have hbytes_eq : (x.bytesA ↦ₛ x.bytes) = (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) := by
        rw [hbs, pointsToBytes_cons]
      have hvalid : SepWPp (tryFromPlacedProg H)
          ((blkPl_85).base + 0x088#64) s
          (x.bytesA ↦₈ b0)
          (fun s2 P2 =>
            (EpilogueStatePlaced s0 sp' s2 ∧
            s2.readReg64 .x19 = x.ret ∧
            s2.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧
            s2.readReg64 .x21 = x.bytesA ∧
            s2.readReg64 .x23 = b0.zeroExtend 64 ∧
            s2.readReg64 .x26 = 0x8000000000000002#64 ∧
            s2.readReg64 .x29 = sp' + 352#64) ∧
            (P2 ⊢ (x.bytesA ↦₈ b0)))
          (tryFromQp s0) := by
        intro R hm hL
        obtain ⟨sf, hsteps, hex⟩ :=
          prologue_44_validVer_wp_placed hlt3 hgt4 hst hpc hrun hx0 hx19 hx20 hx29 R hm hL
        rcases hex with ⟨hpc1, hrun1, Pf, hmf, ⟨h1, h2, h3, h4, h5, h6, h7, hent⟩, hv⟩ | hpan
        · exact ⟨sf, hsteps, Or.inl ⟨hpc1, hrun1, Pf, hmf, ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hent⟩, hv⟩⟩
        · exact ⟨sf, hsteps, Or.inr hpan⟩
      set Fv := memRegion sp' 352 ∗ memRegion x.ret 120 ∗ ((x.bytesA + 1#64) ↦ₛ rest) ∗
        logOff tryFromPlacedImg ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)
      refine SepWPp.mono_pre (P' := (x.bytesA ↦₈ b0) ∗ Fv)
        (by dsimp only [Fv, sp']; rw [hbytes_eq]; apply entails_of_eq; ac_rfl) ?_
      refine SepWPp.bind_frame_entails hvalid ?_
      intro s2 hpc2 hrun2 ⟨hst2, hx19_2, hx20_2, hx21_2, hx23_2, hx26_2, hx29_2⟩
      refine SepWPp.mono_pre (P' :=
          memRegion sp' 352 ∗ memRegion x.ret 120 ∗
          (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) ∗
          logOff tryFromPlacedImg ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
        (by dsimp only [Fv, sp']; apply entails_of_eq; ac_rfl) ?_
      exact prologue_88_to_440_wp_placed hS hvarint hint32 hskip hbytes hpost
        hbs hge9' hlt hlt3 hgt4 hst2 hpc2 hrun2 hx19_2 hx20_2 hx21_2 hx23_2 hx26_2 hx29_2


theorem tryFrom_entry_to_440_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hvarint : DecodeVarintSliceOkWPlaced A H)
    (hint32 : Int32MergeOkWPlaced A H)
    (hskip : SkipFieldOkWPlaced A H)
    (hbytes : BytesMergeOkWPlaced A H)
    (hpost : TryFromPostOk_placed A H)
    {x : TryFromGhost} {s0 : State}
    (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (blkPl_85).base)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.bytesA)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ logOff tryFromPlacedImg ∗
        stackAt s0.sp smallRootStack ∗ A.pool)
      (fun sf Pf => EpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ stackAt (s0.sp - 448#64) tryFromSubStack ∗
          memRegion (s0.sp - 448#64) 352 ∗
          calleeSavedAt (s0.sp - 448#64) s0 ∗
          signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗ A.pool))
      (tryFromQp s0) := by
  by_cases hlt9 : x.bytes.length < 9
  · exact prologue_tooShort_wp_placed hlt9 hpc hrun hsp hcl hx0 hx1 hx8
  · have hge9 : 9 ≤ x.bytes.length := by omega
    set sp' := s0.sp - 448#64
    have hstk1 := stackAt_smallRoot_split s0.sp
    have hstk2 := stackAt_sub_split sp' (skipFieldStackX 100) tryFromSubStack
    have hentry : SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x044#64) s0
        (memRegion (sp' + 352#64) 96)
        (fun s1 P1 =>
          (EpilogueStatePlaced s0 sp' s1 ∧
          s1.readReg64 .x0 = x.bytesA ∧
          s1.readReg64 .x19 = x.ret ∧
          s1.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧
          s1.readReg64 .x29 = sp' + 352#64) ∧
          (P1 ⊢ calleeSavedAt sp' s0))
        (tryFromQp s0) := by
      intro R hm hL
      obtain ⟨sf, hsteps, hex⟩ :=
        prologue_entry_ge9_wp_placed hge9 (by omega) hpc hrun hsp hcl hx0 hx1 hx8 R hm hL
      rcases hex with ⟨hpc1, hrun1, Pf, hmf, ⟨h1, h2, h3, h4, h5, hent⟩, hv⟩ | hpan
      · exact ⟨sf, hsteps, Or.inl ⟨hpc1, hrun1, Pf, hmf, ⟨⟨h1, h2, h3, h4, h5⟩, hent⟩, hv⟩⟩
      · exact ⟨sf, hsteps, Or.inr hpan⟩
    set Fe := (memRegion sp' 352 ∗ memRegion x.ret 120 ∗ (x.bytesA ↦ₛ x.bytes) ∗
      logOff tryFromPlacedImg ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗
      memRegion (sp' - BitVec.ofNat 64 tryFromSubStack) (tryFromSubStack - skipFieldStackX 100)
    refine SepWPp.mono_pre (P' := memRegion (sp' + 352#64) 96 ∗ Fe)
      (by
        rw [hstk1, hstk2]
        dsimp only [Fe, sp']
        apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.bind_frame_entails hentry ?_
    intro s1 hpc1 hrun1 ⟨hst1, hx0_1, hx19_1, hx20_1, hx29_1⟩
    dsimp only [Fe]
    refine SepWPp.mono_pre (P' :=
        (memRegion sp' 352 ∗ memRegion x.ret 120 ∗ (x.bytesA ↦ₛ x.bytes) ∗
          logOff tryFromPlacedImg ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗
        (calleeSavedAt sp' s0 ∗
          memRegion (sp' - BitVec.ofNat 64 tryFromSubStack) (tryFromSubStack - skipFieldStackX 100)))
      (by apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (prologue_44_to_440_wp_placed hS hvarint hint32 hskip hbytes hpost
        hge9 hlt hst1 hpc1 hrun1 hx0_1 hx19_1 hx20_1 hx29_1)
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    rw [hstk2]
    dsimp only [sp']
    apply entails_of_eq; ac_rfl


theorem tryFrom_subroutine_ok_of_post_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hvarint : DecodeVarintSliceOkWPlaced A H)
    (hint32 : Int32MergeOkWPlaced A H)
    (hskip : SkipFieldOkWPlaced A H)
    (hbytes : BytesMergeOkWPlaced A H)
    (hpost : TryFromPostOk_placed A H) :
    subroutine_ok (tryFromPlacedProg H)
      ((blkPl_85).base)
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A)) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hL
  dsimp only [withLsCodeRoLoaded] at hpre
  rw [sepConj_comm ((tryFromPlacedSpec A).pre x s0), sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  dsimp only [tryFromPlacedSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1_nat, hlt, hx8⟩, hmem⟩
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hmem' : s0.mem ⊨
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ logOff tryFromPlacedImg ∗
        stackAt s0.sp smallRootStack ∗ A.pool) ∗ R := by
    ac_nf at hmem ⊢
  have h1 : SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ logOff tryFromPlacedImg ∗
        stackAt s0.sp smallRootStack ∗ A.pool)
      (fun sm Pm =>
        EpilogueStatePlaced s0 (s0.sp - 448#64) sm ∧
        (Pm ⊢ stackAt (s0.sp - 448#64) tryFromSubStack ∗
          memRegion (s0.sp - 448#64) 352 ∗
          calleeSavedAt (s0.sp - 448#64) s0 ∗
          signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗ A.pool))
      (tryFromQp s0) :=
    tryFrom_entry_to_440_wp_placed hS hvarint hint32 hskip hbytes hpost
      hlt hpc hrun hsp hcl hx0 hx1 hx8
  have hfull : SepWPp (tryFromPlacedProg H)
      (s0.readReg64 .x30) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ logOff tryFromPlacedImg ∗
        stackAt s0.sp smallRootStack ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (tryFromPlacedSpec A).post x s0 sf))
      (tryFromQp s0) := by
    refine SepWPp.bind h1 ?_
    intro sm Pm hpcm hrunm ⟨hstm, hentm⟩
    exact SepWPp.mono_pre hentm
      (epilogue_440_wp_placed (A := A) (x := x) hstm hpcm hrunm)
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ | ⟨hpan, Pf, hmf, htr_f⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩,
      Satisfies.mono (sepConj_mono_left hent_f) hmf⟩
  · exact Or.inr (Or.inl ⟨hpan, htr_f R hmf⟩)
  · exact (allowPanic_not_exited hoom).elim


end CryptoVerification.LibsignalTripleRatchet.Wire
