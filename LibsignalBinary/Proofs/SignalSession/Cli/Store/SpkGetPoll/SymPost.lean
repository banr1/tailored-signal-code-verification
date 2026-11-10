/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.Callees
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.Fetches
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Postcondition Packaging, Cut Combinators, and Epilogue for `get_signed_pre_key::{closure#0}`

48-cell stack-frame decomposition, cell-level sret pack bridges, shared post/panic predicates,
framed cut combinators, and shared return epilogue.
-/

/-!
# Postcondition Packaging, Cut Combinators, and Epilogue for `get_signed_pre_key::{closure#0}`

48-cell stack-frame decomposition, cell-level sret pack bridges, shared post/panic predicates,
framed cut combinators, and shared return epilogue.
-/

/-!
# Postcondition Packaging, Cut Combinators, and Epilogue for `get_signed_pre_key::{closure#0}`

48-cell stack-frame decomposition, cell-level sret pack bridges, shared post/panic predicates,
framed cut combinators, and shared return epilogue.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

namespace CliSpkPollNorm

@[arm64_norm ↓, wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[arm64_norm ↓, wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setPC_pre (s : State) (pc : BitVec 64) (idx : BitVec 5) :
    (s.setPC pc).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (idx : BitVec 5) :
    ((s.setPC pc).setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setMem_pre (s : State) (m : Memory) (idx : BitVec 5) :
    (s.setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setPState_pre (s : State) (ps : PState) (idx : BitVec 5) :
    (s.setPState ps).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) (idx : BitVec 5) :
    (s.writeReg64 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_append_lo (hi lo : BitVec 64) :
    BitVec.extractLsb' 0 64 (hi ++ lo) = lo := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_append_hi (hi lo : BitVec 64) :
    BitVec.extractLsb' 64 64 (hi ++ lo) = hi := by
  bv_bits

@[arm64_norm, wp_norm]
theorem bv_sub_sub_lit (x : BitVec 64) (a b : Nat) (_hab : a + b < 2 ^ 64 := by decide) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  bv_omega

end CliSpkPollNorm

open CliSpkPollNorm

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm] words6At words11At

/-! ## 1. Panic, branch-condition, and postcondition packaging helpers -/

theorem csp_regs {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    s2.readReg64 .x19 = s1.readReg64 .x19 ∧
    s2.readReg64 .x20 = s1.readReg64 .x20 ∧
    s2.readReg64 .x21 = s1.readReg64 .x21 ∧
    s2.readReg64 .x22 = s1.readReg64 .x22 ∧
    s2.readReg64 .x23 = s1.readReg64 .x23 ∧
    s2.readReg64 .x24 = s1.readReg64 .x24 ∧
    s2.readReg64 .x25 = s1.readReg64 .x25 ∧
    s2.readReg64 .x26 = s1.readReg64 .x26 ∧
    s2.readReg64 .x27 = s1.readReg64 .x27 ∧
    s2.readReg64 .x28 = s1.readReg64 .x28 ∧
    s2.readReg64 .x29 = s1.readReg64 .x29 ∧
    calleeSavedVRegs s2 = calleeSavedVRegs s1 := by
  rw [CalleeSavedPreserved.iff_regs] at h
  exact h

theorem close_panic_subgoal {s0 s_call sf : State} {F R : SepProp}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  refine allowPanic_frame (F := F) (fun h => ?_) (by simpa only [sepConj_assoc] using hm)
  rcases h with ⟨hfail, hpref⟩
  unfold allocFailedIn at hfail ⊢
  rw [htr] at hfail hpref
  exact ⟨hfail, hpref⟩

theorem oom_readErr_of_trace_eq {s0 sm sf : State}
    (h : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace)
    (htr : sf.trace = sm.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  rcases h with ⟨hfail, hpref⟩
  unfold allocFailedIn at hfail ⊢
  rw [htr]
  exact ⟨hfail, hpref⟩

theorem cmn1_beq_zero {w0 : BitVec 64} (hw0 : w0 ≠ 0xFFFFFFFFFFFFFFFF#64) :
    ((w0 + 1#64) == 0#64) = false := by
  apply beq_eq_false_iff_ne.mpr
  bv_omega

theorem cmn1_add_zero {w0 : BitVec 64} (hw0 : w0 ≠ 0xFFFFFFFFFFFFFFFF#64) :
    ((w0 + 1#64 + 0#64) == 0#64) = false := by
  apply beq_eq_false_iff_ne.mpr
  bv_omega

theorem len_bv_ne_zero {b : BitVec 8} {bs : List (BitVec 8)}
    (hlt : (b :: bs).length < 2 ^ 32) :
    BitVec.ofNat 64 (b :: bs).length ≠ 0#64 := by
  have hpos : 0 < (b :: bs).length := by simp
  intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at hnat
  have hmod : (b :: bs).length % 2 ^ 64 = (b :: bs).length := Nat.mod_eq_of_lt (by omega)
  omega

/-! ## 2. Stack frame decomposition (`48 = 5 + 43` cells) -/

def spkPollSlack (sp : BitVec 64) : SepProp :=
  cells (sp - 384#64) 1 ∗ cells (sp - 256#64) 1 ∗
    cells (sp - 208#64) 1 ∗ cells (sp - 112#64) 2

def spkScratch15 (sp : BitVec 64) : SepProp :=
  cells (sp - 376#64) 5 ∗ cells (sp - 336#64) 5 ∗ cells (sp - 296#64) 5

def spkSavedAt (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem cells_48_split (sp : BitVec 64) :
    cells (sp - 384#64) 48 =
      spkPollSlack sp ∗
        spkScratch15 sp ∗
        cells (sp - 248#64) 5 ∗
        cells (sp - 200#64) 6 ∗ cells (sp - 152#64) 5 ∗
        cells (sp - 96#64) 6 ∗ cells (sp - 48#64) 6 := by
  have s1 : cells (sp - 384#64) 48 = _ := cells_split_sub sp 384 376 1 47
  have s2 : cells (sp - 376#64) 47 = _ := cells_split_sub sp 376 336 5 42
  have s3 : cells (sp - 336#64) 42 = _ := cells_split_sub sp 336 296 5 37
  have s4 : cells (sp - 296#64) 37 = _ := cells_split_sub sp 296 256 5 32
  have s5 : cells (sp - 256#64) 32 = _ := cells_split_sub sp 256 248 1 31
  have s6 : cells (sp - 248#64) 31 = _ := cells_split_sub sp 248 208 5 26
  have s7 : cells (sp - 208#64) 26 = _ := cells_split_sub sp 208 200 1 25
  have s8 : cells (sp - 200#64) 25 = _ := cells_split_sub sp 200 152 6 19
  have s9 : cells (sp - 152#64) 19 = _ := cells_split_sub sp 152 112 5 14
  have s10 : cells (sp - 112#64) 14 = _ := cells_split_sub sp 112 96 2 12
  have s11 : cells (sp - 96#64) 12 = _ := cells_split_sub sp 96 48 6 6
  rw [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  dsimp only [spkPollSlack, spkScratch15]
  ac_rfl

theorem cells_sub_5_376_eq (sp : BitVec 64) :
    cells (sp - 376#64) 5 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64,
        ((sp - 376#64) ↦₆₄ v0) ∗ ((sp - 368#64) ↦₆₄ v1) ∗ ((sp - 360#64) ↦₆₄ v2) ∗
        ((sp - 352#64) ↦₆₄ v3) ∗ ((sp - 344#64) ↦₆₄ v4) := by
  cells_unfold

theorem cells_sub_5_336_eq (sp : BitVec 64) :
    cells (sp - 336#64) 5 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64,
        ((sp - 336#64) ↦₆₄ v0) ∗ ((sp - 328#64) ↦₆₄ v1) ∗ ((sp - 320#64) ↦₆₄ v2) ∗
        ((sp - 312#64) ↦₆₄ v3) ∗ ((sp - 304#64) ↦₆₄ v4) := by
  cells_unfold

theorem cells_sub_5_296_eq (sp : BitVec 64) :
    cells (sp - 296#64) 5 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64,
        ((sp - 296#64) ↦₆₄ v0) ∗ ((sp - 288#64) ↦₆₄ v1) ∗ ((sp - 280#64) ↦₆₄ v2) ∗
        ((sp - 272#64) ↦₆₄ v3) ∗ ((sp - 264#64) ↦₆₄ v4) := by
  cells_unfold

theorem cells_sub_5_248_eq (sp : BitVec 64) :
    cells (sp - 248#64) 5 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64,
        ((sp - 248#64) ↦₆₄ v0) ∗ ((sp - 240#64) ↦₆₄ v1) ∗ ((sp - 232#64) ↦₆₄ v2) ∗
        ((sp - 224#64) ↦₆₄ v3) ∗ ((sp - 216#64) ↦₆₄ v4) := by
  cells_unfold

theorem cells_sub_6_200_eq (sp : BitVec 64) :
    cells (sp - 200#64) 6 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 200#64) ↦₆₄ v0) ∗ ((sp - 192#64) ↦₆₄ v1) ∗ ((sp - 184#64) ↦₆₄ v2) ∗
        ((sp - 176#64) ↦₆₄ v3) ∗ ((sp - 168#64) ↦₆₄ v4) ∗ ((sp - 160#64) ↦₆₄ v5) := by
  cells_unfold

theorem cells_sub_5_152_eq (sp : BitVec 64) :
    cells (sp - 152#64) 5 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64,
        ((sp - 152#64) ↦₆₄ v0) ∗ ((sp - 144#64) ↦₆₄ v1) ∗ ((sp - 136#64) ↦₆₄ v2) ∗
        ((sp - 128#64) ↦₆₄ v3) ∗ ((sp - 120#64) ↦₆₄ v4) := by
  cells_unfold

theorem cells_sub_6_96_eq (sp : BitVec 64) :
    cells (sp - 96#64) 6 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
        ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) := by
  cells_unfold

theorem cells_sub_6_48_eq (sp : BitVec 64) :
    cells (sp - 48#64) 6 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
        ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5) := by
  cells_unfold

private theorem cells_pack_5_376 (sp a0 a1 a2 a3 a4 : BitVec 64) :
    ((sp - 376#64) ↦₆₄ a0) ∗ ((sp - 368#64) ↦₆₄ a1) ∗ ((sp - 360#64) ↦₆₄ a2) ∗
      ((sp - 352#64) ↦₆₄ a3) ∗ ((sp - 344#64) ↦₆₄ a4) ⊢ cells (sp - 376#64) 5 := by
  rw [cells_sub_5_376_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4 (Entails.refl _)))))

private theorem cells_pack_5_336 (sp a0 a1 a2 a3 a4 : BitVec 64) :
    ((sp - 336#64) ↦₆₄ a0) ∗ ((sp - 328#64) ↦₆₄ a1) ∗ ((sp - 320#64) ↦₆₄ a2) ∗
      ((sp - 312#64) ↦₆₄ a3) ∗ ((sp - 304#64) ↦₆₄ a4) ⊢ cells (sp - 336#64) 5 := by
  rw [cells_sub_5_336_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4 (Entails.refl _)))))

private theorem cells_pack_5_296 (sp a0 a1 a2 a3 a4 : BitVec 64) :
    ((sp - 296#64) ↦₆₄ a0) ∗ ((sp - 288#64) ↦₆₄ a1) ∗ ((sp - 280#64) ↦₆₄ a2) ∗
      ((sp - 272#64) ↦₆₄ a3) ∗ ((sp - 264#64) ↦₆₄ a4) ⊢ cells (sp - 296#64) 5 := by
  rw [cells_sub_5_296_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4 (Entails.refl _)))))

private theorem cells_pack_5_248 (sp a0 a1 a2 a3 a4 : BitVec 64) :
    ((sp - 248#64) ↦₆₄ a0) ∗ ((sp - 240#64) ↦₆₄ a1) ∗ ((sp - 232#64) ↦₆₄ a2) ∗
      ((sp - 224#64) ↦₆₄ a3) ∗ ((sp - 216#64) ↦₆₄ a4) ⊢ cells (sp - 248#64) 5 := by
  rw [cells_sub_5_248_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4 (Entails.refl _)))))

private theorem cells_pack_6_200 (sp a0 a1 a2 a3 a4 a5 : BitVec 64) :
    ((sp - 200#64) ↦₆₄ a0) ∗ ((sp - 192#64) ↦₆₄ a1) ∗ ((sp - 184#64) ↦₆₄ a2) ∗
      ((sp - 176#64) ↦₆₄ a3) ∗ ((sp - 168#64) ↦₆₄ a4) ∗ ((sp - 160#64) ↦₆₄ a5) ⊢
      cells (sp - 200#64) 6 := by
  rw [cells_sub_6_200_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4
      (Entails.sepExists_right a5 (Entails.refl _))))))

private theorem cells_pack_5_152 (sp a0 a1 a2 a3 a4 : BitVec 64) :
    ((sp - 152#64) ↦₆₄ a0) ∗ ((sp - 144#64) ↦₆₄ a1) ∗ ((sp - 136#64) ↦₆₄ a2) ∗
      ((sp - 128#64) ↦₆₄ a3) ∗ ((sp - 120#64) ↦₆₄ a4) ⊢ cells (sp - 152#64) 5 := by
  rw [cells_sub_5_152_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4 (Entails.refl _)))))

private theorem cells_pack_6_96 (sp a0 a1 a2 a3 a4 a5 : BitVec 64) :
    ((sp - 96#64) ↦₆₄ a0) ∗ ((sp - 88#64) ↦₆₄ a1) ∗ ((sp - 80#64) ↦₆₄ a2) ∗
      ((sp - 72#64) ↦₆₄ a3) ∗ ((sp - 64#64) ↦₆₄ a4) ∗ ((sp - 56#64) ↦₆₄ a5) ⊢
      cells (sp - 96#64) 6 := by
  rw [cells_sub_6_96_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4
      (Entails.sepExists_right a5 (Entails.refl _))))))

private theorem cells_pack_6_48 (sp a0 a1 a2 a3 a4 a5 : BitVec 64) :
    ((sp - 48#64) ↦₆₄ a0) ∗ ((sp - 40#64) ↦₆₄ a1) ∗ ((sp - 32#64) ↦₆₄ a2) ∗
      ((sp - 24#64) ↦₆₄ a3) ∗ ((sp - 16#64) ↦₆₄ a4) ∗ ((sp - 8#64) ↦₆₄ a5) ⊢
      cells (sp - 48#64) 6 := by
  rw [cells_sub_6_48_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4
      (Entails.sepExists_right a5 (Entails.refl _))))))

private theorem frame48_pack_groups (sp : BitVec 64) :
    spkPollSlack sp ∗
      (cells (sp - 376#64) 5 ∗ cells (sp - 336#64) 5 ∗ cells (sp - 296#64) 5) ∗
      cells (sp - 248#64) 5 ∗
      cells (sp - 200#64) 6 ∗ cells (sp - 152#64) 5 ∗
      cells (sp - 96#64) 6 ∗ cells (sp - 48#64) 6 ⊢
      cells (sp - 384#64) 48 := by
  rw [cells_48_split sp]
  dsimp only [spkScratch15]
  exact Entails.of_eq (by ac_rfl)

/-! ## 3. Cell-level sret pack bridges -/

theorem spkAns_intro (rd : ReadRule) (A : RustAlloc) (x : PkPollGhost) (s0 sf : State)
    (ans : PkAns SignedPreKeyRecord)
    (h : ans = pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          sf.trace = s0.trace) :
    spkAnsAt A x.out ans ⊢
      ∃∗ a : PkAns SignedPreKeyRecord,
        ⌜a = pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
            sf.trace = s0.trace⌝ ∗
        spkAnsAt A x.out a :=
  Entails.sepExists_right ans (Entails.pure_right h (Entails.refl _))

theorem readErr88_pack_cells (A : RustAlloc) (out : BitVec 64)
    (u0 u1 u2 u3 u4 u5 w7 w8 w9 w10 : BitVec 64) :
    ((out ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((out + 8#64) ↦₆₄ u0) ∗ ((out + 16#64) ↦₆₄ u1) ∗
      ((out + 24#64) ↦₆₄ u2) ∗ ((out + 32#64) ↦₆₄ u3) ∗ ((out + 40#64) ↦₆₄ u4) ∗
      ((out + 48#64) ↦₆₄ u5) ∗ ((out + 56#64) ↦₆₄ w7) ∗ ((out + 64#64) ↦₆₄ w8) ∗
      ((out + 72#64) ↦₆₄ w9) ∗ ((out + 80#64) ↦₆₄ w10)) ∗
      speDetached A (utf8 "read") u0 u1 u2 u3 u4 u5 .invalidState ⊢
      spkAnsAt A out .readErr :=
  errResult88_pack A (utf8 "read") out u0 u1 u2 u3 u4 u5 w7 w8 w9 w10 .invalidState

theorem missing88_pack_cells (A : RustAlloc) (out : BitVec 64)
    (w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) :
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((out + 8#64) ↦₆₄ speWord 14) ∗
      ((out + 16#64) ↦₆₄ w2) ∗ ((out + 24#64) ↦₆₄ w3) ∗ ((out + 32#64) ↦₆₄ w4) ∗
      ((out + 40#64) ↦₆₄ w5) ∗ ((out + 48#64) ↦₆₄ w6) ∗ ((out + 56#64) ↦₆₄ w7) ∗
      ((out + 64#64) ↦₆₄ w8) ∗ ((out + 72#64) ↦₆₄ w9) ∗ ((out + 80#64) ↦₆₄ w10) ⊢
      spkAnsAt A out .missing :=
  missing88_pack A out w2 w3 w4 w5 w6 w7 w8 w9 w10

theorem decodeErr88_pack_cells (A : RustAlloc) (out : BitVec 64)
    (e : SignalProtocolError) (u0 u1 u2 u3 u4 u5 w7 w8 w9 w10 : BitVec 64) :
    ((out ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((out + 8#64) ↦₆₄ u0) ∗ ((out + 16#64) ↦₆₄ u1) ∗
      ((out + 24#64) ↦₆₄ u2) ∗ ((out + 32#64) ↦₆₄ u3) ∗ ((out + 40#64) ↦₆₄ u4) ∗
      ((out + 48#64) ↦₆₄ u5) ∗ ((out + 56#64) ↦₆₄ w7) ∗ ((out + 64#64) ↦₆₄ w8) ∗
      ((out + 72#64) ↦₆₄ w9) ∗ ((out + 80#64) ↦₆₄ w10)) ∗
      speDetached A [] u0 u1 u2 u3 u4 u5 e ⊢
      spkAnsAt A out (.decodeErr e) :=
  errResult88_pack A [] out u0 u1 u2 u3 u4 u5 w7 w8 w9 w10 e

theorem found88_pack_cells (A : RustAlloc) (out : BitVec 64) (r : SignedPreKeyRecord)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) :
    ((out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗
      ((out + 24#64) ↦₆₄ w3) ∗ ((out + 32#64) ↦₆₄ w4) ∗ ((out + 40#64) ↦₆₄ w5) ∗
      ((out + 48#64) ↦₆₄ w6) ∗ ((out + 56#64) ↦₆₄ w7) ∗ ((out + 64#64) ↦₆₄ w8) ∗
      ((out + 72#64) ↦₆₄ w9) ∗ ((out + 80#64) ↦₆₄ w10)) ∗
      spkStructDetached A r.signedPreKey w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ⊢
      spkAnsAt A out (.found r) :=
  spkStruct_pack A out r.signedPreKey w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10

/-! ## 4. Shared post/panic predicates, framed cut combinators, and shared epilogue -/

def spkPostQ (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (calleeStk : Nat) (x : PkPollGhost) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (spkGetPollInnerSpec rd pathOk A calleeStk).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

def spkPanicQp (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (calleeStk : Nat) (x : PkPollGhost) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (spkGetPollInnerSpec rd pathOk A calleeStk).onPanic x s0 sf ∗ R)

theorem sepWP_entails_step {prog : Program} {pc : BitVec 64} {s : State}
    {T T' P : SepProp} {post : State → SepProp → Prop}
    (hT : T ⊢ T') {F : SepProp}
    (hP : P ⊢ T ∗ F := by sep_frame)
    (h : SepWP prog pc s (T' ∗ F) post) : SepWP prog pc s P post :=
  SepWP.weaken_pre (Entails.trans hP (sepConj_mono_left hT)) h

theorem sepWP_frame_right {prog : Program} {target_pc : BitVec 64}
    {s : State} {P F : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog target_pc s P (fun sm Pm => post sm (Pm ∗ F))) :
    SepWP prog target_pc s (P ∗ F) post := by
  unfold SepWP reaches_pc at h ⊢
  intro R hm hL
  rw [sepConj_assoc] at hm
  rcases h (F ∗ R) hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pm, hmf, hp⟩ | ⟨_, hf⟩⟩
  · rw [← sepConj_assoc] at hmf
    exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pm ∗ F, hmf, hp⟩⟩
  · exact False.elim (not_satisfies_false_sepConj hf)

theorem sp248_8 (sp : BitVec 64) : sp - 248#64 + 8#64 = sp - 240#64 := by bv_omega
theorem sp248_16 (sp : BitVec 64) : sp - 248#64 + 16#64 = sp - 232#64 := by bv_omega
theorem sp200_8 (sp : BitVec 64) : sp - 200#64 + 8#64 = sp - 192#64 := by bv_omega
theorem sp200_16 (sp : BitVec 64) : sp - 200#64 + 16#64 = sp - 184#64 := by bv_omega
theorem sp200_24 (sp : BitVec 64) : sp - 200#64 + 24#64 = sp - 176#64 := by bv_omega
theorem sp200_32 (sp : BitVec 64) : sp - 200#64 + 32#64 = sp - 168#64 := by bv_omega
theorem sp200_40 (sp : BitVec 64) : sp - 200#64 + 40#64 = sp - 160#64 := by bv_omega
theorem sp200_48 (sp : BitVec 64) : sp - 200#64 + 48#64 = sp - 152#64 := by bv_omega
theorem sp200_56 (sp : BitVec 64) : sp - 200#64 + 56#64 = sp - 144#64 := by bv_omega
theorem sp200_64 (sp : BitVec 64) : sp - 200#64 + 64#64 = sp - 136#64 := by bv_omega
theorem sp200_72 (sp : BitVec 64) : sp - 200#64 + 72#64 = sp - 128#64 := by bv_omega
theorem sp200_80 (sp : BitVec 64) : sp - 200#64 + 80#64 = sp - 120#64 := by bv_omega

theorem sepWP_frame_cut {prog : Program} {img : Obj.Image} {mid target_pc : BitVec 64}
    {s : State} {P P_sub Q_sub F : SepProp} {post : State → SepProp → Prop}
    {Φ : State → Prop}
    (hinv : ImgCallInv img s)
    (h1 : SepWP prog mid s P_sub (fun sm Pm => sm.spAligned = true ∧ Φ sm ∧ (Pm ⊢ Q_sub)))
    (hP : P ⊢ P_sub ∗ F := by
      try simp only [words11At, words6At, spkSavedAt,
        sp248_8, sp248_16, sp200_8, sp200_16, sp200_24, sp200_32, sp200_40,
        sp200_48, sp200_56, sp200_64, sp200_72, sp200_80]
      sep_frame)
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → sm.spAligned = true →
      ImgCallInv img sm → Φ sm → SepWP prog target_pc sm (Q_sub ∗ F) post) :
    SepWP prog target_pc s P post := by
  refine SepWP.weaken_pre hP ?_
  refine SepWP.of_sepWP_inv (mid := mid) hinv.1 hinv.2 ?_
  exact sepWP_frame_right (SepWP.mono h1 fun sm Pm hpcm hrunm ⟨hspm, hΦm, hent⟩ hfl hsym =>
    SepWP.weaken_pre (sepConj_mono_left hent) (h2 sm hpcm hrunm hspm ⟨hfl, hsym⟩ hΦm))

theorem sepWPp_frame_cut {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P P_sub Q_sub F : SepProp} {post Qp : State → SepProp → Prop}
    {Φ : State → Prop}
    (hinv : ImgCallInv img s)
    (h1 : SepWP prog mid s P_sub (fun sm Pm => sm.spAligned = true ∧ Φ sm ∧ (Pm ⊢ Q_sub)))
    (hP : P ⊢ P_sub ∗ F := by
      try simp only [words11At, words6At, spkSavedAt,
        sp248_8, sp248_16, sp200_8, sp200_16, sp200_24, sp200_32, sp200_40,
        sp200_48, sp200_56, sp200_64, sp200_72, sp200_80]
      sep_frame)
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → sm.spAligned = true →
      ImgCallInv img sm → Φ sm → SepWPp prog ret sm (Q_sub ∗ F) post Qp) :
    SepWPp prog ret s P post Qp := by
  unfold SepWP reaches_pc at h1
  intro R hm hL
  have hm' : s.mem ⊨ P_sub ∗ (F ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hP) hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hpm, hspm, hΦm, hent⟩ | ⟨_, hf⟩⟩ := h1 (F ∗ R) hm' hL
  · rw [← sepConj_assoc] at hpm
    obtain ⟨sf, hsteps', hout'⟩ := h2 sm hpcm hrunm hspm (ImgCallInv.of_steps hinv hsteps) hΦm
      R (Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hpm) (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact False.elim (not_satisfies_false_sepConj hf)

theorem trace_ans_congr {rd : ReadRule} {x : PkPollGhost} {s0 s sf : State}
    {ans : PkAns SignedPreKeyRecord}
    (htr : sf.trace = s.trace)
    (h : ans = pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          s.trace = s0.trace) :
    ans = pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
      sf.trace = s0.trace :=
  ⟨h.1, htr.trans h.2⟩

def spkEpiPre (A : RustAlloc) (calleeStk : Nat) (x : PkPollGhost) (s0 : State)
    (D : SepProp)
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : BitVec 64)
    (a0 o7 o8 o9 o10 : BitVec 64)
    (o5 o6 b2 b3 b4 : BitVec 64)
    (c0 c1 c2 c3 c4 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 : BitVec 64)
    (f0 f1 f2 f3 f4 : BitVec 64) : SepProp :=
  D ∗
  words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
  (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
  dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 384#64) calleeStk ∗ spkPollSlack s0.sp ∗
  ((s0.sp - 376#64) ↦₆₄ a0) ∗ ((s0.sp - 368#64) ↦₆₄ o7) ∗ ((s0.sp - 360#64) ↦₆₄ o8) ∗
  ((s0.sp - 352#64) ↦₆₄ o9) ∗ ((s0.sp - 344#64) ↦₆₄ o10) ∗
  ((s0.sp - 336#64) ↦₆₄ o5) ∗ ((s0.sp - 328#64) ↦₆₄ o6) ∗ ((s0.sp - 320#64) ↦₆₄ b2) ∗
  ((s0.sp - 312#64) ↦₆₄ b3) ∗ ((s0.sp - 304#64) ↦₆₄ b4) ∗
  ((s0.sp - 296#64) ↦₆₄ c0) ∗ ((s0.sp - 288#64) ↦₆₄ c1) ∗ ((s0.sp - 280#64) ↦₆₄ c2) ∗
  ((s0.sp - 272#64) ↦₆₄ c3) ∗ ((s0.sp - 264#64) ↦₆₄ c4) ∗
  ((s0.sp - 248#64) ↦₆₄ d0) ∗ ((s0.sp - 240#64) ↦₆₄ d1) ∗ ((s0.sp - 232#64) ↦₆₄ d2) ∗
  ((s0.sp - 224#64) ↦₆₄ d3) ∗ ((s0.sp - 216#64) ↦₆₄ d4) ∗
  ((s0.sp - 200#64) ↦₆₄ e0) ∗ ((s0.sp - 192#64) ↦₆₄ e1) ∗ ((s0.sp - 184#64) ↦₆₄ e2) ∗
  ((s0.sp - 176#64) ↦₆₄ e3) ∗ ((s0.sp - 168#64) ↦₆₄ e4) ∗ ((s0.sp - 160#64) ↦₆₄ e5) ∗
  ((s0.sp - 152#64) ↦₆₄ f0) ∗ ((s0.sp - 144#64) ↦₆₄ f1) ∗ ((s0.sp - 136#64) ↦₆₄ f2) ∗
  ((s0.sp - 128#64) ↦₆₄ f3) ∗ ((s0.sp - 120#64) ↦₆₄ f4) ∗
  spkSavedAt s0

private theorem spkEpiPost_pack (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (calleeStk : Nat) (x : PkPollGhost) (s0 sf : State)
    (ans : PkAns SignedPreKeyRecord) (D : SepProp)
    (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 : BitVec 64)
    (a0 b2 b3 b4 c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 e5 f0 f1 f2 f3 f4 : BitVec 64)
    (hpack : words11At x.out o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 ∗ D ⊢ spkAnsAt A x.out ans)
    (hans : ans = pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          sf.trace = s0.trace) :
    ((x.out ↦₆₄ o0) ∗ ((x.out + 8#64) ↦₆₄ o1) ∗ ((x.out + 16#64) ↦₆₄ o2) ∗
      ((x.out + 24#64) ↦₆₄ o3) ∗ ((x.out + 32#64) ↦₆₄ o4) ∗ ((x.out + 40#64) ↦₆₄ o5) ∗
      ((x.out + 48#64) ↦₆₄ o6) ∗ ((x.out + 56#64) ↦₆₄ o7) ∗ ((x.out + 64#64) ↦₆₄ o8) ∗
      ((x.out + 72#64) ↦₆₄ o9) ∗ ((x.out + 80#64) ↦₆₄ o10)) ∗ D ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
      dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 384#64) calleeStk ∗
      (spkPollSlack s0.sp ∗
        ((((s0.sp - 376#64) ↦₆₄ a0) ∗ ((s0.sp - 368#64) ↦₆₄ o7) ∗ ((s0.sp - 360#64) ↦₆₄ o8) ∗
          ((s0.sp - 352#64) ↦₆₄ o9) ∗ ((s0.sp - 344#64) ↦₆₄ o10)) ∗
         (((s0.sp - 336#64) ↦₆₄ o5) ∗ ((s0.sp - 328#64) ↦₆₄ o6) ∗ ((s0.sp - 320#64) ↦₆₄ b2) ∗
          ((s0.sp - 312#64) ↦₆₄ b3) ∗ ((s0.sp - 304#64) ↦₆₄ b4)) ∗
         (((s0.sp - 296#64) ↦₆₄ c0) ∗ ((s0.sp - 288#64) ↦₆₄ c1) ∗ ((s0.sp - 280#64) ↦₆₄ c2) ∗
          ((s0.sp - 272#64) ↦₆₄ c3) ∗ ((s0.sp - 264#64) ↦₆₄ c4))) ∗
        (((s0.sp - 248#64) ↦₆₄ d0) ∗ ((s0.sp - 240#64) ↦₆₄ d1) ∗ ((s0.sp - 232#64) ↦₆₄ d2) ∗
          ((s0.sp - 224#64) ↦₆₄ d3) ∗ ((s0.sp - 216#64) ↦₆₄ d4)) ∗
        (((s0.sp - 200#64) ↦₆₄ e0) ∗ ((s0.sp - 192#64) ↦₆₄ e1) ∗ ((s0.sp - 184#64) ↦₆₄ e2) ∗
          ((s0.sp - 176#64) ↦₆₄ e3) ∗ ((s0.sp - 168#64) ↦₆₄ e4) ∗ ((s0.sp - 160#64) ↦₆₄ e5)) ∗
        (((s0.sp - 152#64) ↦₆₄ f0) ∗ ((s0.sp - 144#64) ↦₆₄ f1) ∗ ((s0.sp - 136#64) ↦₆₄ f2) ∗
          ((s0.sp - 128#64) ↦₆₄ f3) ∗ ((s0.sp - 120#64) ↦₆₄ f4)) ∗
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ⊢
      (spkGetPollInnerSpec rd pathOk A calleeStk).post x s0 sf := by
  have hans' : words11At x.out o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 ∗ D ⊢
      ∃∗ a : PkAns SignedPreKeyRecord,
        ⌜a = pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
            sf.trace = s0.trace⌝ ∗
        spkAnsAt A x.out a :=
    Entails.trans hpack (spkAns_intro rd A x s0 sf ans hans)
  dsimp only [words11At] at hans'
  have hsaved :
      (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ⊢
      cells (s0.sp - 96#64) 6 ∗ cells (s0.sp - 48#64) 6 := by
    have hsplit :
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
         ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
         ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) =
        ((((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25)) ∗
         (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) := by
      ac_rfl
    rw [hsplit]
    exact sepConj_mono
      (cells_pack_6_96 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
        (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25))
      (cells_pack_6_48 s0.sp (s0.readReg64 .x24) (s0.readReg64 .x23)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
  have hcells := Entails.trans
    (sepConj_mono_right
      (sepConj_mono
        (sepConj_mono (cells_pack_5_376 s0.sp a0 o7 o8 o9 o10)
          (sepConj_mono (cells_pack_5_336 s0.sp o5 o6 b2 b3 b4)
            (cells_pack_5_296 s0.sp c0 c1 c2 c3 c4)))
        (sepConj_mono (cells_pack_5_248 s0.sp d0 d1 d2 d3 d4)
          (sepConj_mono (cells_pack_6_200 s0.sp e0 e1 e2 e3 e4 e5)
            (sepConj_mono (cells_pack_5_152 s0.sp f0 f1 f2 f3 f4) hsaved)))))
    (frame48_pack_groups s0.sp)
  dsimp only [spkGetPollInnerSpec]
  have hassoc :
      (((x.out ↦₆₄ o0) ∗ ((x.out + 8#64) ↦₆₄ o1) ∗ ((x.out + 16#64) ↦₆₄ o2) ∗
        ((x.out + 24#64) ↦₆₄ o3) ∗ ((x.out + 32#64) ↦₆₄ o4) ∗ ((x.out + 40#64) ↦₆₄ o5) ∗
        ((x.out + 48#64) ↦₆₄ o6) ∗ ((x.out + 56#64) ↦₆₄ o7) ∗ ((x.out + 64#64) ↦₆₄ o8) ∗
        ((x.out + 72#64) ↦₆₄ o9) ∗ ((x.out + 80#64) ↦₆₄ o10)) ∗ D ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 384#64) calleeStk ∗
        (spkPollSlack s0.sp ∗
          ((((s0.sp - 376#64) ↦₆₄ a0) ∗ ((s0.sp - 368#64) ↦₆₄ o7) ∗ ((s0.sp - 360#64) ↦₆₄ o8) ∗
            ((s0.sp - 352#64) ↦₆₄ o9) ∗ ((s0.sp - 344#64) ↦₆₄ o10)) ∗
           (((s0.sp - 336#64) ↦₆₄ o5) ∗ ((s0.sp - 328#64) ↦₆₄ o6) ∗ ((s0.sp - 320#64) ↦₆₄ b2) ∗
            ((s0.sp - 312#64) ↦₆₄ b3) ∗ ((s0.sp - 304#64) ↦₆₄ b4)) ∗
           (((s0.sp - 296#64) ↦₆₄ c0) ∗ ((s0.sp - 288#64) ↦₆₄ c1) ∗ ((s0.sp - 280#64) ↦₆₄ c2) ∗
            ((s0.sp - 272#64) ↦₆₄ c3) ∗ ((s0.sp - 264#64) ↦₆₄ c4))) ∗
          (((s0.sp - 248#64) ↦₆₄ d0) ∗ ((s0.sp - 240#64) ↦₆₄ d1) ∗ ((s0.sp - 232#64) ↦₆₄ d2) ∗
            ((s0.sp - 224#64) ↦₆₄ d3) ∗ ((s0.sp - 216#64) ↦₆₄ d4)) ∗
          (((s0.sp - 200#64) ↦₆₄ e0) ∗ ((s0.sp - 192#64) ↦₆₄ e1) ∗ ((s0.sp - 184#64) ↦₆₄ e2) ∗
            ((s0.sp - 176#64) ↦₆₄ e3) ∗ ((s0.sp - 168#64) ↦₆₄ e4) ∗ ((s0.sp - 160#64) ↦₆₄ e5)) ∗
          (((s0.sp - 152#64) ↦₆₄ f0) ∗ ((s0.sp - 144#64) ↦₆₄ f1) ∗ ((s0.sp - 136#64) ↦₆₄ f2) ∗
            ((s0.sp - 128#64) ↦₆₄ f3) ∗ ((s0.sp - 120#64) ↦₆₄ f4)) ∗
          (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
            ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
            ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) =
      ((((x.out ↦₆₄ o0) ∗ ((x.out + 8#64) ↦₆₄ o1) ∗ ((x.out + 16#64) ↦₆₄ o2) ∗
        ((x.out + 24#64) ↦₆₄ o3) ∗ ((x.out + 32#64) ↦₆₄ o4) ∗ ((x.out + 40#64) ↦₆₄ o5) ∗
        ((x.out + 48#64) ↦₆₄ o6) ∗ ((x.out + 56#64) ↦₆₄ o7) ∗ ((x.out + 64#64) ↦₆₄ o8) ∗
        ((x.out + 72#64) ↦₆₄ o9) ∗ ((x.out + 80#64) ↦₆₄ o10)) ∗ D) ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 384#64) calleeStk ∗
        (spkPollSlack s0.sp ∗
          ((((s0.sp - 376#64) ↦₆₄ a0) ∗ ((s0.sp - 368#64) ↦₆₄ o7) ∗ ((s0.sp - 360#64) ↦₆₄ o8) ∗
            ((s0.sp - 352#64) ↦₆₄ o9) ∗ ((s0.sp - 344#64) ↦₆₄ o10)) ∗
           (((s0.sp - 336#64) ↦₆₄ o5) ∗ ((s0.sp - 328#64) ↦₆₄ o6) ∗ ((s0.sp - 320#64) ↦₆₄ b2) ∗
            ((s0.sp - 312#64) ↦₆₄ b3) ∗ ((s0.sp - 304#64) ↦₆₄ b4)) ∗
           (((s0.sp - 296#64) ↦₆₄ c0) ∗ ((s0.sp - 288#64) ↦₆₄ c1) ∗ ((s0.sp - 280#64) ↦₆₄ c2) ∗
            ((s0.sp - 272#64) ↦₆₄ c3) ∗ ((s0.sp - 264#64) ↦₆₄ c4))) ∗
          (((s0.sp - 248#64) ↦₆₄ d0) ∗ ((s0.sp - 240#64) ↦₆₄ d1) ∗ ((s0.sp - 232#64) ↦₆₄ d2) ∗
            ((s0.sp - 224#64) ↦₆₄ d3) ∗ ((s0.sp - 216#64) ↦₆₄ d4)) ∗
          (((s0.sp - 200#64) ↦₆₄ e0) ∗ ((s0.sp - 192#64) ↦₆₄ e1) ∗ ((s0.sp - 184#64) ↦₆₄ e2) ∗
            ((s0.sp - 176#64) ↦₆₄ e3) ∗ ((s0.sp - 168#64) ↦₆₄ e4) ∗ ((s0.sp - 160#64) ↦₆₄ e5)) ∗
          (((s0.sp - 152#64) ↦₆₄ f0) ∗ ((s0.sp - 144#64) ↦₆₄ f1) ∗ ((s0.sp - 136#64) ↦₆₄ f2) ∗
            ((s0.sp - 128#64) ↦₆₄ f3) ∗ ((s0.sp - 120#64) ↦₆₄ f4)) ∗
          (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
            ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
            ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) := by
    ac_rfl
  rw [hassoc]
  exact sepConj_mono hans'
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hcells))))))

theorem epilogue_ok
    {img : Obj.Image} {ext : String → Option (State → State)}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustAlloc} {calleeStk : Nat} {x : PkPollGhost} {R : SepProp}
    {s0 s : State} {ans : PkAns SignedPreKeyRecord} {D P : SepProp}
    {o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 : BitVec 64}
    {u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : BitVec 64}
    {a0 b2 b3 b4 c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 e5 f0 f1 f2 f3 f4 : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spkGetPollName + bv% 344)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hvr : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx26 : s.readReg64 .x26 = o0)
    (hx25 : s.readReg64 .x25 = o1)
    (hx23 : s.readReg64 .x23 = o2)
    (hx24 : s.readReg64 .x24 = o3)
    (hx21 : s.readReg64 .x21 = o4)
    (hpack : words11At x.out o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 ∗ D ⊢ spkAnsAt A x.out ans)
    (hans : ans = pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          s.trace = s0.trace)
    (hP : P ⊢ spkEpiPre A calleeStk x s0 D
      u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10
      a0 o7 o8 o9 o10 o5 o6 b2 b3 b4 c0 c1 c2 c3 c4 d0 d1 d2 d3 d4
      e0 e1 e2 e3 e4 e5 f0 f1 f2 f3 f4 := by
        try simp only [spkEpiPre, words11At, words6At, spkSavedAt,
          sp248_8, sp248_16, sp200_8, sp200_16, sp200_24, sp200_32, sp200_40,
          sp200_48, sp200_56, sp200_64, sp200_72, sp200_80]
        sep_frame) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spkPostQ rd pathOk A calleeStk x R s0) := by
  refine SepWP.weaken_pre hP ?_
  have hfn : libsignalSessionCode.fnOff spkGetPollName =
      num% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}") :=
    spkGetPoll_fnOff
  code_fetches CryptoVerification.libsignalSessionCode cliSpkGetPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}")) 480
  dsimp only [tripleRatchetProgAtExt, spkEpiPre, spkSavedAt, words11At, spkPostQ] at hpc ⊢
  clear hfn hP
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr spkGetPollName = fnBase
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?]
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm, ?_, ?_⟩
  · refine Entails.trans (Entails.of_eq (by ac_rfl))
      (spkEpiPost_pack rd pathOk A calleeStk x s0 _ ans D
        o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10
        a0 b2 b3 b4 c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 e5 f0 f1 f2 f3 f4
        hpack (trace_ans_congr (s := s) rfl hans))
  · simp only [wp_norm, arm64_norm]
  · rw [CalleeSavedPreserved.iff_regs]
    simp only [wp_norm, arm64_norm, hvr]

end CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers
