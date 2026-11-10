/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.Layout
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.Fetches
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Epilogue and Branch Helpers for `get_pre_key::{closure#0}`

Stack-frame decomposition (32 cells), shared return epilogue (`+348 .. +404`), and branch lemmas
for `Dir::get` errors, `PreKeyRecord::deserialize` errors, missing files, and decoded records.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary
open CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace CliPkGetPollNorm

@[arm64_norm ↓, wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem sp_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem sp_setPState_pre (s : State) (ps : PState) :
    (s.setPState ps).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[arm64_norm ↓, wp_norm ↓]
theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg64_setPState_pre (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_setPState_pre (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) (r : Reg) :
    (s.writeVReg128 idx v).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg_setMem_pre (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg_setPState_pre (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setPC_pre (s : State) (pc : BitVec 64) (idx : BitVec 5) :
    (s.setPC pc).readVReg128 idx = s.readVReg128 idx := by
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
theorem readVReg128_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) (idx : BitVec 5) :
    (s.writeReg32 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).fs = s.fs := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).fs = s.fs := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_setPState_pre (s : State) (ps : PState) :
    (s.setPState ps).fs = s.fs := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).fs = s.fs := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_setPState_pre (s : State) (ps : PState) :
    (s.setPState ps).trace = s.trace := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).trace = s.trace := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem calleeSavedVRegs_setPC_pre (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem calleeSavedVRegs_writeVReg128_zero (s : State) (val : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 val) = calleeSavedVRegs s :=
  calleeSavedVRegs_writeVReg128 s 0#5 val

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_append_lo (hi lo : BitVec 64) :
    BitVec.extractLsb' 0 64 (hi ++ lo) = lo := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_append_hi (hi lo : BitVec 64) :
    BitVec.extractLsb' 64 64 (hi ++ lo) = hi := by
  bv_bits

@[arm64_norm, wp_norm]
theorem zext32_trunc32 (u : BitVec 32) :
    (u.zeroExtend 64).truncate 32 = u := by
  bv_bits

@[arm64_norm, wp_norm]
theorem sp_restore_256 (sp0 : BitVec 64) :
    sp0 - 256#64 + 256#64 = sp0 := by
  bv_bits

@[arm64_norm, wp_norm]
theorem cond_eq_adds64 (x y : BitVec 64) :
    ConditionHolds .EQ (AddWithCarry64 x y false).2 = (x + y == 0#64) := by
  have hw : BitVec.setWidth 64 (BitVec.setWidth 65 y + BitVec.setWidth 65 x) = x + y := by
    bv_bits
  show (AddWithCarry64 x y false).2.z = (x + y == 0#64)
  simp [AddWithCarry64, hw]

@[arm64_norm, wp_norm]
theorem cond_ne_adds64 (x y : BitVec 64) :
    ConditionHolds .NE (AddWithCarry64 x y false).2 = (x + y != 0#64) := by
  change (!(ConditionHolds .EQ (AddWithCarry64 x y false).2)) = (x + y != 0#64)
  rw [cond_eq_adds64]
  rfl

@[arm64_norm, wp_norm]
theorem cond_eq_addsPState64 (x y : BitVec 64) :
    ConditionHolds .EQ (addsPState64 x y) = (x + y == 0#64) := by
  have h : addsPState64 x y = (AddWithCarry64 x y false).2 := by
    with_unfolding_all rfl
  rw [h, cond_eq_adds64]

@[arm64_norm, wp_norm]
theorem cond_ne_addsPState64 (x y : BitVec 64) :
    ConditionHolds .NE (addsPState64 x y) = (x + y != 0#64) := by
  have h : addsPState64 x y = (AddWithCarry64 x y false).2 := by
    with_unfolding_all rfl
  rw [h, cond_ne_adds64]

end CliPkGetPollNorm

open CliPkGetPollNorm

theorem bind_sepWP_state {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (h : let st := s; SepWP prog ret st P Q) :
    SepWP prog ret s P Q := h

theorem close_panic_subgoal {s0 s_call sf : State} {F R : SepProp}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  refine allowPanic_frame ?_ (by rwa [sepConj_assoc] at hm)
  rintro ⟨hfail, hpref⟩
  unfold allocFailedIn at hfail ⊢
  rw [htr] at hfail hpref
  exact ⟨hfail, hpref⟩

private theorem bytes_zero_elim {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {ptr : BitVec 64} {bs : List (BitVec 8)} {Rest : SepProp}
    {Q : State → SepProp → Prop} {P : SepProp}
    (heq : P = ((ptr ↦ₛ bs) ∗ vecU8BufRest A 0#64 ptr bs) ∗ Rest)
    (h : SepWP prog ret s Rest Q) :
    SepWP prog ret s P Q := by
  rw [heq, bytes_sep_vecU8BufRest_zero]
  exact SepWP.pure_elim fun _ => h

/-! ## Stack frame layout (`sp - 256` .. `sp - 8`, 32 cells) -/

def pkPollSlack (sp : BitVec 64) : SepProp :=
  cells (sp - 208#64) 1 ∗ cells (sp - 160#64) 1

def pkSavedRegs (sp : BitVec 64) (s0 : State) : SepProp :=
  ((sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)

def pkBoxKeep (x : PkPollGhost) (s0 : State) : SepProp :=
  pkPollSlack s0.sp ∗ pkSavedRegs s0.sp s0 ∗
    (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
    memRegion x.out 56

theorem cells_32_split (sp : BitVec 64) :
    cells (sp - 256#64) 32 =
      pkPollSlack sp ∗
        cells (sp - 256#64) 6 ∗ cells (sp - 200#64) 3 ∗
        cells (sp - 176#64) 2 ∗ cells (sp - 152#64) 7 ∗
        cells (sp - 96#64) 12 := by
  rw [show (32 : Nat) = 6 + 26 from rfl, cells_split_sub sp 256 208 6 26,
    show (26 : Nat) = 1 + 25 from rfl, cells_split_sub sp 208 200 1 25,
    show (25 : Nat) = 3 + 22 from rfl, cells_split_sub sp 200 176 3 22,
    show (22 : Nat) = 2 + 20 from rfl, cells_split_sub sp 176 160 2 20,
    show (20 : Nat) = 1 + 19 from rfl, cells_split_sub sp 160 152 1 19,
    show (19 : Nat) = 7 + 12 from rfl, cells_split_sub sp 152 96 7 12]
  dsimp only [pkPollSlack]
  ac_rfl

theorem cells_sub_6_256_eq (sp : BitVec 64) :
    cells (sp - 256#64) 6 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 256#64) ↦₆₄ v0) ∗ ((sp - 248#64) ↦₆₄ v1) ∗ ((sp - 240#64) ↦₆₄ v2) ∗
        ((sp - 232#64) ↦₆₄ v3) ∗ ((sp - 224#64) ↦₆₄ v4) ∗ ((sp - 216#64) ↦₆₄ v5) := by
  cells_unfold

theorem cells_sub_3_200_eq (sp : BitVec 64) :
    cells (sp - 200#64) 3 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        ((sp - 200#64) ↦₆₄ v0) ∗ ((sp - 192#64) ↦₆₄ v1) ∗ ((sp - 184#64) ↦₆₄ v2) := by
  cells_unfold

theorem cells_sub_2_176_eq (sp : BitVec 64) :
    cells (sp - 176#64) 2 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64,
        ((sp - 176#64) ↦₆₄ v0) ∗ ((sp - 168#64) ↦₆₄ v1) := by
  cells_unfold

theorem cells_sub_7_152_eq (sp : BitVec 64) :
    cells (sp - 152#64) 7 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64,
        ((sp - 152#64) ↦₆₄ v0) ∗ ((sp - 144#64) ↦₆₄ v1) ∗ ((sp - 136#64) ↦₆₄ v2) ∗
        ((sp - 128#64) ↦₆₄ v3) ∗ ((sp - 120#64) ↦₆₄ v4) ∗ ((sp - 112#64) ↦₆₄ v5) ∗
        ((sp - 104#64) ↦₆₄ v6) := by
  cells_unfold

theorem cells_sub_12_96_eq (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
      ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
        ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗ ((sp - 32#64) ↦₆₄ v8) ∗
        ((sp - 24#64) ↦₆₄ v9) ∗ ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11) := by
  cells_unfold

private theorem pkFrame_pack (sp : BitVec 64) (s0 : State)
    (u0 u1 u2 u3 u4 u5 n0 n1 n2 k0 k1 g0 g1 g2 g3 g4 g5 g6 : BitVec 64) :
    (pkPollSlack sp ∗ pkSavedRegs sp s0 ∗
      ((sp - 256#64) ↦₆₄ u0) ∗ ((sp - 248#64) ↦₆₄ u1) ∗
      ((sp - 240#64) ↦₆₄ u2) ∗ ((sp - 232#64) ↦₆₄ u3) ∗
      ((sp - 224#64) ↦₆₄ u4) ∗ ((sp - 216#64) ↦₆₄ u5) ∗
      ((sp - 200#64) ↦₆₄ n0) ∗ ((sp - 192#64) ↦₆₄ n1) ∗ ((sp - 184#64) ↦₆₄ n2) ∗
      ((sp - 176#64) ↦₆₄ k0) ∗ ((sp - 168#64) ↦₆₄ k1) ∗
      ((sp - 152#64) ↦₆₄ g0) ∗ ((sp - 144#64) ↦₆₄ g1) ∗
      ((sp - 136#64) ↦₆₄ g2) ∗ ((sp - 128#64) ↦₆₄ g3) ∗
      ((sp - 120#64) ↦₆₄ g4) ∗ ((sp - 112#64) ↦₆₄ g5) ∗ ((sp - 104#64) ↦₆₄ g6)) ⊢
      cells (sp - 256#64) 32 := by
  rw [cells_32_split]
  have h6 : (((sp - 256#64) ↦₆₄ u0) ∗ ((sp - 248#64) ↦₆₄ u1) ∗ ((sp - 240#64) ↦₆₄ u2) ∗
      ((sp - 232#64) ↦₆₄ u3) ∗ ((sp - 224#64) ↦₆₄ u4) ∗ ((sp - 216#64) ↦₆₄ u5)) ⊢
      cells (sp - 256#64) 6 := by
    rw [cells_sub_6_256_eq]
    exact Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.sepExists_right u2
      (Entails.sepExists_right u3 (Entails.sepExists_right u4
        (Entails.sepExists_right u5 (Entails.refl _))))))
  have h3 : (((sp - 200#64) ↦₆₄ n0) ∗ ((sp - 192#64) ↦₆₄ n1) ∗ ((sp - 184#64) ↦₆₄ n2)) ⊢
      cells (sp - 200#64) 3 := by
    rw [cells_sub_3_200_eq]
    exact Entails.sepExists_right n0 (Entails.sepExists_right n1
      (Entails.sepExists_right n2 (Entails.refl _)))
  have h2 : (((sp - 176#64) ↦₆₄ k0) ∗ ((sp - 168#64) ↦₆₄ k1)) ⊢ cells (sp - 176#64) 2 := by
    rw [cells_sub_2_176_eq]
    exact Entails.sepExists_right k0 (Entails.sepExists_right k1 (Entails.refl _))
  have h7 : (((sp - 152#64) ↦₆₄ g0) ∗ ((sp - 144#64) ↦₆₄ g1) ∗ ((sp - 136#64) ↦₆₄ g2) ∗
      ((sp - 128#64) ↦₆₄ g3) ∗ ((sp - 120#64) ↦₆₄ g4) ∗ ((sp - 112#64) ↦₆₄ g5) ∗
      ((sp - 104#64) ↦₆₄ g6)) ⊢ cells (sp - 152#64) 7 := by
    rw [cells_sub_7_152_eq]
    exact Entails.sepExists_right g0 (Entails.sepExists_right g1 (Entails.sepExists_right g2
      (Entails.sepExists_right g3 (Entails.sepExists_right g4 (Entails.sepExists_right g5
        (Entails.sepExists_right g6 (Entails.refl _)))))))
  have h12 : pkSavedRegs sp s0 ⊢ cells (sp - 96#64) 12 := by
    unfold pkSavedRegs
    rw [cells_sub_12_96_eq]
    exact Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
        (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
          (Entails.sepExists_right _ (Entails.sepExists_right _
            (Entails.sepExists_right _ (Entails.refl _))))))))))))
  refine Entails.trans (Q :=
    pkPollSlack sp ∗
      (((sp - 256#64) ↦₆₄ u0) ∗ ((sp - 248#64) ↦₆₄ u1) ∗ ((sp - 240#64) ↦₆₄ u2) ∗
        ((sp - 232#64) ↦₆₄ u3) ∗ ((sp - 224#64) ↦₆₄ u4) ∗ ((sp - 216#64) ↦₆₄ u5)) ∗
      (((sp - 200#64) ↦₆₄ n0) ∗ ((sp - 192#64) ↦₆₄ n1) ∗ ((sp - 184#64) ↦₆₄ n2)) ∗
      (((sp - 176#64) ↦₆₄ k0) ∗ ((sp - 168#64) ↦₆₄ k1)) ∗
      (((sp - 152#64) ↦₆₄ g0) ∗ ((sp - 144#64) ↦₆₄ g1) ∗ ((sp - 136#64) ↦₆₄ g2) ∗
        ((sp - 128#64) ↦₆₄ g3) ∗ ((sp - 120#64) ↦₆₄ g4) ∗ ((sp - 112#64) ↦₆₄ g5) ∗
        ((sp - 104#64) ↦₆₄ g6)) ∗
      pkSavedRegs sp s0) (Entails.of_eq (by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono h6
    (sepConj_mono h3 (sepConj_mono h2 (sepConj_mono h7 h12))))

/-! ## Shared epilogue helper (`+348` .. `+404` `ret`) -/

def pkEpiloguePost (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (calleeStk : Nat) (x : PkPollGhost) (s0 sf : State) (P_f : SepProp) : Prop :=
  sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
    (P_f ⊢ (pkGetPollInnerSpec rd pathOk A calleeStk).post x s0 sf)

theorem step_epilogue_348 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat} {x : PkPollGhost} {s0 s : State} {P : SepProp}
    (ans : PkAns PreKeyRecord)
    (o0 o1 o2 o3 o4 o5 o6 u2 u3 u4 u5 n0 n1 n2 k0 k1 g0 g1 g2 g3 g4 g5 g6 : BitVec 64)
    (payload : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr pkGetPollName + bv% (348))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hal0 : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx26 : s.readReg64 .x26 = o0)
    (hx25 : s.readReg64 .x25 = o1)
    (hx23 : s.readReg64 .x23 = o2)
    (hx24 : s.readReg64 .x24 = o3)
    (hx21 : s.readReg64 .x21 = o4)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hAns :
      ans = pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
        s.trace = s0.trace)
    (hReasm :
      ((x.out ↦₆₄ o0) ∗ ((x.out + 8#64) ↦₆₄ o1) ∗
        ((x.out + 16#64) ↦₆₄ o2) ∗ ((x.out + 24#64) ↦₆₄ o3) ∗
        ((x.out + 32#64) ↦₆₄ o4) ∗ ((x.out + 40#64) ↦₆₄ o5) ∗
        ((x.out + 48#64) ↦₆₄ o6)) ∗ payload ⊢
      pkGetAnsAt A x.out ans)
    (hP : P ⊢
      pkBoxKeep x s0 ∗ payload ∗ dirAt A x.self x.dir ∗ A.pool ∗
        stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ o5) ∗ ((s0.sp - 248#64) ↦₆₄ o6) ∗
        ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
        ((s0.sp - 224#64) ↦₆₄ u4) ∗ ((s0.sp - 216#64) ↦₆₄ u5) ∗
        ((s0.sp - 200#64) ↦₆₄ n0) ∗ ((s0.sp - 192#64) ↦₆₄ n1) ∗ ((s0.sp - 184#64) ↦₆₄ n2) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
        ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
        ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6)) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s P
      (pkEpiloguePost rd pathOk A calleeStk x s0) := by
  refine SepWP.weaken_pre hP ?_
  have hal : s.spAligned = true := sp_sub_256_spAligned hal0 hsp
  have hfn : libsignalSessionCode.fnOff pkGetPollName =
      num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") :=
    pkGetPoll_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode cliPkGetPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"))
    348 60
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr pkGetPollName = fnBase
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  unfold pkBoxKeep
  rw [memRegion_56_cells x.out]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => ?_
  unfold pkSavedRegs
  wp_steps
  apply bind_sepWP_state; intro sf
  apply SepWP.done (by simp only [sf, wp_norm, arm64_norm, *])
    (by simp only [sf, wp_norm, arm64_norm, *])
  refine ⟨by simp only [sf, wp_norm, arm64_norm, *], ?_, ?_⟩
  · refine ⟨by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *]⟩
  · have htr_sf : sf.trace = s.trace := by simp only [sf, wp_norm, arm64_norm]
    have hAns' :
        ans = pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          sf.trace = s0.trace :=
      ⟨hAns.1, htr_sf.trans hAns.2⟩
    dsimp only [pkGetPollInnerSpec]
    have hpack := pkFrame_pack s0.sp s0 o5 o6 u2 u3 u4 u5 n0 n1 n2 k0 k1 g0 g1 g2 g3 g4 g5 g6
    refine Entails.trans (Q :=
      (((x.out ↦₆₄ o0) ∗ ((x.out + 8#64) ↦₆₄ o1) ∗
          ((x.out + 16#64) ↦₆₄ o2) ∗ ((x.out + 24#64) ↦₆₄ o3) ∗
          ((x.out + 32#64) ↦₆₄ o4) ∗ ((x.out + 40#64) ↦₆₄ o5) ∗
          ((x.out + 48#64) ↦₆₄ o6)) ∗ payload) ∗
      (pkPollSlack s0.sp ∗ pkSavedRegs s0.sp s0 ∗
        ((s0.sp - 256#64) ↦₆₄ o5) ∗ ((s0.sp - 248#64) ↦₆₄ o6) ∗
        ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
        ((s0.sp - 224#64) ↦₆₄ u4) ∗ ((s0.sp - 216#64) ↦₆₄ u5) ∗
        ((s0.sp - 200#64) ↦₆₄ n0) ∗ ((s0.sp - 192#64) ↦₆₄ n1) ∗ ((s0.sp - 184#64) ↦₆₄ n2) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
        ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
        ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6)) ∗
      ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk)) ?_ ?_
    · unfold pkSavedRegs
      exact Entails.of_eq (by ac_rfl)
    · refine Entails.trans (sepConj_mono hReasm (sepConj_mono_left hpack)) ?_
      refine Entails.trans (Q :=
        pkGetAnsAt A x.out ans ∗
          ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
            dirAt A x.self x.dir ∗ A.pool ∗
            stackAt (s0.sp - 256#64) calleeStk ∗ cells (s0.sp - 256#64) 32))
        (Entails.of_eq (by ac_rfl)) ?_
      exact sepConj_mono_left (Entails.sepExists_right ans (Entails.pure_right hAns' (Entails.refl _)))

/-! ## Branch 1 helper: `Dir::get` returned `Err` (`+200` .. `+232` -> `+348`) -/

theorem step_err_200 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat} {x : PkPollGhost} {s0 s : State} {P : SepProp}
    (hDeallocCells : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pkGetPollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"
          "__rustc::__rust_dealloc"))
      ((deallocBufCellsSpec A calleeStk).inImage img))
    (w1 w2 w3 w4 w5 nCap nPtr nLen u0 u1 u2 u3 u4 u5 k0 k1 g6 : BitVec 64)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr pkGetPollName + bv% (200))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hal0 : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = w3)
    (hx22 : s.readReg64 .x22 = nPtr)
    (hx23 : s.readReg64 .x23 = w1)
    (hx24 : s.readReg64 .x24 = w2)
    (hx25 : s.readReg64 .x25 = speWord 1)
    (hx27 : s.readReg64 .x27 = s0.sp - 152#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hAns :
      (PkAns.readErr : PkAns PreKeyRecord) =
          pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
        s.trace = s0.trace)
    (hP : P ⊢
      pkBoxKeep x s0 ∗ readErrHeap A w1 w2 w3 w4 w5 ∗
        (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A nCap nPtr (keyName x.id) ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
        ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
        ((s0.sp - 224#64) ↦₆₄ u4) ∗ ((s0.sp - 216#64) ↦₆₄ u5) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 144#64) ↦₆₄ w1) ∗
        ((s0.sp - 136#64) ↦₆₄ w2) ∗ ((s0.sp - 128#64) ↦₆₄ w3) ∗
        ((s0.sp - 120#64) ↦₆₄ w4) ∗ ((s0.sp - 112#64) ↦₆₄ w5) ∗ ((s0.sp - 104#64) ↦₆₄ g6)) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s P
      (pkEpiloguePost rd pathOk A calleeStk x s0) := by
  refine SepWP.weaken_pre hP ?_; clear hP
  have hal : s.spAligned = true := sp_sub_256_spAligned hal0 hsp
  have hfn : libsignalSessionCode.fnOff pkGetPollName =
      num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") :=
    pkGetPoll_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode cliPkGetPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"))
    200 36
  dsimp only [tripleRatchetProgAtExt] at hDeallocCells hpc ⊢
  clear hfn
  generalize hfn_eq : (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr pkGetPollName = fnBase at *
  by_cases hnCap : nCap = 0#64
  · subst hnCap
    refine bytes_zero_elim (ptr := nPtr) (bs := keyName x.id)
      (Rest := pkBoxKeep x s0 ∗ readErrHeap A w1 w2 w3 w4 w5 ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
        ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
        ((s0.sp - 224#64) ↦₆₄ u4) ∗ ((s0.sp - 216#64) ↦₆₄ u5) ∗
        ((s0.sp - 200#64) ↦₆₄ 0#64) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 144#64) ↦₆₄ w1) ∗
        ((s0.sp - 136#64) ↦₆₄ w2) ∗ ((s0.sp - 128#64) ↦₆₄ w3) ∗
        ((s0.sp - 120#64) ↦₆₄ w4) ∗ ((s0.sp - 112#64) ↦₆₄ w5) ∗ ((s0.sp - 104#64) ↦₆₄ g6))
      (by ac_rfl) ?_
    wp_steps
    apply bind_sepWP_state; intro s_ep
    have htr_ep : s_ep.trace = s.trace := by simp only [s_ep, wp_norm, arm64_norm]
    have hpc_ep : s_ep.pc = fnBase + bv% (348) := by
      simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega
    subst hfn_eq
    exact step_epilogue_348 .readErr errTag (speWord 1) w1 w2 w3 w4 w5
      u2 u3 u4 u5 0#64 nPtr nLen k0 k1 (speWord 1) w1 w2 w3 w4 w5 g6
      (readErrHeap A w1 w2 w3 w4 w5)
      hpc_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hal0
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *]; rfl)
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      ⟨hAns.1, htr_ep.trans hAns.2⟩
      (readErr_reassemble A x.out w1 w2 w3 w4 w5)
      (Entails.of_eq (by ac_rfl))
  · have hnCap_eq : (nCap == 0#64) = false := beq_eq_false_iff_ne.mpr hnCap
    have hnCap_ne : (nCap != 0#64) = true := bne_iff_ne.mpr hnCap
    apply SepWP.seq_inImage
      (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"
        "__rustc::__rust_dealloc"))
      hinv
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
    intro hinv1
    wp_call_inImage hDeallocCells hinv1 (nPtr, nCap, keyName x.id, s0.sp - 256#64)
    wp_steps
    apply bind_sepWP_state; intro s_ep
    have htr_ep : s_ep.trace = s.trace := by simp only [s_ep, wp_norm, arm64_norm, *]
    have hpc_ep : s_ep.pc = fnBase + bv% (348) := by
      simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega
    subst hfn_eq
    exact step_epilogue_348 .readErr errTag (speWord 1) w1 w2 w3 w4 w5
      u2 u3 u4 u5 nCap nPtr nLen k0 k1 (speWord 1) w1 w2 w3 w4 w5 g6
      (readErrHeap A w1 w2 w3 w4 w5)
      hpc_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hal0
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *]; rfl)
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      ⟨hAns.1, htr_ep.trans hAns.2⟩
      (readErr_reassemble A x.out w1 w2 w3 w4 w5)
      (Entails.of_eq (by ac_rfl))

/-! ## Branch 2 helper: `PreKeyRecord::deserialize` returned `Err` (`+152` .. `+232` -> `+348`) -/

theorem step_dec_err_152 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat} {x : PkPollGhost} {s0 s : State} {P : SepProp}
    (hDeallocCells : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pkGetPollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"
          "__rustc::__rust_dealloc"))
      ((deallocBufCellsSpec A calleeStk).inImage img))
    (e : SignalProtocolError) (bytes : List (BitVec 8))
    (w1 w2 nCap nPtr nLen d0 d1 d2 d3 d4 d5 d6 u0 u1 u2 u3 k0 k1 : BitVec 64)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr pkGetPollName + bv% (152))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hal0 : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = d4)
    (hx22 : s.readReg64 .x22 = nPtr)
    (hx23 : s.readReg64 .x23 = w1)
    (hx24 : s.readReg64 .x24 = w2)
    (hx25 : s.readReg64 .x25 = d1)
    (hx27 : s.readReg64 .x27 = d3)
    (hx28 : s.readReg64 .x28 = d2)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hd0_tag : d0 = errTag)
    (hAns : PkAns.decodeErr e =
      pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)))
    (hP : P ⊢
      pkBoxKeep x s0 ∗ pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6 ∗
        (w2 ↦ₛ bytes) ∗ vecU8BufRest A w1 w2 bytes ∗
        (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A nCap nPtr (keyName x.id) ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
        ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
        ((s0.sp - 224#64) ↦₆₄ d5) ∗ ((s0.sp - 216#64) ↦₆₄ d6) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ d0) ∗ ((s0.sp - 144#64) ↦₆₄ d1) ∗
        ((s0.sp - 136#64) ↦₆₄ d2) ∗ ((s0.sp - 128#64) ↦₆₄ d3) ∗
        ((s0.sp - 120#64) ↦₆₄ d4) ∗ ((s0.sp - 112#64) ↦₆₄ d5) ∗ ((s0.sp - 104#64) ↦₆₄ d6)) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s P
      (pkEpiloguePost rd pathOk A calleeStk x s0) := by
  refine SepWP.weaken_pre hP ?_; clear hP
  have hal : s.spAligned = true := sp_sub_256_spAligned hal0 hsp
  have hfn : libsignalSessionCode.fnOff pkGetPollName =
      num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") :=
    pkGetPoll_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode cliPkGetPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"))
    152 84
  dsimp only [tripleRatchetProgAtExt] at hDeallocCells hpc ⊢
  clear hfn
  generalize hfn_eq : (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr pkGetPollName = fnBase at *
  suffices hjoin180 : ∀ (s1 : State) (P1 : SepProp),
      ImgCallInv img s1 →
      s1.pc = fnBase + bv% (180) →
      s1.status = .Running →
      s1.sp = s0.sp - 256#64 →
      s1.trace = s0.trace →
      s1.readReg64 .x19 = x.fut →
      s1.readReg64 .x20 = x.out →
      s1.readReg64 .x21 = d4 →
      s1.readReg64 .x22 = nPtr →
      s1.readReg64 .x25 = d1 →
      s1.readReg64 .x27 = d3 →
      s1.readReg64 .x28 = d2 →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (P1 ⊢ pkBoxKeep x s0 ∗ pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6 ∗
        (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A nCap nPtr (keyName x.id) ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ d5) ∗ ((s0.sp - 248#64) ↦₆₄ d6) ∗
        ((s0.sp - 240#64) ↦₆₄ d5) ∗ ((s0.sp - 232#64) ↦₆₄ d6) ∗
        ((s0.sp - 224#64) ↦₆₄ d5) ∗ ((s0.sp - 216#64) ↦₆₄ d6) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ d0) ∗ ((s0.sp - 144#64) ↦₆₄ d1) ∗
        ((s0.sp - 136#64) ↦₆₄ d2) ∗ ((s0.sp - 128#64) ↦₆₄ d3) ∗
        ((s0.sp - 120#64) ↦₆₄ d4) ∗ ((s0.sp - 112#64) ↦₆₄ d5) ∗ ((s0.sp - 104#64) ↦₆₄ d6)) →
      SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
        (s0.readReg64 Reg.lr) s1 P1 (pkEpiloguePost rd pathOk A calleeStk x s0) by
    by_cases hw1 : w1 = 0#64
    · subst hw1
      refine bytes_zero_elim (ptr := w2) (bs := bytes)
        (Rest := pkBoxKeep x s0 ∗ pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6 ∗
          (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A nCap nPtr (keyName x.id) ∗
          dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
          ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
          ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
          ((s0.sp - 224#64) ↦₆₄ d5) ∗ ((s0.sp - 216#64) ↦₆₄ d6) ∗
          ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
          ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
          ((s0.sp - 152#64) ↦₆₄ d0) ∗ ((s0.sp - 144#64) ↦₆₄ d1) ∗
          ((s0.sp - 136#64) ↦₆₄ d2) ∗ ((s0.sp - 128#64) ↦₆₄ d3) ∗
          ((s0.sp - 120#64) ↦₆₄ d4) ∗ ((s0.sp - 112#64) ↦₆₄ d5) ∗ ((s0.sp - 104#64) ↦₆₄ d6))
        (by ac_rfl) ?_
      apply SepWP.seq_inImage (mid := fnBase + bv% (180)) hinv
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
      intro hinv1
      apply bind_sepWP_state; intro s1
      exact hjoin180 s1 _ hinv1
        (by simp only [s1, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (Entails.of_eq (by ac_rfl))
    · have hw1_eq : (w1 == 0#64) = false := beq_eq_false_iff_ne.mpr hw1
      have hw1_ne : (w1 != 0#64) = true := bne_iff_ne.mpr hw1
      apply SepWP.seq_inImage
        (mid := fnBase + bv% (ls_rel%
          "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"
          "__rustc::__rust_dealloc"))
        hinv
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
      intro hinv1
      wp_call_inImage hDeallocCells hinv1 (w2, w1, bytes, s0.sp - 256#64)
      exact hjoin180 sf _ hinv_sf
        (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (Entails.of_eq (by ac_rfl))
  clear hinv hpc hrun hsp hal htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 hvregs s
  intro s1 P1 hinv1 hpc1 hrun1 hsp1 htr1 h19_1 h20_1 h21_1 h22_1 h25_1 h27_1 h28_1 hv1 hP1
  refine SepWP.weaken_pre hP1 ?_; clear hP1
  have hal1 : s1.spAligned = true := sp_sub_256_spAligned hal0 hsp1
  by_cases hnCap : nCap = 0#64
  · subst hnCap
    refine bytes_zero_elim (ptr := nPtr) (bs := keyName x.id)
      (Rest := pkBoxKeep x s0 ∗ pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6 ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ d5) ∗ ((s0.sp - 248#64) ↦₆₄ d6) ∗
        ((s0.sp - 240#64) ↦₆₄ d5) ∗ ((s0.sp - 232#64) ↦₆₄ d6) ∗
        ((s0.sp - 224#64) ↦₆₄ d5) ∗ ((s0.sp - 216#64) ↦₆₄ d6) ∗
        ((s0.sp - 200#64) ↦₆₄ 0#64) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ d0) ∗ ((s0.sp - 144#64) ↦₆₄ d1) ∗
        ((s0.sp - 136#64) ↦₆₄ d2) ∗ ((s0.sp - 128#64) ↦₆₄ d3) ∗
        ((s0.sp - 120#64) ↦₆₄ d4) ∗ ((s0.sp - 112#64) ↦₆₄ d5) ∗ ((s0.sp - 104#64) ↦₆₄ d6))
      (by ac_rfl) ?_
    wp_steps
    apply bind_sepWP_state; intro s_ep
    have hpc_ep : s_ep.pc = fnBase + bv% (348) := by
      simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega
    have hx26_ep : s_ep.readReg64 .x26 = d0 := by
      rw [hd0_tag]; simp only [s_ep, wp_norm, arm64_norm, *]; rfl
    subst hfn_eq
    exact step_epilogue_348 (.decodeErr e) d0 d1 d2 d3 d4 d5 d6
      d5 d6 d5 d6 0#64 nPtr nLen k0 k1 d0 d1 d2 d3 d4 d5 d6
      (pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6)
      hpc_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hal0
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hx26_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      ⟨hAns, by simp only [s_ep, wp_norm, arm64_norm, *]⟩
      (decodeErr_reassemble A x.out e d0 d1 d2 d3 d4 d5 d6)
      (Entails.of_eq (by ac_rfl))
  · have hnCap_eq : (nCap == 0#64) = false := beq_eq_false_iff_ne.mpr hnCap
    have hnCap_ne : (nCap != 0#64) = true := bne_iff_ne.mpr hnCap
    apply SepWP.seq_inImage
      (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"
        "__rustc::__rust_dealloc"))
      hinv1
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hinv2
    wp_call_inImage hDeallocCells hinv2 (nPtr, nCap, keyName x.id, s0.sp - 256#64)
    wp_steps
    apply bind_sepWP_state; intro s_ep
    have hpc_ep : s_ep.pc = fnBase + bv% (348) := by
      simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega
    have hx26_ep : s_ep.readReg64 .x26 = d0 := by
      rw [hd0_tag]; simp only [s_ep, wp_norm, arm64_norm, *]; rfl
    subst hfn_eq
    exact step_epilogue_348 (.decodeErr e) d0 d1 d2 d3 d4 d5 d6
      d5 d6 d5 d6 nCap nPtr nLen k0 k1 d0 d1 d2 d3 d4 d5 d6
      (pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6)
      hpc_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hal0
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hx26_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      ⟨hAns, by simp only [s_ep, wp_norm, arm64_norm, *]⟩
      (decodeErr_reassemble A x.out e d0 d1 d2 d3 d4 d5 d6)
      (Entails.of_eq (by ac_rfl))

/-! ## Branch 3/4 helper: `.missing` (`+236 -> +240`) and `.found rec` (`+240` .. `+344` -> `+348`) -/

theorem step_ok_240 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat} {x : PkPollGhost} {s0 s : State} {P : SepProp}
    (hDeallocCells : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pkGetPollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"
          "__rustc::__rust_dealloc"))
      ((deallocBufCellsSpec A calleeStk).inImage img))
    (hDropCells : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pkGetPollName -
        bv% (ls_rel%
          "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]"
          "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"))
      ((dropSpeWordCellsSpec A calleeStk).inImage img))
    (ans : PkAns PreKeyRecord) (bytes : List (BitVec 8))
    (w1 w2 nCap nPtr nLen r26 r25 r28 r27 r21 qlo qhi u0 u1 u2 u3 k0 k1
      g0 g1 g2 g3 g4 g5 g6 : BitVec 64)
    (payload : SepProp)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr pkGetPollName + bv% (240))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hal0 : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = r21)
    (hx22 : s.readReg64 .x22 = nPtr)
    (hx23 : s.readReg64 .x23 = w1)
    (hx24 : s.readReg64 .x24 = w2)
    (hx25 : s.readReg64 .x25 = r25)
    (hx26 : s.readReg64 .x26 = r26)
    (hx27 : s.readReg64 .x27 = r27)
    (hx28 : s.readReg64 .x28 = r28)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hAns : ans = pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)))
    (hMode :
      (ans = .missing ∧ r26 = errTag ∧ payload = emp) ∨
      (∃ rec : PreKeyRecord, ans = .found rec ∧ r26 + 1#64 ≠ 0#64 ∧
        payload = pkDecPayload A (.ok rec) r26 r25 r28 r27 r21 qlo qhi))
    (hP : P ⊢
      pkBoxKeep x s0 ∗ payload ∗
        (w2 ↦ₛ bytes) ∗ vecU8BufRest A w1 w2 bytes ∗
        (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A nCap nPtr (keyName x.id) ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
        ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
        ((s0.sp - 224#64) ↦₆₄ qlo) ∗ ((s0.sp - 216#64) ↦₆₄ qhi) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
        ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
        ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6)) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s P
      (pkEpiloguePost rd pathOk A calleeStk x s0) := by
  refine SepWP.weaken_pre hP ?_; clear hP
  have hal : s.spAligned = true := sp_sub_256_spAligned hal0 hsp
  have hfn : libsignalSessionCode.fnOff pkGetPollName =
      num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") :=
    pkGetPoll_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode cliPkGetPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"))
    240 108
  dsimp only [tripleRatchetProgAtExt] at hDeallocCells hDropCells hpc ⊢
  clear hfn
  generalize hfn_eq : (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr pkGetPollName = fnBase at *
  suffices hjoin272 : ∀ (s1 : State) (P1 : SepProp),
      ImgCallInv img s1 →
      s1.pc = fnBase + bv% (272) →
      s1.status = .Running →
      s1.sp = s0.sp - 256#64 →
      s1.trace = s0.trace →
      s1.readReg64 .x19 = x.fut →
      s1.readReg64 .x20 = x.out →
      s1.readReg64 .x21 = r21 →
      s1.readReg64 .x22 = nPtr →
      s1.readReg64 .x25 = r25 →
      s1.readReg64 .x26 = r26 →
      s1.readReg64 .x27 = r27 →
      s1.readReg64 .x28 = r28 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (P1 ⊢ pkBoxKeep x s0 ∗ payload ∗
        (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A nCap nPtr (keyName x.id) ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
        ((s0.sp - 240#64) ↦₆₄ qlo) ∗ ((s0.sp - 232#64) ↦₆₄ qhi) ∗
        ((s0.sp - 224#64) ↦₆₄ qlo) ∗ ((s0.sp - 216#64) ↦₆₄ qhi) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ qlo) ∗ ((s0.sp - 168#64) ↦₆₄ qhi) ∗
        ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
        ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
        ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6)) →
      SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
        (s0.readReg64 Reg.lr) s1 P1 (pkEpiloguePost rd pathOk A calleeStk x s0) by
    by_cases hw1 : w1 = 0#64
    · subst hw1
      refine bytes_zero_elim (ptr := w2) (bs := bytes)
        (Rest := pkBoxKeep x s0 ∗ payload ∗
          (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A nCap nPtr (keyName x.id) ∗
          dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
          ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
          ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
          ((s0.sp - 224#64) ↦₆₄ qlo) ∗ ((s0.sp - 216#64) ↦₆₄ qhi) ∗
          ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
          ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
          ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
          ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
          ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6))
        (by ac_rfl) ?_
      apply SepWP.seq_inImage (mid := fnBase + bv% (272)) hinv
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
      intro hinv1
      apply bind_sepWP_state; intro s1
      exact hjoin272 s1 _ hinv1
        (by simp only [s1, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (Entails.of_eq (by ac_rfl))
    · have hw1_eq : (w1 == 0#64) = false := beq_eq_false_iff_ne.mpr hw1
      have hw1_ne : (w1 != 0#64) = true := bne_iff_ne.mpr hw1
      apply SepWP.seq_inImage
        (mid := fnBase + bv% (ls_rel%
          "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"
          "__rustc::__rust_dealloc"))
        hinv
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
      intro hinv1
      wp_call_inImage hDeallocCells hinv1 (w2, w1, bytes, s0.sp - 256#64)
      exact hjoin272 sf _ hinv_sf
        (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (Entails.of_eq (by ac_rfl))
  clear hinv hpc hrun hsp hal htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs s
  intro s1 P1 hinv1 hpc1 hrun1 hsp1 htr1 h19_1 h20_1 h21_1 h22_1 h25_1 h26_1 h27_1 h28_1 h29_1 hv1 hP1
  refine SepWP.weaken_pre hP1 ?_; clear hP1
  have hal1 : s1.spAligned = true := sp_sub_256_spAligned hal0 hsp1
  suffices hjoin292 : ∀ (s2 : State) (P2 : SepProp),
      ImgCallInv img s2 →
      s2.pc = fnBase + bv% (292) →
      s2.status = .Running →
      s2.sp = s0.sp - 256#64 →
      s2.trace = s0.trace →
      s2.readReg64 .x19 = x.fut →
      s2.readReg64 .x20 = x.out →
      s2.readReg64 .x21 = r21 →
      s2.readReg64 .x25 = r25 →
      s2.readReg64 .x26 = r26 →
      s2.readReg64 .x27 = r27 →
      s2.readReg64 .x28 = r28 →
      s2.readReg64 .x29 = s0.sp - 96#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      (P2 ⊢ pkBoxKeep x s0 ∗ payload ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
        ((s0.sp - 240#64) ↦₆₄ qlo) ∗ ((s0.sp - 232#64) ↦₆₄ qhi) ∗
        ((s0.sp - 224#64) ↦₆₄ qlo) ∗ ((s0.sp - 216#64) ↦₆₄ qhi) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ qlo) ∗ ((s0.sp - 168#64) ↦₆₄ qhi) ∗
        ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
        ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
        ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6)) →
      SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
        (s0.readReg64 Reg.lr) s2 P2 (pkEpiloguePost rd pathOk A calleeStk x s0) by
    by_cases hnCap : nCap = 0#64
    · subst hnCap
      refine bytes_zero_elim (ptr := nPtr) (bs := keyName x.id)
        (Rest := pkBoxKeep x s0 ∗ payload ∗
          dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
          ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
          ((s0.sp - 240#64) ↦₆₄ qlo) ∗ ((s0.sp - 232#64) ↦₆₄ qhi) ∗
          ((s0.sp - 224#64) ↦₆₄ qlo) ∗ ((s0.sp - 216#64) ↦₆₄ qhi) ∗
          ((s0.sp - 200#64) ↦₆₄ 0#64) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
          ((s0.sp - 176#64) ↦₆₄ qlo) ∗ ((s0.sp - 168#64) ↦₆₄ qhi) ∗
          ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
          ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
          ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6))
        (by ac_rfl) ?_
      apply SepWP.seq_inImage (mid := fnBase + bv% (292)) hinv1
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
      intro hinv2
      apply bind_sepWP_state; intro s2
      exact hjoin292 s2 _ hinv2
        (by simp only [s2, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (Entails.of_eq (by ac_rfl))
    · have hnCap_eq : (nCap == 0#64) = false := beq_eq_false_iff_ne.mpr hnCap
      have hnCap_ne : (nCap != 0#64) = true := bne_iff_ne.mpr hnCap
      apply SepWP.seq_inImage
        (mid := fnBase + bv% (ls_rel%
          "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"
          "__rustc::__rust_dealloc"))
        hinv1
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
      intro hinv2
      wp_call_inImage hDeallocCells hinv2 (nPtr, nCap, keyName x.id, s0.sp - 256#64)
      exact hjoin292 sf _ hinv_sf
        (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (Entails.of_eq (by ac_rfl))
  clear hinv1 hpc1 hrun1 hsp1 hal1 htr1 h19_1 h20_1 h21_1 h22_1 h25_1 h26_1 h27_1 h28_1 h29_1 hv1 s1
  intro s2 P2 hinv2 hpc2 hrun2 hsp2 htr2 h19_2 h20_2 h21_2 h25_2 h26_2 h27_2 h28_2 h29_2 hv2 hP2
  refine SepWP.weaken_pre hP2 ?_; clear hP2
  have hal2 : s2.spAligned = true := sp_sub_256_spAligned hal0 hsp2
  rcases hMode with ⟨rfl, rfl, rfl⟩ | ⟨rec, rfl, hd0, rfl⟩
  · wp_steps
    apply bind_sepWP_state; intro s_ep
    have hpc_ep : s_ep.pc = fnBase + bv% (348) := by
      simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega
    subst hfn_eq
    exact step_epilogue_348 .missing errTag (speWord 13) r28 r27 r21 u0 u1
      qlo qhi qlo qhi nCap nPtr nLen qlo qhi (speWord 13) g1 g2 g3 g4 g5 g6
      emp
      hpc_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hal0
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *]; rfl)
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      ⟨hAns, by simp only [s_ep, wp_norm, arm64_norm, *]⟩
      (by rw [sepConj_emp]; exact missing_reassemble A x.out r28 r27 r21 u0 u1)
      (Entails.of_eq (by ac_rfl))
  · have hd0_eq : (r26 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hd0
    have hd0_ne : (r26 + 1#64 != 0#64) = true := bne_iff_ne.mpr hd0
    apply SepWP.seq_inImage
      (mid := fnBase - bv% (ls_rel%
        "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]"
        "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"))
      hinv2
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
    intro hinv3
    have hspe13 : (0x800000000000000d#64 : BitVec 64) = speWord 13 := rfl
    rw [hspe13]
    wp_call_inImage hDropCells hinv3 (s0.sp - 152#64, g1, g2, g3, g4, g5, s0.sp - 256#64)
    wp_steps
    apply bind_sepWP_state; intro s_ep
    have hpc_ep : s_ep.pc = fnBase + bv% (348) := by
      simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega
    subst hfn_eq
    exact step_epilogue_348 (.found rec) r26 r25 r28 r27 r21 qlo qhi
      qlo qhi qlo qhi nCap nPtr nLen qlo qhi w w_1 w_2 w_3 w_4 w_5 g6
      (pkDecPayload A (.ok rec) r26 r25 r28 r27 r21 qlo qhi)
      hpc_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hal0
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      ⟨hAns, by simp only [s_ep, wp_norm, arm64_norm, *]⟩
      (found_reassemble A x.out rec r26 r25 r28 r27 r21 qlo qhi)
      (Entails.of_eq (by ac_rfl))

end CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers
