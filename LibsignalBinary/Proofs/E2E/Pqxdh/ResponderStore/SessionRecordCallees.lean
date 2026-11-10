/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.Fetch
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WPp

/-!
# `SessionRecord`, `drop_glue`, and Log Closure Callees

Proves fast-path `subroutine_ok` contracts on `tripleRatchetProgAt` and under `[LibsignalPlacement]`
for `SessionRecord::archive_current_state_inner` (`0x17f84`), `promote_state` (`0x17490`),
`promote_matching_session` (`0x17970`), `Map::next` (`0x251b0`),
`drop_glue::<process_prekey_impl::{closure#0}>` (`0x70ab0`), and
`try_decrypt_from_record::<PqxdhRng>::{closure#0}` (`0x757c8`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.ResponderStore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "cells_unfold_fast" : tactic =>
  `(tactic| simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub])

/-! ## `SessionRecord::archive_current_state_inner` (`0x17f84`) -/

abbrev archiveCurrentStateInnerName : String :=
  "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"

def archiveCurrentStateInnerEmptySpec : Spec (BitVec 64) where
  pre := fun recPtr s =>
    ⌜s.readReg64 .x0 = recPtr⌝ ∗
    ((recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    cells (s.sp - 64#64) 8
  post := fun recPtr s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
    ((recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    cells (s0.sp - 64#64) 8

theorem archive_current_state_inner_empty_ok_trap {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr archiveCurrentStateInnerName)
      archiveCurrentStateInnerEmptySpec := by
  unfold archiveCurrentStateInnerEmptySpec
  cells_unfold
  have hfn : libsignalSessionCode.fnOff archiveCurrentStateInnerName = 0x17f84 :=
    libsignalSessionCode_fnOff_0x17f84
  responder_fetches_from b (Rust.withPanics (trTrapExterns C abs)) hfn 0x17f84 0 412
  wp_init recPtr s0
  examples_generalize_entry
  examples_hide_fetches
  subst h
  wp_steps
  wp_done

theorem archive_current_state_inner_empty_ok {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr archiveCurrentStateInnerName)
      archiveCurrentStateInnerEmptySpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr archiveCurrentStateInnerName]
  exact subroutine_ok_kit_of_trTrap archive_current_state_inner_empty_ok_trap

/-! ## `SessionRecord::promote_state` (`0x17490`) -/

abbrev promoteStateName : String :=
  "<libsignal_protocol::state::session::SessionRecord>::promote_state"

theorem pointsTo64_memRegion_336_entails_344 (recPtr val : BitVec 64) :
    ((recPtr + 0x18#64) ↦₆₄ val) ∗ memRegion (recPtr + 0x20#64) 336 ⊢
      memRegion (recPtr + 0x18#64) 344 := by
  rw [show (344 : Nat) = 8 + 336 by decide,
    memRegion_split (recPtr + 0x18#64) 8 336 (by decide),
    show recPtr + 0x18#64 + 8#64 = recPtr + 0x20#64 by bv_arith,
    ProofLib.memRegion_eight (recPtr + 0x18#64)]
  exact sepConj_mono_left (Entails.sepExists_intro val)

private theorem cells_sub32_4_merge (sp v0 v1 v2 v3 : BitVec 64) :
    ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
    ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      cells (sp - 32#64) 4 := by
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
        ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) := by
    cells_unfold
  rw [hc4]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.sepExists_right v3 (Entails.refl _))))

def promoteStateEmptySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (recPtr, srcPtr, bs) s =>
    ⌜s.readReg64 .x0 = recPtr ∧ s.readReg64 .x1 = srcPtr ∧ bs.length = 344⌝ ∗
    ((recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    memRegion (recPtr + 0x20#64) 336 ∗
    (srcPtr ↦ₛ bs) ∗
    cells (s.sp - 96#64) 8 ∗
    cells (s.sp - 32#64) 4
  post := fun (recPtr, srcPtr, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    ((recPtr + 0x18#64) ↦ₛ bs) ∗
    (srcPtr ↦ₛ bs) ∗
    cells (s0.sp - 96#64) 8 ∗
    cells (s0.sp - 32#64) 4

theorem promote_state_empty_ok_trap {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr promoteStateName)
      promoteStateEmptySpec := by
  unfold promoteStateEmptySpec
  have hfn : libsignalSessionCode.fnOff promoteStateName = 0x17490 :=
    libsignalSessionCode_fnOff_0x17490
  have harch := archive_current_state_inner_empty_ok_trap (b := b) (C := C)
    (abs := abs)
  have hrel : (trTrapProgAt b C abs).fnAddr archiveCurrentStateInnerName =
      (trTrapProgAt b C abs).fnAddr promoteStateName + 2804#64 := by
    simp only [trTrapProgAt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x17f84,
      libsignalSessionCode_fnOff_0x17490, BitVec.add_assoc]
    rfl
  rw [hrel] at harch
  clear hrel
  have hmemcpy := framelessMemcpy_ok_at_trap (b := b) (C := C) (abs := abs)
    (name := promoteStateName) (k := num% (ls_off% "memcpy" - 0x17490))
  responder_fetches_from b (Rust.withPanics (trTrapExterns C abs)) hfn 0x17490 0 68
  wp_init x s0
  dsimp only [trTrapProgAt] at harch hmemcpy ⊢
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨recPtr, srcPtr, bs⟩ := x
  dsimp only at *
  subst h_1 h_2
  have hc4 : cells (s0.sp - 32#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((s0.sp - 32#64) ↦₆₄ v0) ∗ ((s0.sp - 24#64) ↦₆₄ v1) ∗
        ((s0.sp - 16#64) ↦₆₄ v2) ∗ ((s0.sp - 8#64) ↦₆₄ v3)) := by
    cells_unfold
  rw [hc4]
  simp only [sepExists_sepConj_right]
  wp_pull_exists
  wp_steps
  have hsp_sub : s0.sp - 32#64 - 64#64 = s0.sp - 96#64 := by bv_arith
  wp_call harch (s0.readReg64 (.gpr 0#5))
  wp_steps
  apply SepWP.replace_pre (by sep_focus)
    (pointsTo64_memRegion_336_entails_344 (s0.readReg64 (.gpr 0#5)) 0xffffffffffffffff#64)
  apply SepWP.replace_pre (by sep_focus)
    (cells_sub32_4_merge s0.sp _ _ _ _)
  rw [← h]
  wp_call hmemcpy (s0.readReg64 (.gpr 0#5) + 0x18#64, s0.readReg64 (.gpr 1#5), bs)
  simp only [h] at *
  wp_done

theorem promote_state_empty_ok {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr promoteStateName)
      promoteStateEmptySpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr promoteStateName]
  exact subroutine_ok_kit_of_trTrap promote_state_empty_ok_trap

/-! ## `Map::next` (`0x251b0`) -/

abbrev mapIterNextName : String :=
  "<core::iter::adapters::map::Map<core::slice::iter::Iter<alloc::vec::Vec<u8>>, " ++
  "<libsignal_protocol::state::session::SessionRecord>::" ++
  "previous_session_states::{closure#0}> as core::iter::traits::iterator::Iterator>::next"

private theorem mapIterNextName_fnOff : libsignalSessionCode.fnOff mapIterNextName = 0x25264 :=
  libsignalSessionCode_fnOff_0x25264

def mapIterNextEmptySpec : Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (outPtr, iterPtr, slicePtr) s =>
    ⌜s.readReg64 .x0 = outPtr ∧ s.readReg64 .x1 = iterPtr⌝ ∗
    (iterPtr ↦₆₄ slicePtr) ∗ ((iterPtr + 8#64) ↦₆₄ slicePtr) ∗
    (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
    cells (s.sp - 64#64) 8
  post := fun (outPtr, iterPtr, slicePtr) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (iterPtr ↦₆₄ slicePtr) ∗ ((iterPtr + 8#64) ↦₆₄ slicePtr) ∗
    (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
    cells (s0.sp - 64#64) 8

theorem map_iter_next_empty_ok_trap {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr mapIterNextName)
      mapIterNextEmptySpec := by
  unfold mapIterNextEmptySpec
  cells_unfold
  have hfn : libsignalSessionCode.fnOff mapIterNextName = 0x25264 :=
    libsignalSessionCode_fnOff_0x25264
  responder_fetches_from b (Rust.withPanics (trTrapExterns C abs)) hfn 0x25264 0 568
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨outPtr, iterPtr, slicePtr⟩ := x
  dsimp only at *
  subst h h_1
  wp_pull_exists
  wp_steps
  wp_done

theorem map_iter_next_empty_ok {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr mapIterNextName)
      mapIterNextEmptySpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr mapIterNextName]
  exact subroutine_ok_kit_of_trTrap map_iter_next_empty_ok_trap

/-! ## `SessionRecord::promote_matching_session` (`0x17970`) -/

abbrev promoteMatchingSessionName : String :=
  "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session"

def sessionRecordEmptyHeaderAt (recPtr : BitVec 64) : SepProp :=
  (recPtr ↦₆₄ 0#64) ∗
  ((recPtr + 8#64) ↦₆₄ 8#64) ∗
  ((recPtr + 16#64) ↦₆₄ 0#64) ∗
  ((recPtr + 24#64) ↦₆₄ 0xffffffffffffffff#64)

def promoteMatchingSessionEmptySpec : Spec (BitVec 64 × BitVec 64) where
  pre := fun (recPtr, outPtr) s =>
    ⌜s.readReg64 .x0 = recPtr ∧ s.readReg64 .x8 = outPtr⌝ ∗
    sessionRecordEmptyHeaderAt recPtr ∗
    (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
    (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
    cells (s.sp - 1248#64) 8 ∗
    cells (s.sp - 1184#64) 10 ∗
    (∃∗ w2e0 : BitVec 64, (s.sp - 448#64) ↦₆₄ w2e0) ∗
    cells (s.sp - 96#64) 12
  post := fun (recPtr, outPtr) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    sessionRecordEmptyHeaderAt recPtr ∗
    (outPtr ↦₆₄ 0#64) ∗
    ((outPtr + 8#64) ↦₈ 0#8) ∗
    cells (s0.sp - 1248#64) 8 ∗
    cells (s0.sp - 1184#64) 10 ∗
    (∃∗ w2e0 : BitVec 64, (s0.sp - 448#64) ↦₆₄ w2e0) ∗
    cells (s0.sp - 96#64) 12

theorem promote_matching_session_empty_ok_trap {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr promoteMatchingSessionName)
      promoteMatchingSessionEmptySpec := by
  unfold promoteMatchingSessionEmptySpec sessionRecordEmptyHeaderAt
  cells_unfold_fast
  have hfn : libsignalSessionCode.fnOff promoteMatchingSessionName = 0x17970 :=
    libsignalSessionCode_fnOff_0x17970
  have hiter := map_iter_next_empty_ok_trap (b := b) (C := C) (abs := abs)
  have hrel : (trTrapProgAt b C abs).fnAddr mapIterNextName =
      (trTrapProgAt b C abs).fnAddr promoteMatchingSessionName + 55540#64 := by
    simp only [trTrapProgAt, Program.fnAddr_rebase, mapIterNextName_fnOff,
      libsignalSessionCode_fnOff_0x17970, BitVec.add_assoc]
    rfl
  rw [hrel] at hiter
  clear hrel
  simp only [mapIterNextEmptySpec, cells, sepExists_sepConj_right,
    sepConj_emp] at hiter
  responder_fetches_from b (Rust.withPanics (trTrapExterns C abs)) hfn 0x17970 0 804
  wp_init x s0
  dsimp only [trTrapProgAt] at hiter ⊢
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨recPtr, outPtr⟩ := x
  dsimp only at *
  subst h h_1
  wp_pull_exists
  wp_steps
  wp_call hiter (s0.sp - 448#64, s0.sp - 1128#64, 8#64)
  wp_steps
  wp_done

theorem promote_matching_session_empty_ok {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr promoteMatchingSessionName)
      promoteMatchingSessionEmptySpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr promoteMatchingSessionName]
  exact subroutine_ok_kit_of_trTrap promote_matching_session_empty_ok_trap

/-! ## `drop_glue::<process_prekey_impl::{closure#0}>` (`0x70ab0`) -/

abbrev dropProcessPrekeyImplName : String :=
  "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}> [local#1]"

@[local simp, wp_norm, arm64_norm]
private theorem cond_le_subs_1_4_true :
    ConditionHolds CondCode.LE (subsPState32 1#32 4#32) = true := by
  simp only [ConditionHolds, subsPState32]; decide

@[local simp, wp_norm, arm64_norm]
private theorem cond_eq_subs_1_3_false :
    ConditionHolds CondCode.EQ (subsPState32 1#32 3#32) = false := by
  simp only [ConditionHolds, subsPState32]; decide

@[local simp, wp_norm, arm64_norm]
private theorem cond_ne_subs_1_4_true :
    ConditionHolds CondCode.NE (subsPState32 1#32 4#32) = true := by
  simp only [ConditionHolds, subsPState32]; decide

def dropProcessPrekeyImplState1Spec : Spec (BitVec 64) where
  pre := fun ptr s =>
    ⌜s.readReg64 .x0 = ptr⌝ ∗
    ((ptr + 0x15a#64) ↦₈ 1#8) ∗
    cells (s.sp - 48#64) 6
  post := fun ptr s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    ((ptr + 0x15a#64) ↦₈ 1#8) ∗
    cells (s0.sp - 48#64) 6

/-! ## `try_decrypt_from_record::<PqxdhRng>::{closure#0}` (`0x757c8`) -/

abbrev pqxdhLogClosureName : String :=
  "libsignal_protocol::session_management::" ++
  "try_decrypt_from_record::<libsignal_pqxdh_e2e::PqxdhRng>::{closure#0}"

abbrev pqxdhClosureStack : Nat := 432

private theorem stackAt_pqxdhClosure (sp : BitVec 64) :
    stackAt sp pqxdhClosureStack =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 432#64) ↦₆₄ v0) ∗ ((sp - 424#64) ↦₆₄ v1) ∗
        ((sp - 416#64) ↦₆₄ v2) ∗ ((sp - 408#64) ↦₆₄ v3)) ∗
      stackAt (sp - 96#64) 304 ∗
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
       ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗ ((sp - 80#64) ↦₆₄ w2) ∗
        ((sp - 72#64) ↦₆₄ w3) ∗ ((sp - 64#64) ↦₆₄ w4) ∗ ((sp - 56#64) ↦₆₄ w5) ∗
        ((sp - 48#64) ↦₆₄ w6) ∗ ((sp - 40#64) ↦₆₄ w7) ∗ ((sp - 32#64) ↦₆₄ w8) ∗
        ((sp - 24#64) ↦₆₄ w9) ∗ ((sp - 16#64) ↦₆₄ w10) ∗ ((sp - 8#64) ↦₆₄ w11)) := by
  have h1 := ProofLib.stackAt_split_cells sp 336 12 (by decide)
  have h2 := stackAt_split_bottom (sp - 96#64) 304 32 (by decide)
  have hsub : (sp - 96#64) - BitVec.ofNat 64 (304 + 32) = sp - 432#64 := by
    rw [BitVec.sub_sub]; rfl
  rw [hsub, show (32 : Nat) = 8 * 4 by rfl,
      ProofLib.memRegion_cells (sp - 432#64) 4 (by decide)] at h2
  change stackAt sp pqxdhClosureStack = stackAt (sp - 96#64) 336 ∗ cells (sp - 96#64) 12 at h1
  have hc4 : cells (sp - 432#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 432#64) ↦₆₄ v0) ∗ ((sp - 424#64) ↦₆₄ v1) ∗
        ((sp - 416#64) ↦₆₄ v2) ∗ ((sp - 408#64) ↦₆₄ v3)) := by
    cells_unfold
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
       ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗ ((sp - 80#64) ↦₆₄ w2) ∗
        ((sp - 72#64) ↦₆₄ w3) ∗ ((sp - 64#64) ↦₆₄ w4) ∗ ((sp - 56#64) ↦₆₄ w5) ∗
        ((sp - 48#64) ↦₆₄ w6) ∗ ((sp - 40#64) ↦₆₄ w7) ∗ ((sp - 32#64) ↦₆₄ w8) ∗
        ((sp - 24#64) ↦₆₄ w9) ∗ ((sp - 16#64) ↦₆₄ w10) ∗ ((sp - 8#64) ↦₆₄ w11)) := by
    cells_unfold
  rw [h1, h2, hc4, hc12, sepConj_assoc]

private theorem pqxdhLogClosure_adrp_addr_eq {base entry : BitVec 64}
    (hb : base &&& 0xfff#64 = 0#64) (he : entry = base + 481224#64) :
    (((entry + 36#64) &&& 18446744073709547520#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - 0x75000)) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) = base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
  subst he; bv_arith

def pqxdhLogClosureSpec (img : Obj.Image) : Spec Unit where
  pre := fun _ s =>
    logOff img ∗ stackAt s.sp pqxdhClosureStack
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      logOff img ∗ stackAt s0.sp pqxdhClosureStack

def PqxdhLogClosureOk_trap (img : Obj.Image) (C : Crypto)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr pqxdhLogClosureName)
    ((pqxdhLogClosureSpec img).inImage img)

def PqxdhLogClosureOk (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr pqxdhLogClosureName)
    ((pqxdhLogClosureSpec img).inImage img)

/-! ## Relocatable `[LibsignalPlacement]` Contracts -/

open ProofLib.GenPlacedFetches

theorem archive_current_state_inner_empty_placed_ok [LibsignalPlacement]
    (H : LibsignalHooks) :
    subroutine_ok ((blkPC_51).rebase (blkPl_51).base H) (blkPl_51).base
      archiveCurrentStateInnerEmptySpec := by
  unfold archiveCurrentStateInnerEmptySpec
  cells_unfold
  wp_init recPtr s0
  subst h
  wp_steps
  wp_done

theorem promote_state_empty_placed_ok [LibsignalPlacement]
    (H : LibsignalHooks) (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_47).rebase (blkPl_47).base H) (blkPl_47).base
      (withLsCodeLoaded lsmpl promoteStateEmptySpec) := by
  unfold promoteStateEmptySpec
  have harch := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_47).rebase (blkPl_47).base H) (entry := lsmpl.base 51)
    (archive_current_state_inner_empty_placed_ok H)
  have hmc : subroutine_ok ((blkPC_47).rebase (blkPl_47).base H)
      (lsρ lsMemcpySym) framelessMemcpySpec :=
    ls_hook_ok_of_mem hmemcpy
  wp_init x s0
  obtain ⟨recPtr, srcPtr, bs⟩ := x
  dsimp only [withLsCodeLoaded] at *
  subst h_2 h_3
  have hc4 : cells (s0.sp - 32#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((s0.sp - 32#64) ↦₆₄ v0) ∗ ((s0.sp - 24#64) ↦₆₄ v1) ∗
        ((s0.sp - 16#64) ↦₆₄ v2) ∗ ((s0.sp - 8#64) ↦₆₄ v3)) := by
    cells_unfold
  rw [hc4]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  wp_pull_exists
  wp_steps_lscl (lsmpl.base 51)
  have hsp_sub : s0.sp - 32#64 - 64#64 = s0.sp - 96#64 := by bv_arith
  wp_call harch (s0.readReg64 (.gpr 0#5))
  wp_steps
  apply SepWP.replace_pre (by sep_focus)
    (pointsTo64_memRegion_336_entails_344 (s0.readReg64 (.gpr 0#5)) 0xffffffffffffffff#64)
  apply SepWP.replace_pre (by sep_focus)
    (cells_sub32_4_merge s0.sp _ _ _ _)
  rw [← h_1]
  wp_call hmc (s0.readReg64 (.gpr 0#5) + 0x18#64, s0.readReg64 (.gpr 1#5), bs)
  simp only [h_1] at *
  wp_done

theorem map_iter_next_empty_placed_ok [LibsignalPlacement]
    (H : LibsignalHooks) :
    subroutine_ok ((blkPC_83).rebase (blkPl_83).base H) (blkPl_83).base
      mapIterNextEmptySpec := by
  unfold mapIterNextEmptySpec
  cells_unfold
  wp_init x s0
  obtain ⟨outPtr, iterPtr, slicePtr⟩ := x
  dsimp only at *
  subst h h_1
  wp_pull_exists
  wp_steps
  wp_done

theorem promote_matching_session_empty_placed_ok [LibsignalPlacement]
    (H : LibsignalHooks) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
      (withLsCodeLoaded lsmpl promoteMatchingSessionEmptySpec) := by
  unfold promoteMatchingSessionEmptySpec sessionRecordEmptyHeaderAt
  cells_unfold_fast
  have hiter := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_50).rebase (blkPl_50).base H) (entry := lsmpl.base 83)
    (map_iter_next_empty_placed_ok H)
  simp only [withLsCl, mapIterNextEmptySpec, cells, sepExists_sepConj_right,
    sepConj_emp] at hiter
  wp_init x s0
  obtain ⟨recPtr, outPtr⟩ := x
  dsimp only [withLsCodeLoaded] at *
  subst h_1 h_2
  wp_pull_exists
  wp_steps_lscl (lsmpl.base 83)
  wp_call hiter (s0.sp - 448#64, s0.sp - 1128#64, 8#64)
  wp_steps
  wp_done

end CryptoVerification.E2E.Pqxdh.ResponderStore
