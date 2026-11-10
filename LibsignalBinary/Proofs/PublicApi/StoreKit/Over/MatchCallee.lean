/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchDefs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.SessionRecordCallees
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Steps
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `SessionRecord::promote_matching_session` Miss Proofs

Proves `promote_matching_session_miss_ok` and `promote_matching_session_record_over_ok` on
`tripleRatchetProgAtExt b ext`, plus `CliExt.blackBoxSpec` and relocatable `[LibsignalPlacement]`
variants across version-mismatch, base-key length-mismatch, and constant-time 33-byte key-mismatch
paths.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.CodeLayout
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.SignalSession
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (promoteSavedRegs)

set_option maxRecDepth 200000

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Extern Lookup & Local Decode Trees -/

private theorem externAt?_black_box_over (b : BitVec 64)
    {ext : String → Option (State → State)}
    (h_bb : ext "subtle::black_box::<u8>" = some blackBoxHook) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName +
        bv% (ls_off% "subtle::black_box::<u8>" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) =
      some blackBoxHook := by
  dsimp only [tripleRatchetProgAtExt, promoteMatchingSessionName]
  have hnp : Rust.isPanicSymbol "subtle::black_box::<u8>" = false := by decide +kernel
  have h_bb' : (Rust.withPanics ext) "subtle::black_box::<u8>" = some blackBoxHook := by
    simp [Rust.withPanics, hnp, h_bb]
  rw [Program.externAt?_fnAddr_add
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
    (k := num% (ls_off% "subtle::black_box::<u8>" -
      ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session"))
    (stub := num% (ls_off% "subtle::black_box::<u8>")) (by decide +kernel) (by decide +kernel),
    (ls_hook% "subtle::black_box::<u8>"), h_bb']

private theorem mapIterNextName_fnOff_over :
    libsignalSessionCode.fnOff mapIterNextName =
      num% (ls_off% "<core::iter::adapters::map::Map<core::slice::iter::Iter<alloc::vec::Vec<u8>>, <libsignal_protocol::state::session::SessionRecord>::previous_session_states::{closure#0}> as core::iter::traits::iterator::Iterator>::next") := by
  simp only [mapIterNextName, String.reduceAppend]
  exact (ls_lemma% fnOff "<core::iter::adapters::map::Map<core::slice::iter::Iter<alloc::vec::Vec<u8>>, <libsignal_protocol::state::session::SessionRecord>::previous_session_states::{closure#0}> as core::iter::traits::iterator::Iterator>::next")

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private gen_decodes libsignalSessionCode_tree overIterBin [
  (ls_off% "<core::iter::adapters::map::Map<core::slice::iter::Iter<alloc::vec::Vec<u8>>, <libsignal_protocol::state::session::SessionRecord>::previous_session_states::{closure#0}> as core::iter::traits::iterator::Iterator>::next") →
    (ls_off% "<core::iter::adapters::map::Map<core::slice::iter::Iter<alloc::vec::Vec<u8>>, <libsignal_protocol::state::session::SessionRecord>::previous_session_states::{closure#0}> as core::iter::traits::iterator::Iterator>::next" + 568)]

private gen_decodes libsignalSessionCode_tree overPromoteBin [
  (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") →
    (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session" + 804)]

local macro "cells_unfold_over" : tactic =>
  `(tactic| simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub])

/-! ## 2. Layout-Independent `Map<Iter<Vec<u8>>, ...>::next` Empty-Slice Proof -/

set_option maxHeartbeats 400000 in
theorem map_iter_next_empty_ok_ext {b : BitVec 64}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr mapIterNextName)
      mapIterNextEmptySpec := by
  unfold mapIterNextEmptySpec; cells_unfold_over; dsimp only [tripleRatchetProgAtExt]
  code_fetches_range CryptoVerification.libsignalSessionCode overIterBin b (Rust.withPanics ext)
    mapIterNextName_fnOff_over (num% (ls_off% "<core::iter::adapters::map::Map<core::slice::iter::Iter<alloc::vec::Vec<u8>>, <libsignal_protocol::state::session::SessionRecord>::previous_session_states::{closure#0}> as core::iter::traits::iterator::Iterator>::next")) 0 40
  code_fetches_range CryptoVerification.libsignalSessionCode overIterBin b (Rust.withPanics ext)
    mapIterNextName_fnOff_over (num% (ls_off% "<core::iter::adapters::map::Map<core::slice::iter::Iter<alloc::vec::Vec<u8>>, <libsignal_protocol::state::session::SessionRecord>::previous_session_states::{closure#0}> as core::iter::traits::iterator::Iterator>::next")) 0x144 32
  wp_init x s0; examples_generalize_entry; examples_hide_fetches
  obtain ⟨outPtr, iterPtr, slicePtr⟩ := x; dsimp only at *; subst h h_1
  wp_pull_exists; wp_steps; wp_done

/-! ## 3. Normalization & `black_box` Stepping Helpers -/

private theorem cond_eq_adds64_one_false_over {c : BitVec 64} (hc : c ≠ 0xffffffffffffffff#64) :
    ConditionHolds CondCode.EQ (addsPState64 c 1#64) = false := by
  rw [conditionHolds_eq_addsPState64, beq_eq_false_iff_ne]; intro heq; apply hc; bv_omega
private theorem cond_ne_subs64_one_over {n : Nat} (hgt : 1 < n) (hlt : n < 2 ^ 64) :
    ConditionHolds CondCode.NE (subsPState64 (BitVec.ofNat 64 n) 1#64) = true := by
  rw [conditionHolds_ne_subsPState64, bne_iff_ne]; intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at hnat; omega
private theorem ofNat64_succ_sub_one_over (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by bv_omega
@[local simp, local wp_norm, local arm64_norm]
private theorem sp_sub_1184_align_over (sp : BitVec 64) :
    ((sp - 1184#64) &&& 15#64) = (sp &&& 15#64) := by bv_robdd
@[local simp, local wp_norm, local arm64_norm]
private theorem sp_sub_96_align_over (sp : BitVec 64) :
    ((sp - 96#64) &&& 15#64) = (sp &&& 15#64) := by bv_robdd
@[local simp, local wp_norm, local arm64_norm]
private theorem sp_add_1088_align_over (sp : BitVec 64) :
    ((sp + 1088#64) &&& 15#64) = (sp &&& 15#64) := by bv_robdd
@[local simp, local wp_norm, local arm64_norm]
private theorem cond_eq_subs32_self_over (v : BitVec 32) :
    ConditionHolds CondCode.EQ (subsPState32 v v) = true := by
  rw [conditionHolds_eq_subsPState32, beq_self_eq_true]
@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ne_subs32_self_over (v : BitVec 32) :
    ConditionHolds CondCode.NE (subsPState32 v v) = false := by
  rw [conditionHolds_ne_subsPState32, bne_self_eq_false]
@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ne_subs64_self_over (v : BitVec 64) :
    ConditionHolds CondCode.NE (subsPState64 v v) = false := by
  rw [conditionHolds_ne_subsPState64, bne_self_eq_false]
@[local simp, local wp_norm, local arm64_norm]
private theorem zext64_setWidth32_byte_over (v : BitVec 8) :
    (v.zeroExtend 64 : BitVec 64).setWidth 32 = v.zeroExtend 32 := by bv_omega
@[local simp, local wp_norm, local arm64_norm]
private theorem zext64_extractLsb32_byte_over (v : BitVec 8) :
    (v.zeroExtend 64 : BitVec 64).extractLsb' 0 32 = v.zeroExtend 32 := by bv_slice
@[local simp, local wp_norm, local arm64_norm]
private theorem csel_ver_setWidth32_over (sessVer : BitVec 32) :
    BitVec.setWidth 32 (if ConditionHolds CondCode.EQ (subsPState32 sessVer 0#32)
      then 2#64 else BitVec.setWidth 64 sessVer) =
    if sessVer = 0#32 then 2#32 else sessVer := by
  rw [conditionHolds_eq_subsPState32]; by_cases h : sessVer = 0#32 <;> simp [h]
@[local simp, local wp_norm, local arm64_norm]
private theorem csel_ver_extractLsb32_over (sessVer : BitVec 32) :
    BitVec.extractLsb' 0 32 (if ConditionHolds CondCode.EQ (subsPState32 sessVer 0#32)
      then 2#64 else BitVec.setWidth 64 sessVer) =
    if sessVer = 0#32 then 2#32 else sessVer := by
  rw [conditionHolds_eq_subsPState32]; by_cases h : sessVer = 0#32
  · subst h; decide
  · simp only [beq_iff_eq, h, ↓reduceIte]; bv_slice
@[local simp, local wp_norm, local arm64_norm]
private theorem byte_bne_zext32_over (a b : BitVec 8) :
    (BitVec.setWidth 32 a != BitVec.setWidth 32 b) = (a != b) := by
  by_cases h : a = b
  · subst h; simp [bne]
  · have h32 : BitVec.setWidth 32 a ≠ BitVec.setWidth 32 b := fun heq => h (by bv_omega)
    rw [bne_iff_ne.mpr h32, bne_iff_ne.mpr h]
@[local simp, local wp_norm, local arm64_norm]
private theorem ite_bne_byte_0_1_over (a b : BitVec 8) :
    (if (a != b) = true then 0#64 else 1#64) = if (a == b) = true then 1#64 else 0#64 := by
  cases h : a == b <;> simp [bne, h]

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth32_ite_1_0_over (c : Bool) :
    BitVec.setWidth 32 (if c = true then 1#64 else 0#64) = if c = true then 1#32 else 0#32 := by
  cases c <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_ite_1_0_over (c : Bool) :
    BitVec.setWidth 8 (if c = true then 1#64 else 0#64) = if c = true then 1#8 else 0#8 := by
  cases c <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth64_ite_1_0_32_over (c : Bool) :
    BitVec.setWidth 64 (if c = true then 1#32 else 0#32) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth64_ite_1_0_8_over (c : Bool) :
    BitVec.setWidth 64 (if c = true then 1#8 else 0#8) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem and64_ite_1_0_over (c1 c2 : Bool) :
    ((if c1 = true then 1#64 else 0#64) &&& (if c2 = true then 1#64 else 0#64)) =
      if (c1 && c2) = true then 1#64 else 0#64 := by cases c1 <;> cases c2 <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem and32_ite_1_0_over (c1 c2 : Bool) :
    ((if c1 = true then 1#32 else 0#32) &&& (if c2 = true then 1#32 else 0#32)) =
      if (c1 && c2) = true then 1#32 else 0#32 := by cases c1 <;> cases c2 <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem and64_mask32_ite_1_0_over (c : Bool) :
    ((if c = true then 1#64 else 0#64) &&& 4294967297#64) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem extractLsb32_ite_1_0_over (c : Bool) :
    BitVec.extractLsb' 0 32 (if c = true then 1#64 else 0#64) = if c = true then 1#32 else 0#32 := by
  cases c <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth32_ite_1_0_8_over (c : Bool) :
    BitVec.setWidth 32 (if c = true then 1#8 else 0#8) = if c = true then 1#32 else 0#32 := by
  cases c <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth32_and64_over (a b : BitVec 64) :
    BitVec.setWidth 32 (a &&& b) = BitVec.setWidth 32 a &&& BitVec.setWidth 32 b := by bv_robdd
@[local simp, local wp_norm, local arm64_norm]
private theorem and32_one_ite_1_0_over (c : Bool) :
    ((if c = true then 1#32 else 0#32) &&& 1#32) = if c = true then 1#32 else 0#32 := by
  cases c <;> rfl
private theorem extractLsb32_eq_setWidth32_over (w : BitVec 64) :
    BitVec.extractLsb' 0 32 w = w.setWidth 32 := by bv_slice

private theorem reaches_pc_extern_over {prog : Program} {target_pc : BitVec 64} {s : State}
    {f : State → State} {post : State → Prop} {oom : State → Prop}
    (h_run : s.status = .Running)
    (h_ext : prog.externAt? s.pc = some f)
    (h_keep : s.mem.KeepsFrozen (f s).mem)
    (h_next : reaches_pc prog target_pc (f s) post oom)
    (h_symtab : (f s).symtab = s.symtab := by rfl) :
    reaches_pc prog target_pc s post oom := by
  intro hL
  have hs := Step.extern h_run h_ext h_keep h_symtab
  rcases h_next (hs.codeLoaded hL) with ⟨sf, hsteps, hout⟩
  exact ⟨sf, Steps.step hs hsteps, hout⟩

private theorem step_blackBox_over {prog : Program} {target_pc entry_bb : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop}
    (hext : prog.externAt? entry_bb = some blackBoxHook)
    (hpc : s.pc = entry_bb)
    (hrun : s.status = .Running)
    (hs' : (s.writeReg64 .x0 (((s.readReg64 .x0).setWidth 8).zeroExtend 64)).setPC (s.readReg64 .lr) = s')
    (hnext : SepWP prog target_pc s' P post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at hnext ⊢
  intro R hm
  refine reaches_pc_extern_over hrun (hpc ▸ hext) (Memory.KeepsFrozen.refl _) ?_ rfl
  change reaches_pc prog target_pc
    ((s.writeReg64 .x0 (((s.readReg64 .x0).setWidth 8).zeroExtend 64)).setPC (s.readReg64 .lr)) _ _
  rw [hs']
  have hmem : s'.mem = s.mem := by rw [← hs']; rfl
  exact hnext R (hmem ▸ hm)

local macro "wp_black_box_over" hext:ident : tactic =>
  `(tactic| (
    apply step_blackBox_over $hext
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
  ))

/-! ## 4. Shared Epilogue from `+0xec` (`Map::next` on Empty `previous_sessions` + Return `Ok(false)`) -/

private theorem cells_96_12_eq_over (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      (∃∗ v0, (sp - 96#64) ↦₆₄ v0 ∗ ∃∗ v1, (sp - 88#64) ↦₆₄ v1 ∗
       ∃∗ v2, (sp - 80#64) ↦₆₄ v2 ∗ ∃∗ v3, (sp - 72#64) ↦₆₄ v3 ∗
       ∃∗ v4, (sp - 64#64) ↦₆₄ v4 ∗ ∃∗ v5, (sp - 56#64) ↦₆₄ v5 ∗
       ∃∗ v6, (sp - 48#64) ↦₆₄ v6 ∗ ∃∗ v7, (sp - 40#64) ↦₆₄ v7 ∗
       ∃∗ v8, (sp - 32#64) ↦₆₄ v8 ∗ ∃∗ v9, (sp - 24#64) ↦₆₄ v9 ∗
       ∃∗ v10, (sp - 16#64) ↦₆₄ v10 ∗ ∃∗ v11, (sp - 8#64) ↦₆₄ v11 ∗ emp) := by
  have hstep (k1 k2 : BitVec 64) (h : k1 - 8#64 = k2) : (sp - k1) + 8#64 = sp - k2 := by
    subst h; bv_omega
  dsimp only [cells]
  rw [hstep 96#64 88#64 rfl, hstep 88#64 80#64 rfl, hstep 80#64 72#64 rfl,
      hstep 72#64 64#64 rfl, hstep 64#64 56#64 rfl, hstep 56#64 48#64 rfl,
      hstep 48#64 40#64 rfl, hstep 40#64 32#64 rfl, hstep 32#64 24#64 rfl,
      hstep 24#64 16#64 rfl, hstep 16#64 8#64 rfl]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 600000 in
private theorem promote_miss_from_ec_wp {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s2 : State) (recPtr prevPtr outPtr : BitVec 64)
    (hpc : s2.pc = (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0xec#64)
    (hrun : s2.status = .Running) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : s2.trace = s0.trace) (hsp : s2.sp = s0.sp - 1184#64)
    (hx0 : s2.readReg64 .x0 = recPtr) (hx23 : s2.readReg64 .x23 = outPtr)
    (hvregs : CalleeSavedVRegsPreserved s0 s2) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s2
      (((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 0#64) ∗
       (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗ (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
       cells (s0.sp - 1248#64) 8 ∗ cells (s0.sp - 1184#64) 10 ∗
       (∃∗ w2e0 : BitVec 64, (s0.sp - 448#64) ↦₆₄ w2e0) ∗ promoteSavedRegs s0)
      (fun sf Pf =>
        (Pf ⊢ ((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 0#64) ∗
          (outPtr ↦₆₄ 0#64) ∗ ((outPtr + 8#64) ↦₈ 0#8) ∗ promoteMissStackCells s0.sp) ∧
        sf.trace = s0.trace ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  unfold promoteSavedRegs promoteMissStackCells
  have hfn : libsignalSessionCode.fnOff promoteMatchingSessionName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
  have hiter := map_iter_next_empty_ok_ext (b := b) (ext := ext)
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr mapIterNextName =
      (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName +
        bv% (ls_off% "<core::iter::adapters::map::Map<core::slice::iter::Iter<alloc::vec::Vec<u8>>, <libsignal_protocol::state::session::SessionRecord>::previous_session_states::{closure#0}> as core::iter::traits::iterator::Iterator>::next" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, mapIterNextName_fnOff_over,
      (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session"),
      BitVec.add_assoc]
    rfl
  rw [hrel] at hiter
  clear hrel
  simp only [mapIterNextEmptySpec] at hiter
  cells_unfold_over
  simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub] at hiter
  dsimp only [tripleRatchetProgAtExt] at hiter hpc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode overPromoteBin b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0xec 76
  code_fetches_range CryptoVerification.libsignalSessionCode overPromoteBin b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0x2e4 32
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    promoteMatchingSessionName = entry
  examples_hide_fetches
  have hx0' : s2.readReg64 (Reg.gpr 0#5) = recPtr := hx0
  have hx23' : s2.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  wp_pull_exists
  wp_steps
  wp_call hiter (s0.sp - 448#64, s0.sp - 1128#64, prevPtr)
  wp_steps
  refine SepWP.done (by simp only [hsp, wp_norm, arm64_norm])
    (by simp only [hrun_sf, wp_norm, arm64_norm])
    ⟨?_, by simp only [htr, hpost, wp_norm, arm64_norm],
     by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
     ⟨by simp only [hsp, hsp_sf, wp_norm, arm64_norm], by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
      by simp only [hsp, hsp_sf, wp_norm, arm64_norm], by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
      by simp only [hsp, hsp_sf, wp_norm, arm64_norm], by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
      by simp only [hsp, hsp_sf, wp_norm, arm64_norm], by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
      by simp only [hsp, hsp_sf, wp_norm, arm64_norm], by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
      by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
      by simp only [CalleeSavedVRegsPreserved, calleeSavedVRegs, wp_norm, arm64_norm] at hvregs hvregs_1 ⊢
         exact hvregs_1.trans hvregs⟩⟩
  sep_frame

/-! ## 5. Inductive Constant-Time Byte-Comparison Loop (General Equal-Length Lists) -/

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem promote_ct_loop_last_wp {b : BitVec 64} {ext : String → Option (State → State)}
    (h_bb : ext "subtle::black_box::<u8>" = some blackBoxHook)
    (k0 a0 : BitVec 8) (acc : Bool) (recPtr serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = 1#64) (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = if acc = true then 1#64 else 0#64)
    (hx26 : s.readReg64 .x26 = recPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0xb4#64) s
      ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0))
      (fun sf Pf =>
        Pf = ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0)) ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧
        sf.readReg64 .x0 = (if ((k0 == a0) && acc) = true then 1#64 else 0#64) ∧
        sf.readReg64 .x23 = outPtr ∧ sf.readReg64 .x26 = recPtr ∧ sf.vregs = s.vregs) := by
  have hfn : libsignalSessionCode.fnOff promoteMatchingSessionName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
  have hext := externAt?_black_box_over b h_bb
  dsimp only [tripleRatchetProgAtExt] at hext hpc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode overPromoteBin b (Rust.withPanics ext)
    hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0x80 56
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    promoteMatchingSessionName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = alicePtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = 1#64 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = serPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = if acc = true then 1#64 else 0#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = recPtr := hx26
  wp_steps; wp_black_box_over hext; wp_steps; wp_black_box_over hext
  refine SepWP.done (by simp only [hpc, hx21', wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm])
    ⟨rfl, by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [hx25', wp_norm, arm64_norm], by simp only [hx23', wp_norm, arm64_norm],
     by simp only [hx26', wp_norm, arm64_norm], rfl⟩

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem promote_ct_loop_step_wp {b : BitVec 64} {ext : String → Option (State → State)}
    (h_bb : ext "subtle::black_box::<u8>" = some blackBoxHook)
    (k0 a0 : BitVec 8) (acc : Bool) (m : Nat) (hm_pos : 0 < m) (hm_lt : m + 1 < 2 ^ 64)
    (recPtr serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (m + 1)) (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = if acc = true then 1#64 else 0#64)
    (hx26 : s.readReg64 .x26 = recPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64) s
      ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0))
      (fun s1 Pf =>
        Pf = ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0)) ∧ s1.trace = s.trace ∧ s1.sp = s.sp ∧
        s1.readReg64 .x19 = alicePtr + 1#64 ∧ s1.readReg64 .x21 = BitVec.ofNat 64 m ∧
        s1.readReg64 .x22 = serPtr + 1#64 ∧ s1.readReg64 .x23 = outPtr ∧
        s1.readReg64 .x25 = (if ((k0 == a0) && acc) = true then 1#64 else 0#64) ∧
        s1.readReg64 .x26 = recPtr ∧ s1.vregs = s.vregs) := by
  have hbr := cond_ne_subs64_one_over (by omega : 1 < m + 1) hm_lt
  have hsub1 : BitVec.ofNat 64 (m + 1) - 1#64 = BitVec.ofNat 64 m := ofNat64_succ_sub_one_over m
  have hfn : libsignalSessionCode.fnOff promoteMatchingSessionName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
  have hext := externAt?_black_box_over b h_bb
  dsimp only [tripleRatchetProgAtExt] at hext hpc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode overPromoteBin b (Rust.withPanics ext)
    hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0x80 56
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    promoteMatchingSessionName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = alicePtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 (m + 1) := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = serPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = if acc = true then 1#64 else 0#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = recPtr := hx26
  wp_steps; wp_black_box_over hext; wp_steps
  refine SepWP.done (by simp only [hpc, hx21', hbr, wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm])
    ⟨rfl, by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [hx19', wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hx21', hsub1],
     by simp only [hx22', wp_norm, arm64_norm], by simp only [hx23', wp_norm, arm64_norm],
     by simp only [hx25', wp_norm, arm64_norm], by simp only [hx26', wp_norm, arm64_norm], rfl⟩

set_option maxHeartbeats 400000 in
private theorem promote_ct_loop_gen_wp {b : BitVec 64} {ext : String → Option (State → State)}
    (h_bb : ext "subtle::black_box::<u8>" = some blackBoxHook)
    (ks as_ : List (BitVec 8)) (acc : Bool)
    (hlen : ks.length = as_.length) (hne : ks ≠ []) (hlt : ks.length < 2 ^ 64)
    (recPtr serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64)
    (hrun : s.status = .Running) (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ks.length) (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = if acc = true then 1#64 else 0#64)
    (hx26 : s.readReg64 .x26 = recPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0xb4#64) s
      ((serPtr ↦ₛ ks) ∗ (alicePtr ↦ₛ as_))
      (fun sf Pf =>
        Pf = ((serPtr ↦ₛ ks) ∗ (alicePtr ↦ₛ as_)) ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧
        sf.readReg64 .x0 = (if ctBytesEqAcc ks as_ acc = true then 1#64 else 0#64) ∧
        sf.readReg64 .x23 = outPtr ∧ sf.readReg64 .x26 = recPtr ∧ sf.vregs = s.vregs) := by
  induction ks generalizing as_ acc serPtr alicePtr s with
  | nil => exact absurd rfl hne
  | cons k0 krest ih =>
    cases as_ with
    | nil => simp at hlen
    | cons a0 arest =>
      have hlen' : krest.length = arest.length := by simpa using hlen
      cases krest with
      | nil =>
        cases arest with
        | nil =>
          dsimp only [List.length_cons, List.length_nil, ctBytesEqAcc] at hx21 ⊢
          have hpre_eq : ((serPtr ↦ₛ [k0]) ∗ (alicePtr ↦ₛ [a0])) =
              ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0)) := by
            rw [pointsToBytes_cons, pointsToBytes_nil, pointsToBytes_cons, pointsToBytes_nil,
              sepConj_emp, sepConj_emp]
          rw [hpre_eq]
          exact promote_ct_loop_last_wp h_bb k0 a0 acc recPtr serPtr alicePtr outPtr s
            hpc hrun hx19 hx21 hx22 hx23 hx25 hx26
        | cons _ _ => simp at hlen'
      | cons k1 krest' =>
        cases arest with
        | nil => simp at hlen'
        | cons a1 arest' =>
          have hm_pos : 0 < (k1 :: krest').length := by simp
          have hm_lt : (k1 :: krest').length + 1 < 2 ^ 64 := by simpa using hlt
          dsimp only [List.length_cons] at hx21
          conv => arg 4; rw [pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]; simp only [sepConj_assoc]
          refine SepWP.bind_seq_readOnly
            (promote_ct_loop_step_wp h_bb k0 a0 acc (k1 :: krest').length hm_pos hm_lt
              recPtr serPtr alicePtr outPtr s hpc hrun hx19 hx21 hx22 hx23 hx25 hx26)
            (by sep_focus)
            fun s1 hpc1 hrun1 ⟨htr1, hsp1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hv1⟩ => ?_
          refine SepWP.bind_seq_readOnly
            (ih (a1 :: arest') ((k0 == a0) && acc) hlen' (by simp) (by omega)
              (serPtr + 1#64) (alicePtr + 1#64) s1 hpc1 hrun1 hx19_1 hx21_1 hx22_1 hx23_1 hx25_1 hx26_1)
            (by sep_focus)
            fun sf hpcf hrunf ⟨htrf, hspf, hx0_f, hx23_f, hx26_f, hv_f⟩ => ?_
          refine SepWP.done hpcf hrunf
            ⟨?_, htrf.trans htr1, hspf.trans hsp1, hx0_f, hx23_f, hx26_f, hv_f.trans hv1⟩
          rw [pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]; ac_rfl

/-! ## 6. Cells-Level Proofs for the Three Miss Branches -/

private theorem cells_1184_split_2 (sp : BitVec 64) :
    cells (sp - 1184#64) 10 =
      (∃∗ w4a0 : BitVec 64, (sp - 1184#64) ↦₆₄ w4a0) ∗
      (∃∗ w470 : BitVec 64, (sp - 1136#64) ↦₆₄ w470) ∗
      (cells (sp - 1176#64) 5 ∗ cells (sp - 1128#64) 3) := by
  have hstep (k1 k2 : BitVec 64) (h : k1 - 8#64 = k2) : (sp - k1) + 8#64 = sp - k2 := by
    subst h; bv_omega
  dsimp only [cells]
  simp only [← sepExists_sepConj_left, sepConj_emp]
  rw [hstep 1184#64 1176#64 rfl, hstep 1176#64 1168#64 rfl, hstep 1168#64 1160#64 rfl,
      hstep 1160#64 1152#64 rfl, hstep 1152#64 1144#64 rfl, hstep 1144#64 1136#64 rfl,
      hstep 1136#64 1128#64 rfl, hstep 1128#64 1120#64 rfl, hstep 1120#64 1112#64 rfl]
  ac_rfl

private theorem cells_1184_merge_2 (sp v0 v6 : BitVec 64) :
    ((sp - 1184#64) ↦₆₄ v0) ∗ ((sp - 1136#64) ↦₆₄ v6) ∗
      (cells (sp - 1176#64) 5 ∗ cells (sp - 1128#64) 3) ⊢
      cells (sp - 1184#64) 10 := by
  rw [cells_1184_split_2 sp]
  exact sepConj_mono (Entails.sepExists_right v0 (Entails.refl _))
    (sepConj_mono_left (Entails.sepExists_right v6 (Entails.refl _)))

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 600000 in
theorem promote_matching_session_ver_miss_raw_ok {b : BitVec 64}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName)
      promoteMatchingSessionVerMissRawSpec := by
  have hfn : libsignalSessionCode.fnOff promoteMatchingSessionName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
  refine subroutine_ok_of_sepWP_init
    fun ⟨recPtr, prevPtr, curDiscr, abkPtr, abkLen, sessVer, msgVer, serPtr, outPtr⟩ R s0
      hpc hrun hpre hsp_align => ?_
  dsimp only [promoteMatchingSessionVerMissRawSpec, sessionRecordMissPromoteFieldsAt] at hpre ⊢
  refine ⟨_, hpre, ?_⟩
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
  obtain ⟨hx0, hx1, hx2, hx3, hx8, hcur, hver_ne⟩ := hpure
  have hcmn := cond_eq_adds64_one_false_over hcur
  have hvne_b : ((if (sessVer == 0#32) = true then 2#32 else sessVer) != msgVer.zeroExtend 32) = true := by
    simp only [beq_iff_eq, bne_iff_ne]; exact hver_ne
  conv => arg 4; unfold promoteMissStackCells; rw [cells_1184_split_2 s0.sp]
  have hp1 :
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0xec#64) s0
        (((recPtr + 0x18#64) ↦₆₄ curDiscr) ∗ ((recPtr + 0x160#64) ↦₃₂ sessVer) ∗
         (∃∗ w4a0 : BitVec 64, (s0.sp - 1184#64) ↦₆₄ w4a0) ∗
         (∃∗ w470 : BitVec 64, (s0.sp - 1136#64) ↦₆₄ w470) ∗ cells (s0.sp - 96#64) 12)
        (fun s1 P1 =>
          (P1 ⊢ ((recPtr + 0x18#64) ↦₆₄ curDiscr) ∗ ((recPtr + 0x160#64) ↦₃₂ sessVer) ∗
            ((s0.sp - 1184#64) ↦₆₄ 0#64) ∗ ((s0.sp - 1136#64) ↦₆₄ serPtr) ∗ promoteSavedRegs s0) ∧
          s1.trace = s0.trace ∧ s1.sp = s0.sp - 1184#64 ∧
          s1.readReg64 .x0 = recPtr ∧ s1.readReg64 .x23 = outPtr ∧ s1.vregs = s0.vregs) := by
    rw [cells_96_12_eq_over s0.sp]; dsimp only [tripleRatchetProgAtExt] at hpc ⊢
    code_fetches_range CryptoVerification.libsignalSessionCode overPromoteBin b (Rust.withPanics ext)
      hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0 92
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      promoteMatchingSessionName = entry
    examples_hide_fetches
    have hx0' : s0.readReg64 (Reg.gpr 0#5) = recPtr := hx0
    have hx1' : s0.readReg64 (Reg.gpr 1#5) = msgVer.zeroExtend 64 := hx1
    have hx2' : s0.readReg64 (Reg.gpr 2#5) = serPtr := hx2
    have hx8' : s0.readReg64 (Reg.gpr 8#5) = outPtr := hx8
    wp_pull_exists; wp_steps
    refine SepWP.done (by simp only [hpc, hcmn, hvne_b, wp_norm, arm64_norm])
      (by simp only [hrun, wp_norm, arm64_norm])
      ⟨by unfold promoteSavedRegs; sep_frame, by simp only [wp_norm, arm64_norm],
       by simp only [wp_norm, arm64_norm], by simp only [hx0', wp_norm, arm64_norm],
       by simp only [hx8', wp_norm, arm64_norm], rfl⟩
  apply SepWP.seq
  · exact SepWP.frame_auto hp1
  · intro s1 _ hpc1 hrun1 ⟨hent1, htr1, hsp1, hx0_1, hx23_1, hv1⟩
    refine SepWP.weaken_pre hent1 (SepWP.focus_weaken (cells_1184_merge_2 s0.sp 0#64 serPtr) (by sep_focus) ?_)
    refine SepWP.mono (SepWP.frame_auto (promote_miss_from_ec_wp s0 s1 recPtr prevPtr outPtr hpc1 hrun1
      hsp_align' htr1 hsp1 hx0_1 hx23_1 (by simp [CalleeSavedVRegsPreserved, calleeSavedVRegs, hv1]))) ?_
      (fun _ _ _ hf => hf)
    intro sf _ _ _ ⟨hentf, htrf, hspf, hcsf⟩
    exact ⟨fun hm => Satisfies.mono (sepConj_mono_left (Entails.trans hentf (by rw [htrf]; sep_frame))) hm,
      hspf, hcsf⟩

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 600000 in
theorem promote_matching_session_len_miss_raw_ok {b : BitVec 64}
    {ext : String → Option (State → State)}
    (h_bb : ext "subtle::black_box::<u8>" = some blackBoxHook) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName)
      promoteMatchingSessionLenMissRawSpec := by
  have hfn : libsignalSessionCode.fnOff promoteMatchingSessionName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
  have hext := externAt?_black_box_over b h_bb
  refine subroutine_ok_of_sepWP_init
    fun ⟨recPtr, prevPtr, curDiscr, abkPtr, abkLen, sessVer, msgVer, serPtr, outPtr⟩ R s0
      hpc hrun hpre hsp_align => ?_
  dsimp only [promoteMatchingSessionLenMissRawSpec, sessionRecordMissPromoteFieldsAt] at hpre ⊢
  refine ⟨_, hpre, ?_⟩
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
  obtain ⟨hx0, hx1, hx2, hx3, hx8, hcur, hver_eq, hlen_ne⟩ := hpure
  have hcmn := cond_eq_adds64_one_false_over hcur
  have hveq_b : ((if (sessVer == 0#32) = true then 2#32 else sessVer) != msgVer.zeroExtend 32) = false := by
    simp only [beq_iff_eq, hver_eq, bne_self_eq_false]
  have hlne_b : (33#64 != abkLen) = true := bne_iff_ne.mpr (fun h33 => hlen_ne h33.symm)
  have hlne_b' : (abkLen != 33#64) = true := bne_iff_ne.mpr hlen_ne
  conv => arg 4; unfold promoteMissStackCells; rw [cells_1184_split_2 s0.sp]
  have hp1 :
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0xec#64) s0
        (((recPtr + 0x18#64) ↦₆₄ curDiscr) ∗ ((recPtr + 0x88#64) ↦₆₄ abkLen) ∗
         ((recPtr + 0x160#64) ↦₃₂ sessVer) ∗ (∃∗ w4a0 : BitVec 64, (s0.sp - 1184#64) ↦₆₄ w4a0) ∗
         (∃∗ w470 : BitVec 64, (s0.sp - 1136#64) ↦₆₄ w470) ∗ cells (s0.sp - 96#64) 12)
        (fun s1 P1 =>
          (P1 ⊢ ((recPtr + 0x18#64) ↦₆₄ curDiscr) ∗ ((recPtr + 0x88#64) ↦₆₄ abkLen) ∗
            ((recPtr + 0x160#64) ↦₃₂ sessVer) ∗ ((s0.sp - 1184#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 1136#64) ↦₆₄ serPtr) ∗ promoteSavedRegs s0) ∧
          s1.trace = s0.trace ∧ s1.sp = s0.sp - 1184#64 ∧
          s1.readReg64 .x0 = recPtr ∧ s1.readReg64 .x23 = outPtr ∧ s1.vregs = s0.vregs) := by
    rw [cells_96_12_eq_over s0.sp]; dsimp only [tripleRatchetProgAtExt] at hext hpc ⊢
    code_fetches_range CryptoVerification.libsignalSessionCode overPromoteBin b (Rust.withPanics ext)
      hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0 104
    code_fetches_range CryptoVerification.libsignalSessionCode overPromoteBin b (Rust.withPanics ext)
      hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0xa4 28
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      promoteMatchingSessionName = entry
    examples_hide_fetches
    have hx0' : s0.readReg64 (Reg.gpr 0#5) = recPtr := hx0
    have hx1' : s0.readReg64 (Reg.gpr 1#5) = msgVer.zeroExtend 64 := hx1
    have hx2' : s0.readReg64 (Reg.gpr 2#5) = serPtr := hx2
    have hx3' : s0.readReg64 (Reg.gpr 3#5) = 33#64 := hx3
    have hx8' : s0.readReg64 (Reg.gpr 8#5) = outPtr := hx8
    wp_pull_exists; wp_steps; wp_black_box_over hext; wp_steps
    refine SepWP.done (by simp only [hpc, hcmn, hveq_b, hlne_b, hlne_b', hx3', wp_norm, arm64_norm])
      (by simp only [hrun, wp_norm, arm64_norm])
      ⟨by unfold promoteSavedRegs; sep_frame, by simp only [wp_norm, arm64_norm],
       by simp only [wp_norm, arm64_norm], by simp only [hx0', wp_norm, arm64_norm],
       by simp only [hx8', wp_norm, arm64_norm], rfl⟩
  apply SepWP.seq
  · exact SepWP.frame_auto hp1
  · intro s1 _ hpc1 hrun1 ⟨hent1, htr1, hsp1, hx0_1, hx23_1, hv1⟩
    refine SepWP.weaken_pre hent1 (SepWP.focus_weaken (cells_1184_merge_2 s0.sp 0#64 serPtr) (by sep_focus) ?_)
    refine SepWP.mono (SepWP.frame_auto (promote_miss_from_ec_wp s0 s1 recPtr prevPtr outPtr hpc1 hrun1
      hsp_align' htr1 hsp1 hx0_1 hx23_1 (by simp [CalleeSavedVRegsPreserved, calleeSavedVRegs, hv1]))) ?_
      (fun _ _ _ hf => hf)
    intro sf _ _ _ ⟨hentf, htrf, hspf, hcsf⟩
    exact ⟨fun hm => Satisfies.mono (sepConj_mono_left (Entails.trans hentf (by rw [htrf]; sep_frame))) hm,
      hspf, hcsf⟩

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem promote_key_miss_seg1_wp {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (recPtr curDiscr abkPtr serPtr outPtr : BitVec 64) (sessVer : BitVec 32) (msgVer : BitVec 8)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName)
    (hrun : s0.status = .Running) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 .x0 = recPtr) (hx1 : s0.readReg64 .x1 = msgVer.zeroExtend 64)
    (hx2 : s0.readReg64 .x2 = serPtr) (hx3 : s0.readReg64 .x3 = 33#64) (hx8 : s0.readReg64 .x8 = outPtr)
    (hcur : curDiscr ≠ 0xffffffffffffffff#64)
    (hver_eq : (if sessVer = 0#32 then 2#32 else sessVer) = msgVer.zeroExtend 32) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64) s0
      (((recPtr + 0x18#64) ↦₆₄ curDiscr) ∗ ((recPtr + 0x80#64) ↦₆₄ abkPtr) ∗
       ((recPtr + 0x88#64) ↦₆₄ 33#64) ∗ ((recPtr + 0x160#64) ↦₃₂ sessVer) ∗
       (∃∗ w4a0 : BitVec 64, (s0.sp - 1184#64) ↦₆₄ w4a0) ∗
       (∃∗ w470 : BitVec 64, (s0.sp - 1136#64) ↦₆₄ w470) ∗ cells (s0.sp - 96#64) 12)
      (fun s1 P1 =>
        (P1 ⊢ ((recPtr + 0x18#64) ↦₆₄ curDiscr) ∗ ((recPtr + 0x80#64) ↦₆₄ abkPtr) ∗
          ((recPtr + 0x88#64) ↦₆₄ 33#64) ∗ ((recPtr + 0x160#64) ↦₃₂ sessVer) ∗
          ((s0.sp - 1184#64) ↦₆₄ 0#64) ∗ ((s0.sp - 1136#64) ↦₆₄ serPtr) ∗ promoteSavedRegs s0) ∧
        s1.trace = s0.trace ∧ s1.sp = s0.sp - 1184#64 ∧
        s1.readReg64 .x19 = abkPtr ∧ s1.readReg64 .x21 = 33#64 ∧
        s1.readReg64 .x22 = serPtr ∧ s1.readReg64 .x23 = outPtr ∧
        s1.readReg64 .x25 = 1#64 ∧ s1.readReg64 .x26 = recPtr ∧ s1.vregs = s0.vregs) := by
  have hfn : libsignalSessionCode.fnOff promoteMatchingSessionName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
  have hcmn := cond_eq_adds64_one_false_over hcur
  have hveq_b : ((if (sessVer == 0#32) = true then 2#32 else sessVer) != msgVer.zeroExtend 32) = false := by
    simp only [beq_iff_eq, hver_eq, bne_self_eq_false]
  rw [cells_96_12_eq_over s0.sp]; dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode overPromoteBin b (Rust.withPanics ext)
    hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0 128
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    promoteMatchingSessionName = entry
  examples_hide_fetches
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = recPtr := hx0
  have hx1' : s0.readReg64 (Reg.gpr 1#5) = msgVer.zeroExtend 64 := hx1
  have hx2' : s0.readReg64 (Reg.gpr 2#5) = serPtr := hx2
  have hx3' : s0.readReg64 (Reg.gpr 3#5) = 33#64 := hx3
  have hx8' : s0.readReg64 (Reg.gpr 8#5) = outPtr := hx8
  wp_pull_exists; wp_steps
  refine SepWP.done (by simp only [hpc, hcmn, hveq_b, hx3', wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm])
    ⟨by unfold promoteSavedRegs; sep_frame, by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [hx0', wp_norm, arm64_norm],
     by simp only [hx3', wp_norm, arm64_norm], by simp only [hx2', wp_norm, arm64_norm],
     by simp only [hx8', wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [hx0', wp_norm, arm64_norm], rfl⟩

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem promote_b4_to_ec_wp {b : BitVec 64} {ext : String → Option (State → State)}
    (recPtr outPtr : BitVec 64) (s2 : State)
    (hpc2 : s2.pc = (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0xb4#64)
    (hrun2 : s2.status = .Running) (hx0_2 : (s2.readReg64 .x0).setWidth 32 = 0#32)
    (hx23_2 : s2.readReg64 .x23 = outPtr) (hx26_2 : s2.readReg64 .x26 = recPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0xec#64) s2 emp
      (fun s3 P3 =>
        P3 = emp ∧ s3.trace = s2.trace ∧ s3.sp = s2.sp ∧
        s3.readReg64 .x0 = recPtr ∧ s3.readReg64 .x23 = outPtr ∧ s3.vregs = s2.vregs) := by
  have hfn : libsignalSessionCode.fnOff promoteMatchingSessionName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
  dsimp only [tripleRatchetProgAtExt] at hpc2 ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode overPromoteBin b (Rust.withPanics ext)
    hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0xb4 12
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr promoteMatchingSessionName = entry
  examples_hide_fetches
  have hx0_2_ex : BitVec.extractLsb' 0 32 (s2.readReg64 (Reg.gpr 0#5)) = 0#32 := by
    rw [extractLsb32_eq_setWidth32_over]; exact hx0_2
  have hx0_2_sw : BitVec.setWidth 32 (s2.readReg64 (Reg.gpr 0#5)) = 0#32 := hx0_2
  have hx23_2' : s2.readReg64 (Reg.gpr 23#5) = outPtr := hx23_2
  have hx26_2' : s2.readReg64 (Reg.gpr 26#5) = recPtr := hx26_2
  wp_steps
  exact SepWP.done (by simp only [hpc2, hx0_2_ex, hx0_2_sw, wp_norm, arm64_norm])
    (by simp only [hrun2, wp_norm, arm64_norm])
    ⟨rfl, by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [hx26_2', wp_norm, arm64_norm], by simp only [hx23_2', wp_norm, arm64_norm], rfl⟩

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 600000 in
theorem promote_matching_session_key_miss_raw_ok {b : BitVec 64}
    {ext : String → Option (State → State)}
    (h_bb : ext "subtle::black_box::<u8>" = some blackBoxHook) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName)
      promoteMatchingSessionKeyMissRawSpec := by
  refine subroutine_ok_of_sepWP_init
    fun ⟨recPtr, prevPtr, curDiscr, abkPtr, sessVer, msgVer, serPtr, outPtr, serBytes, ak⟩ R s0
      hpc hrun hpre hsp_align => ?_
  dsimp only [promoteMatchingSessionKeyMissRawSpec, sessionRecordMissPromoteFieldsAt] at hpre ⊢
  refine ⟨_, hpre, ?_⟩
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
  obtain ⟨hx0, hx1, hx2, hx3, hx8, hcur, hver_eq, hklen, halen, hne⟩ := hpure
  have hacc_false : ctBytesEqAcc serBytes ak true = false :=
    ctBytesEqAcc_true_of_ne (hklen.trans halen.symm) hne
  conv => arg 4; unfold promoteMissStackCells; rw [cells_1184_split_2 s0.sp]
  apply SepWP.seq
  · exact SepWP.frame_auto (promote_key_miss_seg1_wp s0 recPtr curDiscr abkPtr serPtr outPtr sessVer msgVer
      hpc hrun hsp_align' hx0 hx1 hx2 hx3 hx8 hcur hver_eq)
  · intro s1 _ hpc1 hrun1 ⟨hent1, htr1, hsp1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hv1⟩
    refine SepWP.weaken_pre hent1 ?_
    have hloop := promote_ct_loop_gen_wp h_bb serBytes ak true (hklen.trans halen.symm)
      (by intro hn; rw [hn] at hklen; simp at hklen) (by rw [hklen]; decide)
      recPtr serPtr abkPtr outPtr s1 hpc1 hrun1 hx19_1
      (by rw [hklen]; exact hx21_1) hx22_1 hx23_1 hx25_1 hx26_1
    rw [hacc_false] at hloop; simp only [Bool.false_eq_true, ↓reduceIte] at hloop
    refine SepWP.bind_seq_readOnly hloop (by sep_focus)
      fun s2 hpc2 hrun2 ⟨htr2, hsp2, hx0_2, hx23_2, hx26_2, hv2⟩ => ?_
    refine SepWP.bind_seq_readOnly
      (promote_b4_to_ec_wp recPtr outPtr s2 hpc2 hrun2 (by rw [hx0_2]; rfl) hx23_2 hx26_2)
      (emp_sepConj _).symm fun s3 hpc3 hrun3 ⟨htr3, hsp3, hx0_3, hx23_3, hv3⟩ => ?_
    have hv_30 : s3.vregs = s0.vregs := hv3.trans (hv2.trans hv1)
    refine SepWP.focus_weaken (cells_1184_merge_2 s0.sp 0#64 serPtr) (by sep_focus) ?_
    refine SepWP.mono (SepWP.frame_auto (promote_miss_from_ec_wp s0 s3 recPtr prevPtr outPtr hpc3 hrun3
      hsp_align' (htr3.trans (htr2.trans htr1)) (hsp3.trans (hsp2.trans hsp1)) hx0_3 hx23_3
      (by simp [CalleeSavedVRegsPreserved, calleeSavedVRegs, hv_30]))) ?_ (fun _ _ _ hf => hf)
    intro sf _ _ _ ⟨hentf, htrf, hspf, hcsf⟩
    exact ⟨fun hm => Satisfies.mono (sepConj_mono_left (Entails.trans hentf (by rw [htrf]; sep_frame))) hm,
      hspf, hcsf⟩

/-! ## 7. Record-Level Miss Theorems -/

set_option maxHeartbeats 600000 in
theorem promote_matching_session_record_over_ok {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_bb : ext "subtle::black_box::<u8>" = some blackBoxHook) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName)
      (promoteMatchingSessionRecordOverSpec A) := by
  refine subroutine_ok_by_cases
    (fun (x : BitVec 64 × BitVec 64 × BitVec 64 × SessionGhost × Session (List (BitVec 8)) ×
      BitVec 8 × BitVec 64 × BitVec 64 × List (BitVec 8)) =>
        x.2.2.2.2.1.state.version = x.2.2.2.2.2.1.zeroExtend 32) ?_ ?_
  · refine subroutine_ok_by_cases
      (fun (x : BitVec 64 × BitVec 64 × BitVec 64 × SessionGhost × Session (List (BitVec 8)) ×
        BitVec 8 × BitVec 64 × BitVec 64 × List (BitVec 8)) =>
          x.2.2.2.2.1.aliceBaseKey.length = 33) ?_ ?_
    · refine subroutine_ok_refine_frame (promote_matching_session_key_miss_raw_ok h_bb) ?_
      intro ⟨recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key⟩ R s0 hpre
      dsimp only [promoteMatchingSessionRecordOverSpec] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hlen33, hpre⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hver, hpre⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, hmiss, hklen⟩, hmem⟩
      have hne_key : key ≠ sess.aliceBaseKey := fun hk => hmiss ⟨hver, hk.symm⟩
      have hrec_mem : s0.mem ⊨ sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
          ((serPtr ↦ₛ key) ∗ (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
           (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗ stackAt s0.sp promoteMatchingSessionMissStack ∗ R) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
      obtain ⟨hcap_ne, halice, hle, _hlt⟩ := sessionRecordAt_miss_facts hrec_mem
      have hexp := sessionRecordAt_expose_miss A recPtr prevCap prevPtr G sess
      have hal33 : G.alice.bytes.length = 33 := by rw [halice]; exact hlen33
      have hcapnz : G.alice.cap ≠ 0 := by
        intro h0; have h1 : G.alice.cap.toNat = 0 := by simp [h0]
        rw [h1, hal33] at hle; omega
      have habk : BitVec.ofNat 64 G.alice.bytes.length = 33#64 := by rw [hal33]
      rw [habk, aliceBufOverAt_expose_33 A G sess.aliceBaseKey halice hlen33 hcapnz] at hexp
      refine ⟨⟨recPtr, prevPtr, G.localIk.cap, G.alice.ptr, sess.state.sessionVersion,
          msgVer, serPtr, outPtr, key, sess.aliceBaseKey⟩,
        sessionRecordMissRestAt A recPtr prevCap prevPtr G sess ∗
          (A.live G.alice.ptr G.alice.cap.toNat 1 ∗ memRegion (G.alice.ptr + 33#64) (G.alice.cap.toNat - 33)) ∗
          (memRegion (s0.sp - 1104#64) 656 ∗ memRegion (s0.sp - 440#64) 344), ?_, ?_⟩
      · dsimp only [promoteMatchingSessionKeyMissRawSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hcap_ne, hver, hklen, hlen33, hne_key⟩, ?_⟩
        rw [hexp, stackAt_promoteMissStack_eq s0.sp] at hrec_mem
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hrec_mem
      · intro sf hpost
        dsimp only [promoteMatchingSessionKeyMissRawSpec, promoteMatchingSessionRecordOverSpec] at hpost ⊢
        rw [hexp, stackAt_promoteMissStack_eq s0.sp]
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
    · refine subroutine_ok_refine_frame (promote_matching_session_len_miss_raw_ok h_bb) ?_
      intro ⟨recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key⟩ R s0 hpre
      dsimp only [promoteMatchingSessionRecordOverSpec] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hlen_ne, hpre⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hver, hpre⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, _hmiss, _hklen⟩, hmem⟩
      have hrec_mem : s0.mem ⊨ sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
          ((serPtr ↦ₛ key) ∗ (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
           (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗ stackAt s0.sp promoteMatchingSessionMissStack ∗ R) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
      obtain ⟨hcap_ne, halice, hle, hlt⟩ := sessionRecordAt_miss_facts hrec_mem
      have hexp := sessionRecordAt_expose_miss A recPtr prevCap prevPtr G sess
      have habk_ne : BitVec.ofNat 64 G.alice.bytes.length ≠ 33#64 :=
        ofNat_len_ne_33 (Nat.lt_of_le_of_lt hle hlt) (by rw [halice]; exact hlen_ne)
      refine ⟨⟨recPtr, prevPtr, G.localIk.cap, G.alice.ptr, BitVec.ofNat 64 G.alice.bytes.length,
          sess.state.sessionVersion, msgVer, serPtr, outPtr⟩,
        sessionRecordMissRestAt A recPtr prevCap prevPtr G sess ∗ aliceBufOverAt A G ∗ (serPtr ↦ₛ key) ∗
          (memRegion (s0.sp - 1104#64) 656 ∗ memRegion (s0.sp - 440#64) 344), ?_, ?_⟩
      · dsimp only [promoteMatchingSessionLenMissRawSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hcap_ne, hver, habk_ne⟩, ?_⟩
        rw [hexp, stackAt_promoteMissStack_eq s0.sp] at hrec_mem
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hrec_mem
      · intro sf hpost
        dsimp only [promoteMatchingSessionLenMissRawSpec, promoteMatchingSessionRecordOverSpec] at hpost ⊢
        rw [hexp, stackAt_promoteMissStack_eq s0.sp]
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · refine subroutine_ok_refine_frame promote_matching_session_ver_miss_raw_ok ?_
    intro ⟨recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key⟩ R s0 hpre
    dsimp only [promoteMatchingSessionRecordOverSpec] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hver_ne, hpre⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, _hmiss, _hklen⟩, hmem⟩
    have hrec_mem : s0.mem ⊨ sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
        ((serPtr ↦ₛ key) ∗ (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
         (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗ stackAt s0.sp promoteMatchingSessionMissStack ∗ R) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    obtain ⟨hcap_ne, _halice, _hle, _hlt⟩ := sessionRecordAt_miss_facts hrec_mem
    have hexp := sessionRecordAt_expose_miss A recPtr prevCap prevPtr G sess
    refine ⟨⟨recPtr, prevPtr, G.localIk.cap, G.alice.ptr, BitVec.ofNat 64 G.alice.bytes.length,
        sess.state.sessionVersion, msgVer, serPtr, outPtr⟩,
      sessionRecordMissRestAt A recPtr prevCap prevPtr G sess ∗ aliceBufOverAt A G ∗ (serPtr ↦ₛ key) ∗
        (memRegion (s0.sp - 1104#64) 656 ∗ memRegion (s0.sp - 440#64) 344), ?_, ?_⟩
    · dsimp only [promoteMatchingSessionVerMissRawSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hcap_ne, hver_ne⟩, ?_⟩
      rw [hexp, stackAt_promoteMissStack_eq s0.sp] at hrec_mem
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hrec_mem
    · intro sf hpost
      dsimp only [promoteMatchingSessionVerMissRawSpec, promoteMatchingSessionRecordOverSpec] at hpost ⊢
      rw [hexp, stackAt_promoteMissStack_eq s0.sp]
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

set_option maxHeartbeats 400000 in
/-- Public `promoteMatchingSessionMissSpec` theorem mirroring `Matched.promote_matching_session_match_ok`. -/
theorem promote_matching_session_miss_ok {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_bb : ext "subtle::black_box::<u8>" = some blackBoxHook) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName)
      (promoteMatchingSessionMissSpec A) := by
  refine subroutine_ok_refine_frame (promote_matching_session_record_over_ok (A := A) h_bb) ?_
  intro x R s0 hpre
  dsimp only [promoteMatchingSessionMissSpec] at hpre; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, hcur, hmiss, hklen⟩, hmem⟩
  have hrec_sat : s0.mem ⊨ sessionRecordAt A x.recPtr x.g x.r ∗
      ((x.serPtr ↦ₛ x.serBytes) ∗ memRegion x.outPtr 16 ∗ stackAt s0.sp promoteMatchingSessionMissStack ∗ R) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  have hg_some : ∃ G : SessionGhost, x.g.cur = some G := by
    have hrec_l := Satisfies.of_sep_left hrec_sat
    unfold sessionRecordAt at hrec_l; rw [hcur] at hrec_l
    cases hgc : x.g.cur with
    | none =>
      rw [hgc] at hrec_l; have hf := Satisfies.of_sep_right hrec_l
      rw [satisfies_pure] at hf; exact False.elim hf
    | some G => exact ⟨G, rfl⟩
  obtain ⟨G, hgc⟩ := hg_some
  have hrec_eq : sessionRecordAt A x.recPtr x.g x.r =
      sessionRecordAt A x.recPtr ⟨x.g.prevCap, x.g.prevPtr, some G⟩ ⟨some x.s⟩ := by
    unfold sessionRecordAt; rw [hgc, hcur]
  refine ⟨(x.recPtr, x.g.prevCap, x.g.prevPtr, G, x.s, x.msgVer, x.serPtr, x.outPtr, x.serBytes),
    memRegion (x.outPtr + 9#64) 7, ?_, ?_⟩
  · dsimp only [promoteMatchingSessionRecordOverSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hmiss, hklen⟩, ?_⟩
    rw [hrec_eq, outRegion16_split_over x.outPtr] at hrec_sat
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hrec_sat
  · intro sf hpost
    dsimp only [promoteMatchingSessionRecordOverSpec, promoteMatchingSessionMissSpec] at hpost ⊢
    rw [hrec_eq]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

/-! ## 8. Contract-Backed `_ext32` Miss Theorems (`CliExt.blackBoxSpec`) -/

private theorem black_box_subroutine_ok_ext32 (b : BitVec 64)
    {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>" CliExt.blackBoxSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName +
        bv% (ls_off% "subtle::black_box::<u8>" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session"))
      CliExt.blackBoxSpec :=
  hook_ok_at (P := libsignalSessionCode) (b := b) (hooks := ext)
    (name := promoteMatchingSessionName) (hname := "subtle::black_box::<u8>")
    (k := num% (ls_off% "subtle::black_box::<u8>" -
      ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session"))
    (stub := num% (ls_off% "subtle::black_box::<u8>"))
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
    (by decide +kernel) (by decide +kernel) (ls_hook% "subtle::black_box::<u8>")
    (by decide +kernel) h_bb

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem promote_ct_loop_last_wp_ext32 {b : BitVec 64} {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>" CliExt.blackBoxSpec)
    (recPtr outPtr : BitVec 64) (k0 a0 : BitVec 8) (acc : Bool) (serPtr alicePtr : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = alicePtr) (hx21 : s.readReg64 .x21 = 1#64)
    (hx22 : s.readReg64 .x22 = serPtr) (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = if acc = true then 1#64 else 0#64) (hx26 : s.readReg64 .x26 = recPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0xb4#64) s
      ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0) ∗ stackAt s.sp extHookStack)
      (fun sf Pf =>
        (Pf ⊢ (serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0) ∗ stackAt s.sp extHookStack) ∧
        sf.trace = s.trace ∧ sf.sp = s.sp ∧
        (sf.readReg64 .x0).setWidth 32 = (if ((k0 == a0) && acc) = true then 1#32 else 0#32) ∧
        sf.readReg64 .x23 = outPtr ∧ sf.readReg64 .x26 = recPtr ∧ CalleeSavedVRegsPreserved s sf) := by
  have hfn : libsignalSessionCode.fnOff promoteMatchingSessionName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
  have hbb := black_box_subroutine_ok_ext32 b h_bb
  simp only [CliExt.blackBoxSpec, CliExt.withStack] at hbb; dsimp only [tripleRatchetProgAtExt] at hbb hpc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode overPromoteBin b (Rust.withPanics ext)
    hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0x80 56
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr promoteMatchingSessionName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = alicePtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = 1#64 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = serPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = if acc = true then 1#64 else 0#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = recPtr := hx26
  wp_steps; wp_call hbb (if (k0 == a0) = true then 1#64 else 0#64)
  wp_steps; wp_call hbb (if ((k0 == a0) && acc) = true then 1#64 else 0#64)
  refine SepWP.done (by simp only [*, wp_norm, arm64_norm]) (by simp only [*, wp_norm, arm64_norm])
    ⟨by sep_frame, by simp only [*, wp_norm, arm64_norm], by simp only [*, wp_norm, arm64_norm],
     by simp only [*, wp_norm, arm64_norm], by simp only [*, wp_norm, arm64_norm],
     by simp only [*, wp_norm, arm64_norm], CalleeSavedVRegsPreserved.trans hvregs hvregs_1⟩

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem promote_ct_loop_step_wp_ext32 {b : BitVec 64} {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>" CliExt.blackBoxSpec)
    (recPtr outPtr : BitVec 64) (k0 a0 : BitVec 8) (acc : Bool)
    (m : Nat) (hm_pos : 0 < m) (hm_lt : m + 1 < 2 ^ 64) (serPtr alicePtr : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = alicePtr) (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (m + 1))
    (hx22 : s.readReg64 .x22 = serPtr) (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = if acc = true then 1#64 else 0#64) (hx26 : s.readReg64 .x26 = recPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64) s
      ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0) ∗ stackAt s.sp extHookStack)
      (fun s1 Pf =>
        (Pf ⊢ (serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0) ∗ stackAt s.sp extHookStack) ∧
        s1.trace = s.trace ∧ s1.sp = s.sp ∧
        s1.readReg64 .x19 = alicePtr + 1#64 ∧ s1.readReg64 .x21 = BitVec.ofNat 64 m ∧
        s1.readReg64 .x22 = serPtr + 1#64 ∧ s1.readReg64 .x23 = outPtr ∧
        s1.readReg64 .x25 = (if ((k0 == a0) && acc) = true then 1#64 else 0#64) ∧
        s1.readReg64 .x26 = recPtr ∧ CalleeSavedVRegsPreserved s s1) := by
  have hbr := cond_ne_subs64_one_over (by omega : 1 < m + 1) hm_lt
  have hsub1 : BitVec.ofNat 64 (m + 1) - 1#64 = BitVec.ofNat 64 m := ofNat64_succ_sub_one_over m
  have hfn : libsignalSessionCode.fnOff promoteMatchingSessionName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
  have hbb := black_box_subroutine_ok_ext32 b h_bb
  simp only [CliExt.blackBoxSpec, CliExt.withStack] at hbb; dsimp only [tripleRatchetProgAtExt] at hbb hpc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode overPromoteBin b (Rust.withPanics ext)
    hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0x80 56
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr promoteMatchingSessionName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = alicePtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 (m + 1) := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = serPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = if acc = true then 1#64 else 0#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = recPtr := hx26
  wp_steps; wp_call hbb (if (k0 == a0) = true then 1#64 else 0#64); wp_steps
  refine SepWP.done (by simp only [*, wp_norm, arm64_norm]) (by simp only [*, wp_norm, arm64_norm])
    ⟨by sep_frame, by simp only [*, wp_norm, arm64_norm], by simp only [*, wp_norm, arm64_norm],
     by simp only [*, wp_norm, arm64_norm], by simp only [*, wp_norm, arm64_norm],
     by simp only [*, wp_norm, arm64_norm], by simp only [*, wp_norm, arm64_norm],
     by simp only [*, wp_norm, arm64_norm], by simp only [*, wp_norm, arm64_norm], hvregs⟩

private theorem promote_ct_loop_gen_wp_ext32 {b : BitVec 64} {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>" CliExt.blackBoxSpec)
    (ks as_ : List (BitVec 8)) (acc : Bool)
    (hlen : ks.length = as_.length) (hne : ks ≠ []) (hlt : ks.length < 2 ^ 64)
    (recPtr serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0x80#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = alicePtr) (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ks.length)
    (hx22 : s.readReg64 .x22 = serPtr) (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = if acc = true then 1#64 else 0#64) (hx26 : s.readReg64 .x26 = recPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0xb4#64) s
      ((serPtr ↦ₛ ks) ∗ (alicePtr ↦ₛ as_) ∗ stackAt s.sp extHookStack)
      (fun sf Pf =>
        (Pf ⊢ (serPtr ↦ₛ ks) ∗ (alicePtr ↦ₛ as_) ∗ stackAt s.sp extHookStack) ∧
        sf.trace = s.trace ∧ sf.sp = s.sp ∧
        (sf.readReg64 .x0).setWidth 32 = (if ctBytesEqAcc ks as_ acc = true then 1#32 else 0#32) ∧
        sf.readReg64 .x23 = outPtr ∧ sf.readReg64 .x26 = recPtr ∧ CalleeSavedVRegsPreserved s sf) :=
  ctBytesEq_loop_induct_wp (promote_ct_loop_last_wp_ext32 h_bb recPtr outPtr)
    (promote_ct_loop_step_wp_ext32 h_bb recPtr outPtr)
    ks as_ acc hlen hne hlt serPtr alicePtr s hpc hrun hsp_align hx19 hx21 hx22 hx23 hx25 hx26

/-- Version-miss raw contract on `tripleRatchetProgAtExt b ext` (`extHookStack` framed). -/
theorem promote_matching_session_ver_miss_raw_ok_ext32 {b : BitVec 64}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName)
      promoteMatchingSessionVerMissRawSpecExt :=
  promoteMatchingSessionVerMissRawExt_of_raw promote_matching_session_ver_miss_raw_ok

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 600000 in
/-- Length-miss raw contract under `HookSat ext "subtle::black_box::<u8>" CliExt.blackBoxSpec`. -/
theorem promote_matching_session_len_miss_raw_ok_ext32 {b : BitVec 64}
    {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>" CliExt.blackBoxSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName)
      promoteMatchingSessionLenMissRawSpecExt := by
  have hfn : libsignalSessionCode.fnOff promoteMatchingSessionName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
  have hbb := black_box_subroutine_ok_ext32 b h_bb; simp only [CliExt.blackBoxSpec, CliExt.withStack] at hbb
  refine subroutine_ok_of_sepWP_init
    fun ⟨recPtr, prevPtr, curDiscr, abkPtr, abkLen, sessVer, msgVer, serPtr, outPtr⟩ R s0
      hpc hrun hpre hsp_align => ?_
  dsimp only [promoteMatchingSessionLenMissRawSpecExt, sessionRecordMissPromoteFieldsAt] at hpre ⊢
  refine ⟨_, hpre, ?_⟩
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
  obtain ⟨hx0, hx1, hx2, hx3, hx8, hcur, hver_eq, hlen_ne⟩ := hpure
  have hcmn := cond_eq_adds64_one_false_over hcur
  have hveq_b : ((if (sessVer == 0#32) = true then 2#32 else sessVer) != msgVer.zeroExtend 32) = false := by
    simp only [beq_iff_eq, hver_eq, bne_self_eq_false]
  have hlne_b : (33#64 != abkLen) = true := bne_iff_ne.mpr (fun h33 => hlen_ne h33.symm)
  have hlne_b' : (abkLen != 33#64) = true := bne_iff_ne.mpr hlen_ne
  conv => arg 4; unfold promoteMissStackCellsExt; rw [cells_1184_split_2 s0.sp]
  have hp1 :
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 0xb4#64) s0
        (((recPtr + 0x18#64) ↦₆₄ curDiscr) ∗ ((recPtr + 0x88#64) ↦₆₄ abkLen) ∗
         ((recPtr + 0x160#64) ↦₃₂ sessVer) ∗ stackAt (s0.sp - 1184#64) extHookStack ∗
         (∃∗ w4a0 : BitVec 64, (s0.sp - 1184#64) ↦₆₄ w4a0) ∗
         (∃∗ w470 : BitVec 64, (s0.sp - 1136#64) ↦₆₄ w470) ∗ cells (s0.sp - 96#64) 12)
        (fun s1 P1 =>
          (P1 ⊢ ((recPtr + 0x18#64) ↦₆₄ curDiscr) ∗ ((recPtr + 0x88#64) ↦₆₄ abkLen) ∗
            ((recPtr + 0x160#64) ↦₃₂ sessVer) ∗ stackAt (s0.sp - 1184#64) extHookStack ∗
            ((s0.sp - 1184#64) ↦₆₄ 0#64) ∗ ((s0.sp - 1136#64) ↦₆₄ serPtr) ∗ promoteSavedRegs s0) ∧
          s1.trace = s0.trace ∧ s1.sp = s0.sp - 1184#64 ∧
          (s1.readReg64 .x0).setWidth 32 = 0#32 ∧ s1.readReg64 .x23 = outPtr ∧
          s1.readReg64 .x26 = recPtr ∧ CalleeSavedVRegsPreserved s0 s1) := by
    rw [cells_96_12_eq_over s0.sp]; dsimp only [tripleRatchetProgAtExt] at hbb hpc ⊢
    code_fetches_range CryptoVerification.libsignalSessionCode overPromoteBin b (Rust.withPanics ext)
      hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0 104
    code_fetches_range CryptoVerification.libsignalSessionCode overPromoteBin b (Rust.withPanics ext)
      hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")) 0xa4 20
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr promoteMatchingSessionName = entry
    examples_hide_fetches
    have hx0' : s0.readReg64 (Reg.gpr 0#5) = recPtr := hx0
    have hx1' : s0.readReg64 (Reg.gpr 1#5) = msgVer.zeroExtend 64 := hx1
    have hx2' : s0.readReg64 (Reg.gpr 2#5) = serPtr := hx2
    have hx3' : s0.readReg64 (Reg.gpr 3#5) = 33#64 := hx3
    have hx8' : s0.readReg64 (Reg.gpr 8#5) = outPtr := hx8
    wp_pull_exists; wp_steps; wp_call hbb 0#64
    refine SepWP.done (by simp only [*, wp_norm, arm64_norm]) (by simp only [*, wp_norm, arm64_norm])
      ⟨by unfold promoteSavedRegs; sep_frame, by simp only [*, wp_norm, arm64_norm],
       by simp only [*, wp_norm, arm64_norm], by simp only [*, wp_norm, arm64_norm],
       by simp only [*, wp_norm, arm64_norm], by simp only [*, wp_norm, arm64_norm], hvregs⟩
  apply SepWP.seq
  · exact SepWP.frame_auto hp1
  · intro s1 _ hpc1 hrun1 ⟨hent1, htr1, hsp1, hx0_1, hx23_1, hx26_1, hv1⟩
    refine SepWP.weaken_pre hent1 ?_
    refine SepWP.bind_seq_readOnly (promote_b4_to_ec_wp recPtr outPtr s1 hpc1 hrun1 hx0_1 hx23_1 hx26_1)
      (emp_sepConj _).symm fun s2 hpc2 hrun2 ⟨htr2, hsp2, hx0_2, hx23_2, hv2⟩ => ?_
    have hv_20 : CalleeSavedVRegsPreserved s0 s2 :=
      CalleeSavedVRegsPreserved.trans hv1 (by simp [CalleeSavedVRegsPreserved, calleeSavedVRegs, hv2])
    refine SepWP.focus_weaken (cells_1184_merge_2 s0.sp 0#64 serPtr) (by sep_focus) ?_
    conv => arg 4; rw [stackAt_inner_extHookStack_eq s0.sp]
    refine SepWP.mono (SepWP.frame_auto (promote_miss_from_ec_wp s0 s2 recPtr prevPtr outPtr hpc2 hrun2
      hsp_align' (htr2.trans htr1) (hsp2.trans hsp1) hx0_2 hx23_2 hv_20)) ?_ (fun _ _ _ hf => hf)
    intro sf _ _ _ ⟨hentf, htrf, hspf, hcsf⟩
    exact ⟨fun hm => Satisfies.mono (sepConj_mono_left
      (Entails.trans hentf (by rw [htrf, promoteMissStackCellsExt_eq s0.sp]; sep_frame))) hm, hspf, hcsf⟩

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 600000 in
/-- Key-miss raw contract under `HookSat ext "subtle::black_box::<u8>" CliExt.blackBoxSpec`. -/
theorem promote_matching_session_key_miss_raw_ok_ext32 {b : BitVec 64}
    {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>" CliExt.blackBoxSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName)
      promoteMatchingSessionKeyMissRawSpecExt := by
  refine subroutine_ok_of_sepWP_init
    fun ⟨recPtr, prevPtr, curDiscr, abkPtr, sessVer, msgVer, serPtr, outPtr, serBytes, ak⟩ R s0
      hpc hrun hpre hsp_align => ?_
  dsimp only [promoteMatchingSessionKeyMissRawSpecExt, sessionRecordMissPromoteFieldsAt] at hpre ⊢
  refine ⟨_, hpre, ?_⟩
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
  obtain ⟨hx0, hx1, hx2, hx3, hx8, hcur, hver_eq, hklen, halen, hne⟩ := hpure
  have hacc_false : ctBytesEqAcc serBytes ak true = false :=
    ctBytesEqAcc_true_of_ne (hklen.trans halen.symm) hne
  conv => arg 4; unfold promoteMissStackCellsExt; rw [cells_1184_split_2 s0.sp]
  apply SepWP.seq
  · exact SepWP.frame_auto (promote_key_miss_seg1_wp s0 recPtr curDiscr abkPtr serPtr outPtr sessVer msgVer
      hpc hrun hsp_align' hx0 hx1 hx2 hx3 hx8 hcur hver_eq)
  · intro s1 _ hpc1 hrun1 ⟨hent1, htr1, hsp1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hv1⟩
    refine SepWP.weaken_pre hent1 ?_
    have hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true := by
      rw [hsp1, sp_sub_1184_align_over]; exact hsp_align'
    have hloop := promote_ct_loop_gen_wp_ext32 h_bb serBytes ak true (hklen.trans halen.symm)
      (by intro hn; rw [hn] at hklen; simp at hklen) (by rw [hklen]; decide)
      recPtr serPtr abkPtr outPtr s1 hpc1 hrun1 hsp_align1 hx19_1
      (by rw [hklen]; exact hx21_1) hx22_1 hx23_1 hx25_1 hx26_1
    rw [hacc_false] at hloop; simp only [Bool.false_eq_true, ↓reduceIte] at hloop
    conv => arg 4; rw [← hsp1]
    apply SepWP.seq
    · exact SepWP.frame_auto hloop
    · intro s2 _ hpc2 hrun2 ⟨hent2, htr2, hsp2, hx0_2, hx23_2, hx26_2, hv2⟩
      refine SepWP.weaken_pre hent2 ?_; conv => arg 4; rw [hsp1]
      refine SepWP.bind_seq_readOnly (promote_b4_to_ec_wp recPtr outPtr s2 hpc2 hrun2 hx0_2 hx23_2 hx26_2)
        (emp_sepConj _).symm fun s3 hpc3 hrun3 ⟨htr3, hsp3, hx0_3, hx23_3, hv3⟩ => ?_
      have hv_30 : CalleeSavedVRegsPreserved s0 s3 :=
        CalleeSavedVRegsPreserved.trans (by simp [CalleeSavedVRegsPreserved, calleeSavedVRegs, hv1])
          (CalleeSavedVRegsPreserved.trans hv2 (by simp [CalleeSavedVRegsPreserved, calleeSavedVRegs, hv3]))
      refine SepWP.focus_weaken (cells_1184_merge_2 s0.sp 0#64 serPtr) (by sep_focus) ?_
      conv => arg 4; rw [stackAt_inner_extHookStack_eq s0.sp]
      refine SepWP.mono (SepWP.frame_auto (promote_miss_from_ec_wp s0 s3 recPtr prevPtr outPtr hpc3 hrun3
        hsp_align' (htr3.trans (htr2.trans htr1)) (hsp3.trans (hsp2.trans hsp1)) hx0_3 hx23_3 hv_30)) ?_
        (fun _ _ _ hf => hf)
      intro sf _ _ _ ⟨hentf, htrf, hspf, hcsf⟩
      exact ⟨fun hm => Satisfies.mono (sepConj_mono_left
        (Entails.trans hentf (by rw [htrf, promoteMissStackCellsExt_eq s0.sp]; sep_frame))) hm, hspf, hcsf⟩

/-- Tight (`promoteMatchingSessionMatchStackExt = 17568` B) record-over miss theorem. -/
theorem promote_matching_session_record_over_matchStack_ok_ext32 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>" CliExt.blackBoxSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName)
      (promoteMatchingSessionRecordOverMatchStackSpecExt A) :=
  promoteMatchingSessionRecordOverMatchStackExt_of_raw A promote_matching_session_ver_miss_raw_ok_ext32
    (promote_matching_session_len_miss_raw_ok_ext32 h_bb) (promote_matching_session_key_miss_raw_ok_ext32 h_bb)

/-- Record-over miss theorem (`p2PromoteMissStackExt = 17632` B) under `CliExt.blackBoxSpec`. -/
theorem promote_matching_session_record_over_ok_ext32 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>" CliExt.blackBoxSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName)
      (promoteMatchingSessionRecordOverSpecExt A) :=
  promoteMatchingSessionRecordOverExt_of_matchStack
    (promote_matching_session_record_over_matchStack_ok_ext32 (A := A) h_bb)

/-- Tight (`promoteMatchingSessionMatchStackExt = 17568` B) miss theorem under `CliExt.blackBoxSpec`. -/
theorem promote_matching_session_miss_matchStack_ok_ext32 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>" CliExt.blackBoxSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName)
      (promoteMatchingSessionMissMatchStackSpecExt A) :=
  promoteMatchingSessionMissMatchStackExt_of_recordOver
    (promote_matching_session_record_over_matchStack_ok_ext32 (A := A) h_bb)

/-- Public `promoteMatchingSessionMissSpecExt` (`p2PromoteMissStackExt = 17632` B) theorem. -/
theorem promote_matching_session_miss_ok_ext32 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>" CliExt.blackBoxSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName)
      (promoteMatchingSessionMissSpecExt A) :=
  promoteMatchingSessionMissExt_of_matchStack
    (promote_matching_session_miss_matchStack_ok_ext32 (A := A) h_bb)

/-! ## 9. Relocatable `[LibsignalPlacement]` Proofs -/

section Placed

open Arm64.Obj ProofLib.GenPlacedFetches

private theorem externAt?_black_box_placed [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    ((blkPC_50).rebase (blkPl_50).base H).externAt? (lsρ lsBlackBoxU8Sym) =
      some blackBoxHook :=
  (ls_externAt?_of_mem (prog := (blkPC_50).rebase (blkPl_50).base H) (sym := lsBlackBoxU8Sym)).trans h_bb

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 600000 in
private theorem promote_miss_from_ec_placed_wp [LibsignalPlacement] {H : LibsignalHooks}
    (s0 s2 : State) (recPtr prevPtr outPtr : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s2.mem)
    (hpc : s2.pc = (blkPl_50).base + 0xec#64)
    (hrun : s2.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : s2.trace = s0.trace)
    (hsp : s2.sp = s0.sp - 1184#64)
    (hx0 : s2.readReg64 .x0 = recPtr)
    (hx23 : s2.readReg64 .x23 = outPtr)
    (hvregs : s2.vregs = s0.vregs) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H) (s0.readReg64 .x30) s2
      (((recPtr + 8#64) ↦₆₄ prevPtr) ∗
       ((recPtr + 16#64) ↦₆₄ 0#64) ∗
       (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
       (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
       cells (s0.sp - 1248#64) 8 ∗
       cells (s0.sp - 1184#64) 10 ∗
       (∃∗ w2e0 : BitVec 64, (s0.sp - 448#64) ↦₆₄ w2e0) ∗
       promoteSavedRegs s0)
      (fun sf Pf =>
        (Pf ⊢
          ((recPtr + 8#64) ↦₆₄ prevPtr) ∗
          ((recPtr + 16#64) ↦₆₄ 0#64) ∗
          (outPtr ↦₆₄ 0#64) ∗
          ((outPtr + 8#64) ↦₈ 0#8) ∗
          promoteMissStackCells s0.sp) ∧
        sf.trace = s0.trace ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf) := by
  unfold promoteSavedRegs promoteMissStackCells
  have hiter := ls_subroutine_ok_of_block
    (callerProg := (blkPC_50).rebase (blkPl_50).base H) (entry := lsmpl.base 83)
    (subroutine_ok_withLsCodeLoaded_of_plain (map_iter_next_empty_placed_ok H))
  cells_unfold_over
  simp only [withLsCodeLoaded, mapIterNextEmptySpec, cells, sepConj_emp, sepExists_sepConj_right,
    bv_sub_add_lit, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub] at hiter
  have hx0' : s2.readReg64 (Reg.gpr 0#5) = recPtr := hx0
  have hx23' : s2.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  wp_pull_exists
  wp_steps_lscl (lsmpl.base 83)
  wp_call hiter (s0.sp - 448#64, s0.sp - 1128#64, prevPtr)
  wp_steps
  refine SepWP.done (by simp only [hsp, wp_norm, arm64_norm])
    (by simp only [hrun_sf, wp_norm, arm64_norm])
    ⟨?_, by simp only [htr, hpost, wp_norm, arm64_norm],
     by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
     ⟨by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
      by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
      by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
      by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
      by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
      by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
      by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
      by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
      by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
      by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
      by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
      by simp only [CalleeSavedVRegsPreserved, calleeSavedVRegs, wp_norm, arm64_norm] at hvregs_1 ⊢
         rw [hvregs_1, hvregs]⟩⟩
  sep_frame

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem promote_ct_loop_last_placed_wp [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (k0 a0 : BitVec 8) (acc : Bool)
    (recPtr serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (blkPl_50).base + 0x80#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = 1#64)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = if acc = true then 1#64 else 0#64)
    (hx26 : s.readReg64 .x26 = recPtr) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H) ((blkPl_50).base + 0xb4#64) s
      ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0))
      (fun sf Pf =>
        Pf = ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0)) ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = (if ((k0 == a0) && acc) = true then 1#64 else 0#64) ∧
        sf.readReg64 .x23 = outPtr ∧
        sf.readReg64 .x26 = recPtr ∧
        sf.vregs = s.vregs) := by
  have hext := externAt?_black_box_placed h_bb
  have hx19' : s.readReg64 (Reg.gpr 19#5) = alicePtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = 1#64 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = serPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = if acc = true then 1#64 else 0#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = recPtr := hx26
  wp_steps
  wp_black_box_over hext
  wp_steps
  wp_black_box_over hext
  refine SepWP.done (by simp only [hpc, hx21', wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm])
    ⟨rfl, by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [hx25', wp_norm, arm64_norm], by simp only [hx23', wp_norm, arm64_norm],
     by simp only [hx26', wp_norm, arm64_norm], rfl⟩

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem promote_ct_loop_step_placed_wp [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (k0 a0 : BitVec 8) (acc : Bool) (m : Nat) (hm_pos : 0 < m) (hm_lt : m + 1 < 2 ^ 64)
    (recPtr serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (blkPl_50).base + 0x80#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (m + 1))
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = if acc = true then 1#64 else 0#64)
    (hx26 : s.readReg64 .x26 = recPtr) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H) ((blkPl_50).base + 0x80#64) s
      ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0))
      (fun s1 Pf =>
        Pf = ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0)) ∧
        s1.trace = s.trace ∧
        s1.sp = s.sp ∧
        s1.readReg64 .x19 = alicePtr + 1#64 ∧
        s1.readReg64 .x21 = BitVec.ofNat 64 m ∧
        s1.readReg64 .x22 = serPtr + 1#64 ∧
        s1.readReg64 .x23 = outPtr ∧
        s1.readReg64 .x25 = (if ((k0 == a0) && acc) = true then 1#64 else 0#64) ∧
        s1.readReg64 .x26 = recPtr ∧
        s1.vregs = s.vregs) := by
  have hgt : 1 < m + 1 := by omega
  have hbr := cond_ne_subs64_one_over hgt hm_lt
  have hsub1 : BitVec.ofNat 64 (m + 1) - 1#64 = BitVec.ofNat 64 m := ofNat64_succ_sub_one_over m
  have hext := externAt?_black_box_placed h_bb
  have hx19' : s.readReg64 (Reg.gpr 19#5) = alicePtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 (m + 1) := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = serPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = if acc = true then 1#64 else 0#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = recPtr := hx26
  wp_steps
  wp_black_box_over hext
  wp_steps
  refine SepWP.done (by simp only [hpc, hx21', hbr, wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm])
    ⟨rfl, by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [hx19', wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm, hx21', hsub1],
     by simp only [hx22', wp_norm, arm64_norm],
     by simp only [hx23', wp_norm, arm64_norm],
     by simp only [hx25', wp_norm, arm64_norm],
     by simp only [hx26', wp_norm, arm64_norm],
     rfl⟩

set_option maxHeartbeats 400000 in
private theorem promote_ct_loop_gen_placed_wp [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (ks as_ : List (BitVec 8)) (acc : Bool)
    (hlen : ks.length = as_.length) (hne : ks ≠ []) (hlt : ks.length < 2 ^ 64)
    (recPtr serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (blkPl_50).base + 0x80#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ks.length)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = if acc = true then 1#64 else 0#64)
    (hx26 : s.readReg64 .x26 = recPtr) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H) ((blkPl_50).base + 0xb4#64) s
      ((serPtr ↦ₛ ks) ∗ (alicePtr ↦ₛ as_))
      (fun sf Pf =>
        Pf = ((serPtr ↦ₛ ks) ∗ (alicePtr ↦ₛ as_)) ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = (if ctBytesEqAcc ks as_ acc = true then 1#64 else 0#64) ∧
        sf.readReg64 .x23 = outPtr ∧
        sf.readReg64 .x26 = recPtr ∧
        sf.vregs = s.vregs) := by
  induction ks generalizing as_ acc serPtr alicePtr s with
  | nil => exact absurd rfl hne
  | cons k0 krest ih =>
    cases as_ with
    | nil => simp at hlen
    | cons a0 arest =>
      have hlen' : krest.length = arest.length := by simpa using hlen
      cases krest with
      | nil =>
        cases arest with
        | nil =>
          dsimp only [List.length_cons, List.length_nil, ctBytesEqAcc] at hx21 ⊢
          have hpre_eq : ((serPtr ↦ₛ [k0]) ∗ (alicePtr ↦ₛ [a0])) =
              ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0)) := by
            rw [pointsToBytes_cons, pointsToBytes_nil, pointsToBytes_cons, pointsToBytes_nil,
              sepConj_emp, sepConj_emp]
          rw [hpre_eq]
          exact promote_ct_loop_last_placed_wp h_bb k0 a0 acc recPtr serPtr alicePtr outPtr s
            hpc hrun hx19 hx21 hx22 hx23 hx25 hx26
        | cons _ _ => simp at hlen'
      | cons k1 krest' =>
        cases arest with
        | nil => simp at hlen'
        | cons a1 arest' =>
          have hm_pos : 0 < (k1 :: krest').length := by simp
          have hm_lt : (k1 :: krest').length + 1 < 2 ^ 64 := by simpa using hlt
          have hlt' : (k1 :: krest').length < 2 ^ 64 := by omega
          dsimp only [List.length_cons] at hx21
          conv =>
            arg 4
            rw [pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]
            simp only [sepConj_assoc]
          refine SepWP.bind_seq_readOnly
            (promote_ct_loop_step_placed_wp h_bb k0 a0 acc (k1 :: krest').length hm_pos hm_lt
              recPtr serPtr alicePtr outPtr s hpc hrun hx19 hx21 hx22 hx23 hx25 hx26)
            (by sep_focus)
            fun s1 hpc1 hrun1 ⟨htr1, hsp1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hv1⟩ => ?_
          refine SepWP.bind_seq_readOnly
            (ih (a1 :: arest') ((k0 == a0) && acc) hlen' (by simp) hlt'
              (serPtr + 1#64) (alicePtr + 1#64) s1 hpc1 hrun1 hx19_1 hx21_1 hx22_1 hx23_1 hx25_1 hx26_1)
            (by sep_focus)
            fun sf hpcf hrunf ⟨htrf, hspf, hx0_f, hx23_f, hx26_f, hv_f⟩ => ?_
          refine SepWP.done hpcf hrunf
            ⟨?_, htrf.trans htr1, hspf.trans hsp1, hx0_f, hx23_f, hx26_f, hv_f.trans hv1⟩
          rw [pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]
          ac_rfl

private theorem sepWP_add_lscl {prog : Program} {tgt : BitVec 64} {s : State} {P : SepProp}
    {pl : MultiPlacement} {Q : State → SepProp → Prop} {R : State → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog tgt s P (fun sf Pf => Q sf Pf ∧ R sf)) :
    SepWP prog tgt s P (fun sf Pf => Q sf Pf ∧ LibsignalCodeLoaded pl sf.mem ∧ R sf) :=
  sepWP_mono_lscl hcl h (fun _ _ _ _ hcl1 ⟨hq, hr⟩ => ⟨hq, hcl1, hr⟩)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 600000 in
theorem promote_matching_session_ver_miss_raw_placed_ok [LibsignalPlacement] {H : LibsignalHooks} :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
      (withLsCodeLoaded lsmpl promoteMatchingSessionVerMissRawSpec) := by
  refine subroutine_ok_of_sepWP_init
    fun ⟨recPtr, prevPtr, curDiscr, abkPtr, abkLen, sessVer, msgVer, serPtr, outPtr⟩ R s0
      hpc hrun hpre hsp_align => ?_
  have ⟨hcl0, hpre'⟩ := extract_withLsCodeLoaded hpre
  dsimp only [promoteMatchingSessionVerMissRawSpec, sessionRecordMissPromoteFieldsAt] at hpre'
  dsimp only [withLsCodeLoaded, promoteMatchingSessionVerMissRawSpec, sessionRecordMissPromoteFieldsAt]
  refine ⟨_, hpre', ?_⟩
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
  obtain ⟨hx0, hx1, hx2, hx3, hx8, hcur, hver_ne⟩ := hpure
  have hcmn := cond_eq_adds64_one_false_over hcur
  have hvne_b : ((if (sessVer == 0#32) = true then 2#32 else sessVer) != msgVer.zeroExtend 32) = true := by
    simp only [beq_iff_eq, bne_iff_ne]
    exact hver_ne
  conv => arg 4; unfold promoteMissStackCells; rw [cells_1184_split_2 s0.sp]
  have hp1 :
      SepWP ((blkPC_50).rebase (blkPl_50).base H) ((blkPl_50).base + 0xec#64) s0
        (((recPtr + 0x18#64) ↦₆₄ curDiscr) ∗
         ((recPtr + 0x160#64) ↦₃₂ sessVer) ∗
         (∃∗ w4a0 : BitVec 64, (s0.sp - 1184#64) ↦₆₄ w4a0) ∗
         (∃∗ w470 : BitVec 64, (s0.sp - 1136#64) ↦₆₄ w470) ∗
         cells (s0.sp - 96#64) 12)
        (fun s1 P1 =>
          (P1 ⊢ ((recPtr + 0x18#64) ↦₆₄ curDiscr) ∗ ((recPtr + 0x160#64) ↦₃₂ sessVer) ∗
            ((s0.sp - 1184#64) ↦₆₄ 0#64) ∗ ((s0.sp - 1136#64) ↦₆₄ serPtr) ∗ promoteSavedRegs s0) ∧
          LibsignalCodeLoaded lsmpl s1.mem ∧
          s1.trace = s0.trace ∧ s1.sp = s0.sp - 1184#64 ∧
          s1.readReg64 .x0 = recPtr ∧ s1.readReg64 .x23 = outPtr ∧ s1.vregs = s0.vregs) := by
    apply sepWP_add_lscl hcl0
    rw [cells_96_12_eq_over s0.sp]
    have hx0' : s0.readReg64 (Reg.gpr 0#5) = recPtr := hx0
    have hx1' : s0.readReg64 (Reg.gpr 1#5) = msgVer.zeroExtend 64 := hx1
    have hx2' : s0.readReg64 (Reg.gpr 2#5) = serPtr := hx2
    have hx8' : s0.readReg64 (Reg.gpr 8#5) = outPtr := hx8
    wp_pull_exists
    wp_steps
    refine SepWP.done (by simp only [hpc, hcmn, hvne_b, wp_norm, arm64_norm])
      (by simp only [hrun, wp_norm, arm64_norm])
      ⟨?_, by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
       by simp only [hx0', wp_norm, arm64_norm], by simp only [hx8', wp_norm, arm64_norm], rfl⟩
    unfold promoteSavedRegs
    sep_frame
  apply SepWP.seq
  · exact SepWP.frame_auto hp1
  · intro s1 _ hpc1 hrun1 ⟨hent1, hcl1, htr1, hsp1, hx0_1, hx23_1, hv1⟩
    refine SepWP.weaken_pre hent1 ?_
    refine SepWP.focus_weaken (cells_1184_merge_2 s0.sp 0#64 serPtr) (by sep_focus) ?_
    apply SepWP.mono
    · exact SepWP.frame_auto
        (promote_miss_from_ec_placed_wp s0 s1 recPtr prevPtr outPtr hcl1 hpc1 hrun1 hsp_align' htr1 hsp1 hx0_1 hx23_1 hv1)
    · intro sf _ _ _ ⟨hentf, htrf, hspf, hcsf⟩
      refine ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm, hspf, hcsf⟩
      refine Entails.trans hentf ?_
      rw [htrf]
      sep_frame
    · intro _ _ _ hf; exact hf

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 600000 in
theorem promote_matching_session_len_miss_raw_placed_ok [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
      (withLsCodeLoaded lsmpl promoteMatchingSessionLenMissRawSpec) := by
  have hext := externAt?_black_box_placed h_bb
  refine subroutine_ok_of_sepWP_init
    fun ⟨recPtr, prevPtr, curDiscr, abkPtr, abkLen, sessVer, msgVer, serPtr, outPtr⟩ R s0
      hpc hrun hpre hsp_align => ?_
  have ⟨hcl0, hpre'⟩ := extract_withLsCodeLoaded hpre
  dsimp only [promoteMatchingSessionLenMissRawSpec, sessionRecordMissPromoteFieldsAt] at hpre'
  dsimp only [withLsCodeLoaded, promoteMatchingSessionLenMissRawSpec, sessionRecordMissPromoteFieldsAt]
  refine ⟨_, hpre', ?_⟩
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
  obtain ⟨hx0, hx1, hx2, hx3, hx8, hcur, hver_eq, hlen_ne⟩ := hpure
  have hcmn := cond_eq_adds64_one_false_over hcur
  have hveq_b : ((if (sessVer == 0#32) = true then 2#32 else sessVer) != msgVer.zeroExtend 32) = false := by
    simp only [beq_iff_eq, hver_eq, bne_self_eq_false]
  have hlne_b : (33#64 != abkLen) = true := bne_iff_ne.mpr (fun h33 => hlen_ne h33.symm)
  have hlne_b' : (abkLen != 33#64) = true := bne_iff_ne.mpr hlen_ne
  conv => arg 4; unfold promoteMissStackCells; rw [cells_1184_split_2 s0.sp]
  have hp1 :
      SepWP ((blkPC_50).rebase (blkPl_50).base H) ((blkPl_50).base + 0xec#64) s0
        (((recPtr + 0x18#64) ↦₆₄ curDiscr) ∗
         ((recPtr + 0x88#64) ↦₆₄ abkLen) ∗
         ((recPtr + 0x160#64) ↦₃₂ sessVer) ∗
         (∃∗ w4a0 : BitVec 64, (s0.sp - 1184#64) ↦₆₄ w4a0) ∗
         (∃∗ w470 : BitVec 64, (s0.sp - 1136#64) ↦₆₄ w470) ∗
         cells (s0.sp - 96#64) 12)
        (fun s1 P1 =>
          (P1 ⊢ ((recPtr + 0x18#64) ↦₆₄ curDiscr) ∗ ((recPtr + 0x88#64) ↦₆₄ abkLen) ∗
            ((recPtr + 0x160#64) ↦₃₂ sessVer) ∗
            ((s0.sp - 1184#64) ↦₆₄ 0#64) ∗ ((s0.sp - 1136#64) ↦₆₄ serPtr) ∗ promoteSavedRegs s0) ∧
          LibsignalCodeLoaded lsmpl s1.mem ∧
          s1.trace = s0.trace ∧ s1.sp = s0.sp - 1184#64 ∧
          s1.readReg64 .x0 = recPtr ∧ s1.readReg64 .x23 = outPtr ∧ s1.vregs = s0.vregs) := by
    apply sepWP_add_lscl hcl0
    rw [cells_96_12_eq_over s0.sp]
    have hx0' : s0.readReg64 (Reg.gpr 0#5) = recPtr := hx0
    have hx1' : s0.readReg64 (Reg.gpr 1#5) = msgVer.zeroExtend 64 := hx1
    have hx2' : s0.readReg64 (Reg.gpr 2#5) = serPtr := hx2
    have hx3' : s0.readReg64 (Reg.gpr 3#5) = 33#64 := hx3
    have hx8' : s0.readReg64 (Reg.gpr 8#5) = outPtr := hx8
    wp_pull_exists
    wp_steps
    wp_black_box_over hext
    wp_steps
    refine SepWP.done (by simp only [hpc, hcmn, hveq_b, hlne_b, hlne_b', hx3', wp_norm, arm64_norm])
      (by simp only [hrun, wp_norm, arm64_norm])
      ⟨?_, by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
       by simp only [hx0', wp_norm, arm64_norm], by simp only [hx8', wp_norm, arm64_norm], rfl⟩
    unfold promoteSavedRegs
    sep_frame
  apply SepWP.seq
  · exact SepWP.frame_auto hp1
  · intro s1 _ hpc1 hrun1 ⟨hent1, hcl1, htr1, hsp1, hx0_1, hx23_1, hv1⟩
    refine SepWP.weaken_pre hent1 ?_
    refine SepWP.focus_weaken (cells_1184_merge_2 s0.sp 0#64 serPtr) (by sep_focus) ?_
    apply SepWP.mono
    · exact SepWP.frame_auto
        (promote_miss_from_ec_placed_wp s0 s1 recPtr prevPtr outPtr hcl1 hpc1 hrun1 hsp_align' htr1 hsp1 hx0_1 hx23_1 hv1)
    · intro sf _ _ _ ⟨hentf, htrf, hspf, hcsf⟩
      refine ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm, hspf, hcsf⟩
      refine Entails.trans hentf ?_
      rw [htrf]
      sep_frame
    · intro _ _ _ hf; exact hf

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 600000 in
theorem promote_matching_session_key_miss_raw_placed_ok [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
      (withLsCodeLoaded lsmpl promoteMatchingSessionKeyMissRawSpec) := by
  refine subroutine_ok_of_sepWP_init
    fun ⟨recPtr, prevPtr, curDiscr, abkPtr, sessVer, msgVer, serPtr, outPtr, serBytes, ak⟩ R s0
      hpc hrun hpre hsp_align => ?_
  have ⟨hcl0, hpre'⟩ := extract_withLsCodeLoaded hpre
  dsimp only [promoteMatchingSessionKeyMissRawSpec, sessionRecordMissPromoteFieldsAt] at hpre'
  dsimp only [withLsCodeLoaded, promoteMatchingSessionKeyMissRawSpec, sessionRecordMissPromoteFieldsAt]
  refine ⟨_, hpre', ?_⟩
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
  obtain ⟨hx0, hx1, hx2, hx3, hx8, hcur, hver_eq, hklen, halen, hne⟩ := hpure
  have hcmn := cond_eq_adds64_one_false_over hcur
  have hveq_b : ((if (sessVer == 0#32) = true then 2#32 else sessVer) != msgVer.zeroExtend 32) = false := by
    simp only [beq_iff_eq, hver_eq, bne_self_eq_false]
  have hacc_false : ctBytesEqAcc serBytes ak true = false :=
    ctBytesEqAcc_true_of_ne (hklen.trans halen.symm) hne
  conv => arg 4; unfold promoteMissStackCells; rw [cells_1184_split_2 s0.sp]
  have hp1 :
      SepWP ((blkPC_50).rebase (blkPl_50).base H) ((blkPl_50).base + 0x80#64) s0
        (((recPtr + 0x18#64) ↦₆₄ curDiscr) ∗
         ((recPtr + 0x80#64) ↦₆₄ abkPtr) ∗
         ((recPtr + 0x88#64) ↦₆₄ 33#64) ∗
         ((recPtr + 0x160#64) ↦₃₂ sessVer) ∗
         (∃∗ w4a0 : BitVec 64, (s0.sp - 1184#64) ↦₆₄ w4a0) ∗
         (∃∗ w470 : BitVec 64, (s0.sp - 1136#64) ↦₆₄ w470) ∗
         cells (s0.sp - 96#64) 12)
        (fun s1 P1 =>
          (P1 ⊢ ((recPtr + 0x18#64) ↦₆₄ curDiscr) ∗ ((recPtr + 0x80#64) ↦₆₄ abkPtr) ∗
            ((recPtr + 0x88#64) ↦₆₄ 33#64) ∗ ((recPtr + 0x160#64) ↦₃₂ sessVer) ∗
            ((s0.sp - 1184#64) ↦₆₄ 0#64) ∗ ((s0.sp - 1136#64) ↦₆₄ serPtr) ∗ promoteSavedRegs s0) ∧
          LibsignalCodeLoaded lsmpl s1.mem ∧
          s1.trace = s0.trace ∧ s1.sp = s0.sp - 1184#64 ∧
          s1.readReg64 .x19 = abkPtr ∧ s1.readReg64 .x21 = 33#64 ∧
          s1.readReg64 .x22 = serPtr ∧ s1.readReg64 .x23 = outPtr ∧
          s1.readReg64 .x25 = 1#64 ∧ s1.readReg64 .x26 = recPtr ∧ s1.vregs = s0.vregs) := by
    apply sepWP_add_lscl hcl0
    rw [cells_96_12_eq_over s0.sp]
    have hx0' : s0.readReg64 (Reg.gpr 0#5) = recPtr := hx0
    have hx1' : s0.readReg64 (Reg.gpr 1#5) = msgVer.zeroExtend 64 := hx1
    have hx2' : s0.readReg64 (Reg.gpr 2#5) = serPtr := hx2
    have hx3' : s0.readReg64 (Reg.gpr 3#5) = 33#64 := hx3
    have hx8' : s0.readReg64 (Reg.gpr 8#5) = outPtr := hx8
    wp_pull_exists
    wp_steps
    refine SepWP.done (by simp only [hpc, hcmn, hveq_b, hx3', wp_norm, arm64_norm])
      (by simp only [hrun, wp_norm, arm64_norm])
      ⟨?_, by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
       by simp only [hx0', wp_norm, arm64_norm], by simp only [hx3', wp_norm, arm64_norm],
       by simp only [hx2', wp_norm, arm64_norm], by simp only [hx8', wp_norm, arm64_norm],
       by simp only [wp_norm, arm64_norm], by simp only [hx0', wp_norm, arm64_norm], rfl⟩
    unfold promoteSavedRegs
    sep_frame
  apply SepWP.seq
  · exact SepWP.frame_auto hp1
  · intro s1 _ hpc1 hrun1 ⟨hent1, hcl1, htr1, hsp1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hv1⟩
    refine SepWP.weaken_pre hent1 ?_
    have hloop := promote_ct_loop_gen_placed_wp h_bb serBytes ak true (hklen.trans halen.symm)
      (by intro hn; rw [hn] at hklen; simp at hklen) (by rw [hklen]; decide)
      recPtr serPtr abkPtr outPtr s1 hpc1 hrun1 hx19_1
      (by rw [hklen]; exact hx21_1) hx22_1 hx23_1 hx25_1 hx26_1
    rw [hacc_false] at hloop
    simp only [Bool.false_eq_true, ↓reduceIte] at hloop
    have hloop_cl := sepWP_add_lscl hcl1 hloop
    refine SepWP.bind_seq_readOnly hloop_cl (by sep_focus)
      fun s2 hpc2 hrun2 ⟨hcl2, htr2, hsp2, hx0_2, hx23_2, hx26_2, hv2⟩ => ?_
    have hp3 :
        SepWP ((blkPC_50).rebase (blkPl_50).base H) ((blkPl_50).base + 0xec#64) s2 emp
          (fun s3 P3 =>
            P3 = emp ∧ LibsignalCodeLoaded lsmpl s3.mem ∧
            s3.trace = s2.trace ∧ s3.sp = s2.sp ∧
            s3.readReg64 .x0 = recPtr ∧ s3.readReg64 .x23 = outPtr ∧ s3.vregs = s2.vregs) := by
      apply sepWP_add_lscl hcl2
      have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
      have hx23_2' : s2.readReg64 (Reg.gpr 23#5) = outPtr := hx23_2
      have hx26_2' : s2.readReg64 (Reg.gpr 26#5) = recPtr := hx26_2
      wp_steps
      exact SepWP.done (by simp only [hpc2, hx0_2', wp_norm, arm64_norm])
        (by simp only [hrun2, wp_norm, arm64_norm])
        ⟨rfl, by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
         by simp only [hx26_2', wp_norm, arm64_norm], by simp only [hx23_2', wp_norm, arm64_norm], rfl⟩
    refine SepWP.bind_seq_readOnly hp3 (emp_sepConj _).symm
      fun s3 hpc3 hrun3 ⟨hcl3, htr3, hsp3, hx0_3, hx23_3, hv3⟩ => ?_
    have htr_30 : s3.trace = s0.trace := htr3.trans (htr2.trans htr1)
    have hsp_30 : s3.sp = s0.sp - 1184#64 := hsp3.trans (hsp2.trans hsp1)
    have hv_30 : s3.vregs = s0.vregs := hv3.trans (hv2.trans hv1)
    refine SepWP.focus_weaken (cells_1184_merge_2 s0.sp 0#64 serPtr) (by sep_focus) ?_
    apply SepWP.mono
    · exact SepWP.frame_auto
        (promote_miss_from_ec_placed_wp s0 s3 recPtr prevPtr outPtr hcl3 hpc3 hrun3 hsp_align' htr_30 hsp_30 hx0_3 hx23_3 hv_30)
    · intro sf _ _ _ ⟨hentf, htrf, hspf, hcsf⟩
      refine ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm, hspf, hcsf⟩
      refine Entails.trans hentf ?_
      rw [htrf]
      sep_frame
    · intro _ _ _ hf; exact hf

private theorem subroutine_ok_withLsCodeLoaded_refine_frame {α β : Type}
    {prog : Program} {entry : BitVec 64} {pl : MultiPlacement}
    {inner : Spec α} {outer : Spec β}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl inner))
    (href : ∀ (x : β) (R : SepProp) (s0 : State),
      (s0.mem ⊨ outer.pre x s0 ∗ R) →
      ∃ (y : α) (F : SepProp),
        (s0.mem ⊨ inner.pre y s0 ∗ (F ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ inner.post y s0 sf ∗ (F ∗ R)) →
          (sf.mem ⊨ outer.post x s0 sf ∗ R)))
    (hpanic : ∀ y R (s0 sf : State), ¬ (sf.mem ⊨ inner.onPanic y s0 sf ∗ R) := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (hexit : ∀ y code R (s0 sf : State), ¬ (sf.mem ⊨ inner.onExit y code s0 sf ∗ R) := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ x y F R (s0 sf : State),
      (sf.mem ⊨ inner.onOom y s0 sf ∗ (F ∗ R)) → (sf.mem ⊨ outer.onOom x s0 sf ∗ R) := by
      intro _ _ _ _ _ _ ho; first
        | exact ho
        | exact False.elim (not_satisfies_false_sepConj ho)
        | exact satisfies_true_sepConj _ _) :
    subroutine_ok prog entry (withLsCodeLoaded pl outer) := by
  refine subroutine_ok_refine_frame h (fun x R s0 hpre => ?_) hpanic hexit hoom
  have ⟨hcl0, hpre'⟩ := extract_withLsCodeLoaded hpre
  obtain ⟨y, F, hy_pre, hy_post⟩ := href x R s0 hpre'
  refine ⟨y, F, ?_, hy_post⟩
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hcl0, hy_pre⟩

set_option maxHeartbeats 600000 in
theorem promote_matching_session_record_over_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
      (withLsCodeLoaded lsmpl (promoteMatchingSessionRecordOverSpec A)) := by
  refine subroutine_ok_by_cases
    (fun (x : BitVec 64 × BitVec 64 × BitVec 64 × SessionGhost × Session (List (BitVec 8)) ×
      BitVec 8 × BitVec 64 × BitVec 64 × List (BitVec 8)) =>
        x.2.2.2.2.1.state.version = x.2.2.2.2.2.1.zeroExtend 32) ?_ ?_
  · refine subroutine_ok_by_cases
      (fun (x : BitVec 64 × BitVec 64 × BitVec 64 × SessionGhost × Session (List (BitVec 8)) ×
        BitVec 8 × BitVec 64 × BitVec 64 × List (BitVec 8)) =>
          x.2.2.2.2.1.aliceBaseKey.length = 33) ?_ ?_
    · -- Branch 3: 33-byte `aliceBaseKey ≠ key`
      have hsub : subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
          (withLsCodeLoaded lsmpl
            { promoteMatchingSessionRecordOverSpec A with
              pre := fun x s0 =>
                ⌜x.2.2.2.2.1.aliceBaseKey.length = 33⌝ ∗
                  (⌜x.2.2.2.2.1.state.version = x.2.2.2.2.2.1.zeroExtend 32⌝ ∗
                    (promoteMatchingSessionRecordOverSpec A).pre x s0) }) := by
        refine subroutine_ok_withLsCodeLoaded_refine_frame
          (promote_matching_session_key_miss_raw_placed_ok h_bb) ?_
        intro ⟨recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key⟩ R s0 hpre
        dsimp only [promoteMatchingSessionRecordOverSpec] at hpre
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨hlen33, hpre⟩
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨hver, hpre⟩
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, hmiss, hklen⟩, hmem⟩
        have hne_key : key ≠ sess.aliceBaseKey := fun hk => hmiss ⟨hver, hk.symm⟩
        have hrec_mem : s0.mem ⊨ sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
            ((serPtr ↦ₛ key) ∗ (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
             (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
             stackAt s0.sp promoteMatchingSessionMissStack ∗ R) :=
          Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
        obtain ⟨hcap_ne, halice, hle, _hlt⟩ := sessionRecordAt_miss_facts hrec_mem
        have hexp := sessionRecordAt_expose_miss A recPtr prevCap prevPtr G sess
        have hal33 : G.alice.bytes.length = 33 := by rw [halice]; exact hlen33
        have hcapnz : G.alice.cap ≠ 0 := by
          intro h0
          have h1 : G.alice.cap.toNat = 0 := by simp [h0]
          rw [h1, hal33] at hle; omega
        have habk : BitVec.ofNat 64 G.alice.bytes.length = 33#64 := by rw [hal33]
        rw [habk, aliceBufOverAt_expose_33 A G sess.aliceBaseKey halice hlen33 hcapnz] at hexp
        refine ⟨⟨recPtr, prevPtr, G.localIk.cap, G.alice.ptr, sess.state.sessionVersion,
            msgVer, serPtr, outPtr, key, sess.aliceBaseKey⟩,
          sessionRecordMissRestAt A recPtr prevCap prevPtr G sess ∗
            (A.live G.alice.ptr G.alice.cap.toNat 1 ∗
              memRegion (G.alice.ptr + 33#64) (G.alice.cap.toNat - 33)) ∗
            (memRegion (s0.sp - 1104#64) 656 ∗ memRegion (s0.sp - 440#64) 344), ?_, ?_⟩
        · dsimp only [promoteMatchingSessionKeyMissRawSpec]
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hcap_ne, hver, hklen, hlen33, hne_key⟩, ?_⟩
          rw [hexp, stackAt_promoteMissStack_eq s0.sp] at hrec_mem
          exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hrec_mem
        · intro sf hpost
          dsimp only [promoteMatchingSessionKeyMissRawSpec, promoteMatchingSessionRecordOverSpec] at hpost ⊢
          rw [hexp, stackAt_promoteMissStack_eq s0.sp]
          exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
      exact subroutine_ok_mono hsub
        (fun _ _ _ hp => Satisfies.mono (Entails.of_eq (by dsimp only [withLsCodeLoaded]; ac_rfl)) hp)
        (fun _ _ _ _ hq => hq)
    · -- Branch 2: `aliceBaseKey.length ≠ 33`
      have hsub : subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
          (withLsCodeLoaded lsmpl
            { promoteMatchingSessionRecordOverSpec A with
              pre := fun x s0 =>
                ⌜¬ x.2.2.2.2.1.aliceBaseKey.length = 33⌝ ∗
                  (⌜x.2.2.2.2.1.state.version = x.2.2.2.2.2.1.zeroExtend 32⌝ ∗
                    (promoteMatchingSessionRecordOverSpec A).pre x s0) }) := by
        refine subroutine_ok_withLsCodeLoaded_refine_frame
          (promote_matching_session_len_miss_raw_placed_ok h_bb) ?_
        intro ⟨recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key⟩ R s0 hpre
        dsimp only [promoteMatchingSessionRecordOverSpec] at hpre
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨hlen_ne, hpre⟩
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨hver, hpre⟩
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, _hmiss, _hklen⟩, hmem⟩
        have hrec_mem : s0.mem ⊨ sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
            ((serPtr ↦ₛ key) ∗ (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
             (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
             stackAt s0.sp promoteMatchingSessionMissStack ∗ R) :=
          Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
        obtain ⟨hcap_ne, halice, hle, hlt⟩ := sessionRecordAt_miss_facts hrec_mem
        have hexp := sessionRecordAt_expose_miss A recPtr prevCap prevPtr G sess
        have habk_ne : BitVec.ofNat 64 G.alice.bytes.length ≠ 33#64 :=
          ofNat_len_ne_33 (Nat.lt_of_le_of_lt hle hlt) (by rw [halice]; exact hlen_ne)
        refine ⟨⟨recPtr, prevPtr, G.localIk.cap, G.alice.ptr,
            BitVec.ofNat 64 G.alice.bytes.length, sess.state.sessionVersion,
            msgVer, serPtr, outPtr⟩,
          sessionRecordMissRestAt A recPtr prevCap prevPtr G sess ∗ aliceBufOverAt A G ∗
            (serPtr ↦ₛ key) ∗
            (memRegion (s0.sp - 1104#64) 656 ∗ memRegion (s0.sp - 440#64) 344), ?_, ?_⟩
        · dsimp only [promoteMatchingSessionLenMissRawSpec]
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hcap_ne, hver, habk_ne⟩, ?_⟩
          rw [hexp, stackAt_promoteMissStack_eq s0.sp] at hrec_mem
          exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hrec_mem
        · intro sf hpost
          dsimp only [promoteMatchingSessionLenMissRawSpec, promoteMatchingSessionRecordOverSpec] at hpost ⊢
          rw [hexp, stackAt_promoteMissStack_eq s0.sp]
          exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
      exact subroutine_ok_mono hsub
        (fun _ _ _ hp => Satisfies.mono (Entails.of_eq (by dsimp only [withLsCodeLoaded]; ac_rfl)) hp)
        (fun _ _ _ _ hq => hq)
  · -- Branch 1: Version mismatch (`sess.state.version ≠ msgVer.zeroExtend 32`)
    have hsub : subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
        (withLsCodeLoaded lsmpl
          { promoteMatchingSessionRecordOverSpec A with
            pre := fun x s0 =>
              ⌜¬ x.2.2.2.2.1.state.version = x.2.2.2.2.2.1.zeroExtend 32⌝ ∗
                (promoteMatchingSessionRecordOverSpec A).pre x s0 }) := by
      refine subroutine_ok_withLsCodeLoaded_refine_frame
        promote_matching_session_ver_miss_raw_placed_ok ?_
      intro ⟨recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key⟩ R s0 hpre
      dsimp only [promoteMatchingSessionRecordOverSpec] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨hver_ne, hpre⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, _hmiss, _hklen⟩, hmem⟩
      have hrec_mem : s0.mem ⊨ sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
          ((serPtr ↦ₛ key) ∗ (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
           (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
           stackAt s0.sp promoteMatchingSessionMissStack ∗ R) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
      obtain ⟨hcap_ne, _halice, _hle, _hlt⟩ := sessionRecordAt_miss_facts hrec_mem
      have hexp := sessionRecordAt_expose_miss A recPtr prevCap prevPtr G sess
      refine ⟨⟨recPtr, prevPtr, G.localIk.cap, G.alice.ptr,
          BitVec.ofNat 64 G.alice.bytes.length, sess.state.sessionVersion,
          msgVer, serPtr, outPtr⟩,
        sessionRecordMissRestAt A recPtr prevCap prevPtr G sess ∗ aliceBufOverAt A G ∗
          (serPtr ↦ₛ key) ∗
          (memRegion (s0.sp - 1104#64) 656 ∗ memRegion (s0.sp - 440#64) 344), ?_, ?_⟩
      · dsimp only [promoteMatchingSessionVerMissRawSpec]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hcap_ne, hver_ne⟩, ?_⟩
        rw [hexp, stackAt_promoteMissStack_eq s0.sp] at hrec_mem
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hrec_mem
      · intro sf hpost
        dsimp only [promoteMatchingSessionVerMissRawSpec, promoteMatchingSessionRecordOverSpec] at hpost ⊢
        rw [hexp, stackAt_promoteMissStack_eq s0.sp]
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
    exact subroutine_ok_mono hsub
      (fun _ _ _ hp => Satisfies.mono (Entails.of_eq (by dsimp only [withLsCodeLoaded]; ac_rfl)) hp)
      (fun _ _ _ _ hq => hq)

set_option maxHeartbeats 400000 in
/-- Relocatable `[LibsignalPlacement]` `promoteMatchingSessionMissSpec` theorem on block `50`. -/
theorem promote_matching_session_miss_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
      (withLsCodeLoaded lsmpl (promoteMatchingSessionMissSpec A)) := by
  refine subroutine_ok_withLsCodeLoaded_refine_frame
    (promote_matching_session_record_over_placed_ok (A := A) h_bb) ?_
  intro x R s0 hpre
  dsimp only [promoteMatchingSessionMissSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, hcur, hmiss, hklen⟩, hmem⟩
  have hrec_sat : s0.mem ⊨ sessionRecordAt A x.recPtr x.g x.r ∗
      ((x.serPtr ↦ₛ x.serBytes) ∗ memRegion x.outPtr 16 ∗
       stackAt s0.sp promoteMatchingSessionMissStack ∗ R) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  have hg_some : ∃ G : SessionGhost, x.g.cur = some G := by
    have hrec_l := Satisfies.of_sep_left hrec_sat
    unfold sessionRecordAt at hrec_l
    rw [hcur] at hrec_l
    cases hgc : x.g.cur with
    | none =>
      rw [hgc] at hrec_l
      have hf := Satisfies.of_sep_right hrec_l
      rw [satisfies_pure] at hf
      exact False.elim hf
    | some G => exact ⟨G, rfl⟩
  obtain ⟨G, hgc⟩ := hg_some
  have hrec_eq : sessionRecordAt A x.recPtr x.g x.r =
      sessionRecordAt A x.recPtr ⟨x.g.prevCap, x.g.prevPtr, some G⟩ ⟨some x.s⟩ := by
    unfold sessionRecordAt
    rw [hgc, hcur]
  refine ⟨(x.recPtr, x.g.prevCap, x.g.prevPtr, G, x.s, x.msgVer, x.serPtr, x.outPtr, x.serBytes),
    memRegion (x.outPtr + 9#64) 7, ?_, ?_⟩
  · dsimp only [promoteMatchingSessionRecordOverSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hmiss, hklen⟩, ?_⟩
    rw [hrec_eq, outRegion16_split_over x.outPtr] at hrec_sat
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hrec_sat
  · intro sf hpost
    dsimp only [promoteMatchingSessionRecordOverSpec, promoteMatchingSessionMissSpec] at hpost ⊢
    rw [hrec_eq]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

end Placed

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
