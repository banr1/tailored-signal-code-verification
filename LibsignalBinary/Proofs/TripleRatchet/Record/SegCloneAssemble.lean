/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Record.FetchClone
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Destination Slot Assembly and Version Check for `SegClone`

Verifies the `alice_base_key` (`+0x56c / +0x1920 / +0x430 → +0x584 / +0x46c`) and `pq_ratchet_state`
(`+0x584 / +0x46c → +0x594`) clone steps together with the 344-byte destination `SessionStructure`
reassembly and version check (`+0x594 → +0x69c / +0x7e4`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Fast side-condition closer that clears large continuation/spec hypotheses before simplifying. -/
macro "segCloneAssemble_close" : tactic =>
  `(tactic| (
    try clear hnext
    try clear hshim
    try clear halloc
    try clear hmemcpy
    try clear hcall
    try clear hpanic
    try clear hsub
    try clear hexpose
    try clear htail_pts
    try clear h_at_39c
    try clear h_at_3f8
    try clear h_at_444
    try clear h_at_478
    first
    | rfl
    | (dsimp only [State.spAligned, Reg.x0, Reg.x1, Reg.x2, Reg.x8, Reg.x9, Reg.x10,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.fp] at *
       try simp (config := { decide := true }) only [reduceStateReadReg64,
        State.pc_writeReg64, State.pc_writeReg32,
        State.status_writeReg64, State.status_writeReg32,
        State.sp_writeReg64_gpr,
        State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64,
        calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, calleeSavedVRegs_setPState,
        calleeSavedVRegs_writeReg64, calleeSavedVRegs_writeReg32,
        calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg]
       simp (config := { decide := true }) only [*, reduceStateReadReg64,
        State.pc_writeReg64, State.pc_writeReg32,
        State.status_writeReg64, State.status_writeReg32,
        State.sp_writeReg64_gpr,
        State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64,
        calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, calleeSavedVRegs_setPState,
        calleeSavedVRegs_writeReg64, calleeSavedVRegs_writeReg32,
        calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg,
        State.setPC, State.setPState,
        BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_add, List.length_cons]
       done)
    | (dsimp only [State.spAligned, Reg.x0, Reg.x1, Reg.x2, Reg.x8, Reg.x9, Reg.x10,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.fp] at *
       try simp (config := { decide := true }) only [reduceStateReadReg64,
        State.pc_writeReg64, State.pc_writeReg32,
        State.status_writeReg64, State.status_writeReg32,
        State.sp_writeReg64_gpr,
        State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64,
        calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, calleeSavedVRegs_setPState,
        calleeSavedVRegs_writeReg64, calleeSavedVRegs_writeReg32,
        calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg]
       simp [*, State.setPC, State.setPState, State.writeReg64, State.writeReg32]
       done)
    | (dsimp only [State.spAligned, Reg.x0, Reg.x1, Reg.x2, Reg.x8, Reg.x9, Reg.x10,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.fp] at *
       subst_vars
       simp [*, State.setPC, State.setPState, State.writeReg64, State.writeReg32]
       done)))

theorem segClone_aliceBaseKey_444_pos {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {F : SepProp}
    (halice : 0 < x.G.alice.bytes.length)
    (hlen_le : x.G.alice.bytes.length ≤ x.G.alice.cap.toNat)
    (hcap_lt : x.G.alice.cap.toNat < 2 ^ 63)
    (hptr : x.G.alice.ptr ≠ 0)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x444#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 x.G.alice.bytes.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (alice' : VecGhost),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x46c#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = alice'.cap →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = alice'.ptr →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      alice'.bytes = x.G.alice.bytes →
      alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗
          vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        (s.sp + 0x198#64) ↦₆₄ x.G.alice.cap ∗
        (s.sp + 0x1a0#64) ↦₆₄ x.G.alice.ptr ∗
        (s.sp + 0x1a8#64) ↦₆₄ BitVec.ofNat 64 x.G.alice.bytes.length ∗
        (x.G.alice.ptr ↦ₛ x.G.alice.bytes) ∗
        A.live x.G.alice.ptr x.G.alice.cap.toNat 1 ∗
        memRegion (x.G.alice.ptr + BitVec.ofNat 64 x.G.alice.bytes.length)
          (x.G.alice.cap.toNat - x.G.alice.bytes.length) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_3a4a8
  have hshim := segClone_shim_ok_at hA
  have halloc := segClone_alloc_ok_at hA
  have hmemcpy := segClone_memcpy_ok_at hA
  have hpanic := segClone_panic_0x2628 (img := img) (C := C) (A := A) (ctl := ctl)
    (S := S) (ext := ext) (ret := ret) (Q := Q) x s0
  have h1a0 : s.sp + 0x198#64 + 8#64 = s.sp + 0x1a0#64 := by bv_arith
  have h1a8 : s.sp + 0x198#64 + 16#64 = s.sp + 0x1a8#64 := by bv_arith
  have halice_lt : x.G.alice.bytes.length < 2 ^ 63 := by omega
  have halice_le63 : x.G.alice.bytes.length + 1 ≤ 2 ^ 63 := by omega
  have halice_le64 : x.G.alice.bytes.length ≤ 2 ^ 64 := by omega
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk x.G.alice.bytes.length 1 := ⟨halice, hpow2, halice_le63⟩
  have htoNat : (BitVec.ofNat 64 x.G.alice.bytes.length).toNat = x.G.alice.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  segClone_fetches img.base (Rust.withPanics ext) hfn 0x444 40
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (1112))
  wp_steps
  wp_call hshim ()
  clear hshim
  wp_steps
  wp_call halloc (x.G.alice.bytes.length, 1)
  clear halloc
  refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_3rd fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (9768))
    wp_steps
    refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
    exact hpanic _ _ R (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
  · clear hpanic
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (1132))
    wp_steps
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.alice.ptr, x.G.alice.bytes)
    clear hmemcpy
    refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
    have hsp_eq : sf.sp = s.sp := by segCloneAssemble_close
    refine SepWPp.weaken_pre ?_
      (hnext _ ⟨BitVec.ofNat 64 x.G.alice.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.alice.bytes⟩
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
        (by segCloneAssemble_close) (by segCloneAssemble_close) rfl rfl)
    rw [vecGhostAt_eq_of_pos A x.G.alice (s.sp + 0x198#64) halice, h1a0, h1a8,
        vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.G.alice.bytes halice halice_lt hoom64]
    have h_pure_emp :
        (⌜x.G.alice.bytes.length ≤ x.G.alice.cap.toNat ∧
            x.G.alice.cap.toNat < 2 ^ 63 ∧ x.G.alice.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
    rw [h_pure_emp]
    simp only [sepConj_assoc, hsp_eq, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

/-- Clones `alice_base_key` (`+0x56c / +0x1920 / +0x430 → +0x584 / +0x46c`) and loads registration IDs. -/
theorem segClone_aliceBaseKey {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v30 : BitVec 64} {w288 w28c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x56c#64 ∨
           s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x1920#64 ∨
           s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x430#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (alice' : VecGhost),
      s1.pc = (if x.G.alice.bytes = [] then
                 (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x584#64
               else
                 (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x46c#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x21 = w288.setWidth 64 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = w28c.setWidth 64 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = alice'.cap →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = alice'.ptr →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      alice'.bytes = x.G.alice.bytes →
      alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗
          vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
          ((s.sp + 0x288#64) ↦₃₂ w288) ∗
          ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
          ((s.sp + 0x30#64) ↦₆₄ s.readReg64 .x26) ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗
        ((s.sp + 0x288#64) ↦₃₂ w288) ∗
        ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
        ((s.sp + 0x30#64) ↦₆₄ v30) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_3a4a8
  have h1a0 : s.sp + 0x198#64 + 8#64 = s.sp + 0x1a0#64 := by bv_arith
  have h1a8 : s.sp + 0x198#64 + 16#64 = s.sp + 0x1a8#64 := by bv_arith
  segClone_fetches img.base (Rust.withPanics ext) hfn 0x430 20
  segClone_fetches img.base (Rust.withPanics ext) hfn 0x56c 24
  segClone_fetches img.base (Rust.withPanics ext) hfn 0x1920 24
  clear hfn
  rcases eq_nil_or_length_pos x.G.alice.bytes with halice | halice
  · simp only [halice, ↓reduceIte] at hnext
    rw [vecGhostAt_eq_of_nil A x.G.alice (s.sp + 0x198#64) halice, h1a0, h1a8]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    have h_pure_emp :
        (⌜x.G.alice.cap.toNat < 2 ^ 63 ∧ x.G.alice.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr msgDecryptName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    rcases hpc with hpc | hpc | hpc
    · apply SepWPp.of_sepWP (mid := entry + bv% (1412))
      wp_steps
      refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
      refine SepWPp.weaken_pre ?_
        (hnext _ ⟨0#64, 1#64, []⟩ (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by simp [halice]) (by simp [halice]))
      rw [vecGhostAt_eq_of_nil A x.G.alice (s.sp + 0x198#64) halice, h1a0, h1a8,
          vecU8Buf_nil_eq A, h_pure_emp]
      dsimp only [Reg.x26]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · apply SepWPp.of_sepWP (mid := entry + bv% (1412))
      wp_steps
      refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
      refine SepWPp.weaken_pre ?_
        (hnext _ ⟨0#64, 1#64, []⟩ (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by simp [halice]) (by simp [halice]))
      rw [vecGhostAt_eq_of_nil A x.G.alice (s.sp + 0x198#64) halice, h1a0, h1a8,
          vecU8Buf_nil_eq A, h_pure_emp]
      dsimp only [Reg.x26]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · apply SepWPp.of_sepWP (mid := entry + bv% (1412))
      wp_steps
      refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
      refine SepWPp.weaken_pre ?_
        (hnext _ ⟨0#64, 1#64, []⟩ (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by simp [halice]) (by simp [halice]))
      rw [vecGhostAt_eq_of_nil A x.G.alice (s.sp + 0x198#64) halice, h1a0, h1a8,
          vecU8Buf_nil_eq A, h_pure_emp]
      dsimp only [Reg.x26]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
  · have halice_ne_nil : x.G.alice.bytes ≠ [] := List.ne_nil_of_length_pos halice
    simp only [halice_ne_nil, ↓reduceIte] at hnext
    rw [vecGhostAt_eq_of_pos A x.G.alice (s.sp + 0x198#64) halice, h1a0, h1a8]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have halice_ne : BitVec.ofNat 64 x.G.alice.bytes.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos halice (by omega)
    have halice_beq : (BitVec.ofNat 64 x.G.alice.bytes.length == 0#64) = false :=
      beq_ofNat_zero_eq_false halice (by omega)
    have hsub := @segClone_aliceBaseKey_444_pos img C A ctl S ext hA x R s0
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr msgDecryptName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    suffices h_at_444 : ∀ s_444 : State,
        s_444.pc = entry + bv% (1092) →
        s_444.status = .Running →
        s_444.sp = s.sp →
        s_444.spAligned = true →
        s_444.readReg64 .x19 = s.readReg64 .x19 →
        s_444.readReg64 .x21 = w288.setWidth 64 →
        s_444.readReg64 .x22 = s.readReg64 .x22 →
        s_444.readReg64 .x23 = w28c.setWidth 64 →
        s_444.readReg64 .x24 = s.readReg64 .x24 →
        s_444.readReg64 .x25 = BitVec.ofNat 64 x.G.alice.bytes.length →
        s_444.readReg64 .x26 = s.readReg64 .x26 →
        s_444.readReg64 .x28 = s.readReg64 .x28 →
        s_444.readReg64 .x29 = s.readReg64 .x29 →
        (s_444.trace = s0.trace ∧ calleeSavedVRegs s_444 = calleeSavedVRegs s0) →
        SepWPp prog ret s_444
          (A.pool ∗
            (s_444.sp + 0x198#64) ↦₆₄ x.G.alice.cap ∗
            (s_444.sp + 0x1a0#64) ↦₆₄ x.G.alice.ptr ∗
            (s_444.sp + 0x1a8#64) ↦₆₄ BitVec.ofNat 64 x.G.alice.bytes.length ∗
            (x.G.alice.ptr ↦ₛ x.G.alice.bytes) ∗
            A.live x.G.alice.ptr x.G.alice.cap.toNat 1 ∗
            memRegion (x.G.alice.ptr + BitVec.ofNat 64 x.G.alice.bytes.length)
              (x.G.alice.cap.toNat - x.G.alice.bytes.length) ∗
            (s_444.sp + 0x288#64) ↦₃₂ w288 ∗
            (s_444.sp + 0x28c#64) ↦₃₂ w28c ∗
            (s_444.sp + 0x30#64) ↦₆₄ s.readReg64 .x26 ∗
            stackAt s_444.sp allocHookStack ∗ F)
          Q (clonePanicPost C A ctl uuidTryParse S img x R s0) by
      rcases hpc with hpc | hpc | hpc
      · apply SepWPp.of_sepWP (mid := entry + bv% (1092))
        wp_steps
        refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
        dsimp only [Reg.x26] at h_at_444
        exact h_at_444 _ (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      · apply SepWPp.of_sepWP (mid := entry + bv% (1092))
        wp_steps
        refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
        dsimp only [Reg.x26] at h_at_444
        exact h_at_444 _ (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      · apply SepWPp.of_sepWP (mid := entry + bv% (1092))
        wp_steps
        refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
        dsimp only [Reg.x26] at h_at_444
        exact h_at_444 _ (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
    intro s_444 hpc444 hrun444 hsp444 hspA444 hx19_444 hx21_444 hx22_444 hx23_444 hx24_444 hx25_444 hx26_444 hx28_444 hx29_444 htr444
    refine SepWPp.weaken_pre
      (P' := A.pool ∗
              (s_444.sp + 0x198#64) ↦₆₄ x.G.alice.cap ∗
              (s_444.sp + 0x1a0#64) ↦₆₄ x.G.alice.ptr ∗
              (s_444.sp + 0x1a8#64) ↦₆₄ BitVec.ofNat 64 x.G.alice.bytes.length ∗
              (x.G.alice.ptr ↦ₛ x.G.alice.bytes) ∗
              A.live x.G.alice.ptr x.G.alice.cap.toNat 1 ∗
              memRegion (x.G.alice.ptr + BitVec.ofNat 64 x.G.alice.bytes.length)
                (x.G.alice.cap.toNat - x.G.alice.bytes.length) ∗
              stackAt s_444.sp allocHookStack ∗
              (((s_444.sp + 0x288#64) ↦₃₂ w288) ∗
                ((s_444.sp + 0x28c#64) ↦₃₂ w28c) ∗
                ((s_444.sp + 0x30#64) ↦₆₄ s.readReg64 .x26) ∗ F))
      (Entails.of_eq (by ac_rfl)) ?_
    refine hsub halice hlen_le hcap_lt hptr hpc444 hrun444 hspA444 hx25_444 htr444
      fun s1 alice' hpc1 hrun1 hsp1 hspA1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 htr1 hbytes' hcap' => ?_
    rw [hsp444]
    refine SepWPp.weaken_pre ?_
      (hnext s1 alice' hpc1 hrun1 (by reg_chain) hspA1
        (by reg_chain) (by reg_chain) (by reg_chain)
        (by reg_chain) (by reg_chain) hx25_1 (by reg_chain)
        hx27_1 (by reg_chain) (by reg_chain) htr1 hbytes' hcap')
    exact Entails.of_eq (by ac_rfl)

theorem segClone_pqRatchet_478_pos {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {F : SepProp}
    (hpq : 0 < x.st.pqRatchetState.length)
    (hlen_le : x.st.pqRatchetState.length ≤ x.G.pq.cap.toNat)
    (hcap_lt : x.G.pq.cap.toNat < 2 ^ 63)
    (hptr : x.G.pq.ptr ≠ 0)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x478#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.st.pqRatchetState.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pqCap' pqPtr' : BitVec 64),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x594#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = pqCap' →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = pqPtr' →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      pqCap' = BitVec.ofNat 64 x.st.pqRatchetState.length →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
          vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        (s.sp + 0x1b0#64) ↦₆₄ x.G.pq.cap ∗
        (s.sp + 0x1b8#64) ↦₆₄ x.G.pq.ptr ∗
        (s.sp + 0x1c0#64) ↦₆₄ BitVec.ofNat 64 x.st.pqRatchetState.length ∗
        (x.G.pq.ptr ↦ₛ x.st.pqRatchetState) ∗
        A.live x.G.pq.ptr x.G.pq.cap.toNat 1 ∗
        memRegion (x.G.pq.ptr + BitVec.ofNat 64 x.st.pqRatchetState.length)
          (x.G.pq.cap.toNat - x.st.pqRatchetState.length) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_3a4a8
  have hshim := segClone_shim_ok_at hA
  have halloc := segClone_alloc_ok_at hA
  have hmemcpy := segClone_memcpy_ok_at hA
  have hpanic := segClone_panic_0x25f8 (img := img) (C := C) (A := A) (ctl := ctl)
    (S := S) (ext := ext) (ret := ret) (Q := Q) x s0
  have h1b8 : s.sp + 0x1b0#64 + 8#64 = s.sp + 0x1b8#64 := by bv_arith
  have h1c0 : s.sp + 0x1b0#64 + 16#64 = s.sp + 0x1c0#64 := by bv_arith
  have hpq_lt : x.st.pqRatchetState.length < 2 ^ 63 := by omega
  have hpq_le63 : x.st.pqRatchetState.length + 1 ≤ 2 ^ 63 := by omega
  have hpq_le64 : x.st.pqRatchetState.length ≤ 2 ^ 64 := by omega
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk x.st.pqRatchetState.length 1 := ⟨hpq, hpow2, hpq_le63⟩
  have htoNat : (BitVec.ofNat 64 x.st.pqRatchetState.length).toNat = x.st.pqRatchetState.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  segClone_fetches img.base (Rust.withPanics ext) hfn 0x478 48
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (1164))
  wp_steps
  wp_call hshim ()
  clear hshim
  wp_steps
  wp_call halloc (x.st.pqRatchetState.length, 1)
  clear halloc
  refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_3rd fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (9720))
    wp_steps
    refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
    exact hpanic _ _ R (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
  · clear hpanic
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (1428))
    wp_steps
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.pq.ptr, x.st.pqRatchetState)
    clear hmemcpy
    wp_steps
    refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
    refine SepWPp.weaken_pre ?_
      (hnext _ (BitVec.ofNat 64 x.st.pqRatchetState.length) (sf_1.readReg64 (Reg.gpr 0#5))
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) rfl)
    rw [vecU8At_eq_of_pos A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState hpq,
        h1b8, h1c0,
        vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.st.pqRatchetState hpq hpq_lt hoom64]
    have hsp_eq : sf.sp = s.sp := by segCloneAssemble_close
    have h_pure_emp :
        (⌜x.st.pqRatchetState.length ≤ x.G.pq.cap.toNat ∧
            x.G.pq.cap.toNat < 2 ^ 63 ∧ x.G.pq.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
    rw [h_pure_emp]
    simp only [sepConj_assoc, hsp_eq, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

/-- Clones `pq_ratchet_state` (`+0x584 / +0x46c → +0x594`) and restores `x24 = sp + 0xca0`. -/
theorem segClone_pqRatchet {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {F : SepProp}
    (hpc : s.pc = (if x.G.alice.bytes = [] then
                     (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x584#64
                   else
                     (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x46c#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pqCap' pqPtr' : BitVec 64),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x594#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = pqCap' →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = pqPtr' →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x22 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      pqCap' = BitVec.ofNat 64 x.st.pqRatchetState.length →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
          vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_3a4a8
  have h1b8 : s.sp + 0x1b0#64 + 8#64 = s.sp + 0x1b8#64 := by bv_arith
  have h1c0 : s.sp + 0x1b0#64 + 16#64 = s.sp + 0x1c0#64 := by bv_arith
  have hpcs : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x584#64 ∨
              s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x46c#64 := by
    by_cases h : x.G.alice.bytes = [] <;> simp only [h, ↓reduceIte] at hpc <;> [exact Or.inl hpc; exact Or.inr hpc]
  clear hpc
  segClone_fetches img.base (Rust.withPanics ext) hfn 0x46c 12
  segClone_fetches img.base (Rust.withPanics ext) hfn 0x584 16
  clear hfn
  rcases eq_nil_or_length_pos x.st.pqRatchetState with hpq | hpq
  · rw [hpq, vecU8At_eq_of_nil A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr, h1b8, h1c0]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    have h_pure_emp :
        (⌜x.G.pq.cap.toNat < 2 ^ 63 ∧ x.G.pq.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr msgDecryptName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    rcases hpcs with hpc | hpc
    · apply SepWPp.of_sepWP (mid := entry + bv% (1428))
      wp_steps
      refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
      refine SepWPp.weaken_pre ?_
        (hnext _ 0#64 1#64 (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by simp [hpq]))
      rw [hpq, vecU8At_eq_of_nil A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr, h1b8, h1c0,
          vecU8Buf_nil_eq A, h_pure_emp]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · apply SepWPp.of_sepWP (mid := entry + bv% (1428))
      wp_steps
      refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
      refine SepWPp.weaken_pre ?_
        (hnext _ 0#64 1#64 (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by simp [hpq]))
      rw [hpq, vecU8At_eq_of_nil A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr, h1b8, h1c0,
          vecU8Buf_nil_eq A, h_pure_emp]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
  · rw [vecU8At_eq_of_pos A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState hpq,
        h1b8, h1c0]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hpq_ne : BitVec.ofNat 64 x.st.pqRatchetState.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos hpq (by omega)
    have hpq_beq : (BitVec.ofNat 64 x.st.pqRatchetState.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpq (by omega)
    have hsub := @segClone_pqRatchet_478_pos img C A ctl S ext hA x R s0
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr msgDecryptName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    suffices h_at_478 : ∀ s_478 : State,
        s_478.pc = entry + bv% (1144) →
        s_478.status = .Running →
        s_478.sp = s.sp →
        s_478.spAligned = true →
        s_478.readReg64 .x19 = s.readReg64 .x19 →
        s_478.readReg64 .x20 = BitVec.ofNat 64 x.st.pqRatchetState.length →
        s_478.readReg64 .x21 = s.readReg64 .x21 →
        s_478.readReg64 .x23 = s.readReg64 .x23 →
        s_478.readReg64 .x25 = s.readReg64 .x25 →
        s_478.readReg64 .x26 = s.readReg64 .x22 →
        s_478.readReg64 .x27 = s.readReg64 .x27 →
        s_478.readReg64 .x28 = s.readReg64 .x28 →
        s_478.readReg64 .x29 = s.readReg64 .x29 →
        (s_478.trace = s0.trace ∧ calleeSavedVRegs s_478 = calleeSavedVRegs s0) →
        SepWPp prog ret s_478
          (A.pool ∗
            (s_478.sp + 0x1b0#64) ↦₆₄ x.G.pq.cap ∗
            (s_478.sp + 0x1b8#64) ↦₆₄ x.G.pq.ptr ∗
            (s_478.sp + 0x1c0#64) ↦₆₄ BitVec.ofNat 64 x.st.pqRatchetState.length ∗
            (x.G.pq.ptr ↦ₛ x.st.pqRatchetState) ∗
            A.live x.G.pq.ptr x.G.pq.cap.toNat 1 ∗
            memRegion (x.G.pq.ptr + BitVec.ofNat 64 x.st.pqRatchetState.length)
              (x.G.pq.cap.toNat - x.st.pqRatchetState.length) ∗
            stackAt s_478.sp allocHookStack ∗ F)
          Q (clonePanicPost C A ctl uuidTryParse S img x R s0) by
      rcases hpcs with hpc | hpc
      · apply SepWPp.of_sepWP (mid := entry + bv% (1144))
        wp_steps
        refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
        exact h_at_478 _ (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      · apply SepWPp.of_sepWP (mid := entry + bv% (1144))
        wp_steps
        refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
        exact h_at_478 _ (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
    intro s_478 hpc478 hrun478 hsp478 hspA478 hx19_478 hx20_478 hx21_478 hx23_478 hx25_478 hx26_478 hx27_478 hx28_478 hx29_478 htr478
    refine hsub hpq hlen_le hcap_lt hptr hpc478 hrun478 hspA478 hx20_478 htr478
      fun s1 pqCap' pqPtr' hpc1 hrun1 hsp1 hspA1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 htr1 hcap' => ?_
    rw [hsp478] at hx24_1 ⊢
    exact hnext s1 pqCap' pqPtr' hpc1 hrun1 (by reg_chain) hspA1
      (by reg_chain) hx20_1 (by reg_chain) hx22_1
      (by reg_chain) hx24_1 (by reg_chain) (by reg_chain)
      (by reg_chain) (by reg_chain) (by reg_chain) htr1 hcap'

/-- First half of destination slot assembly (`+0x594 → +0x620`, 35 instructions). -/
theorem segClone_assemble_1 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (dv : DstVals)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64)
    (scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v00 v08 : BitVec 64) (w14 : BitVec 32) (pendPtr' : BitVec 64)
    (w24 w28 w2c : BitVec 32) (sessionVersion previousCounter : BitVec 32)
    (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x594#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (hx28 : s.readReg64 .x28 = chainsPtr')
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x620#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x8 = w2c.setWidth 64 →
      s1.readReg64 .x9 = w28.setWidth 64 →
      s1.readReg64 .x10 = previousCounter.setWidth 64 →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (segClone_dstSlotsMidAt s.sp dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
          scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendPtr' ∗
          chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          spillSlotsAt s.sp v00 v08 w14 pendPtr' w24 w28 w2c chainsCap' sessionVersion
            scCap' rootPtr' previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (dstSlotsAt s.sp dv ∗
        chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        spillSlotsAt s.sp v00 v08 w14 pendPtr' w24 w28 w2c chainsCap' sessionVersion
          scCap' rootPtr' previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr localIk'.cap ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_3a4a8
  segClone_fetches img.base (Rust.withPanics ext) hfn 0x594 140
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  unfold segClone_dstSlotsMidAt spillSlotsAt at hnext
  unfold dstSlotsAt spillSlotsAt
  rw [chunks96_6QAt_sp_0xb40 s.sp sq0 sq1 sq2 sq3 sq4 sq5,
      segClone_chunks96_6QAt_sp_0xd38 s.sp dv.q0 dv.q1 dv.q2 dv.q3 dv.q4 dv.q5]
  rw [chunks96_6QAt_sp_0xb40 s.sp sq0 sq1 sq2 sq3 sq4 sq5,
      segClone_chunks96_6QAt_sp_0xd38 s.sp sq0 sq1 sq2 sq3 sq4 sq5] at hnext
  simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hnext ⊢
  apply SepWPp.of_sepWP (mid := entry + bv% (1568))
  wp_steps
  refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
  refine SepWPp.weaken_pre ?_
    (hnext _ (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      (by segCloneAssemble_close) (by segCloneAssemble_close))
  exact Entails.of_eq (by ac_rfl)

/-- Second half of destination slot assembly and version check (`+0x620 → +0x69c / +0x7e4`, 31 instructions). -/
theorem segClone_assemble_2 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (dv : DstVals)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64) (alice' : VecGhost)
    (pqCap' pqPtr' : BitVec 64)
    (scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (kybCap' kybPtr' v08 : BitVec 64) (w14 : BitVec 32) (pendCap' pendPtr' : BitVec 64)
    (w24 w28 w2c : BitVec 32) (w288 w28c : BitVec 32)
    (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x620#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = w2c.setWidth 64)
    (hx9 : s.readReg64 .x9 = w28.setWidth 64)
    (hx10 : s.readReg64 .x10 = x.st.previousCounter.setWidth 64)
    (hx19 : s.readReg64 .x19 = kybCap')
    (hx20 : s.readReg64 .x20 = pqCap')
    (hx21 : s.readReg64 .x21 = w288.setWidth 64)
    (hx22 : s.readReg64 .x22 = pqPtr')
    (hx23 : s.readReg64 .x23 = w28c.setWidth 64)
    (_hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (hx25 : s.readReg64 .x25 = alice'.cap)
    (hx26 : s.readReg64 .x26 = pendCap')
    (hx27 : s.readReg64 .x27 = alice'.ptr)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ s1 : State,
      s1.pc = (if x.st.version.toNat = x.msg.messageVersion.toNat then
                 (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x69c#64
               else
                 (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x7e4#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x9 = x.msg.messageVersion.setWidth 64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (segClone_dstSlotsWrittenAt s.sp localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
          pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w28 w2c v08 w24
          kybCap' kybPtr' w14 x.st.sessionVersion x.st.previousCounter w288 w28c ∗
          spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
            scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗
          ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (segClone_dstSlotsMidAt s.sp dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
        scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendPtr' ∗
        spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
          scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr localIk'.cap ∗
        ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_3a4a8
  segClone_fetches img.base (Rust.withPanics ext) hfn 0x620 124
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  have hver_eq_iff :
      x.st.version.toNat = x.msg.messageVersion.toNat ↔
        (if x.st.sessionVersion = 0 then 2 else x.st.sessionVersion) =
          x.msg.messageVersion.setWidth 32 := by
    unfold SessionState.version
    constructor
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [h, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.msg.messageVersion.isLt; omega)]
    · intro h
      have ht := congrArg BitVec.toNat h
      rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.msg.messageVersion.isLt; omega)] at ht
  have hpc_ver :
      (if (if x.st.sessionVersion = 0 then 2#64 else BitVec.truncate 64 x.st.sessionVersion) =
          BitVec.zeroExtend 64 x.msg.messageVersion then entry + bv% (1692) else entry + bv% (2020)) =
      (if x.st.version.toNat = x.msg.messageVersion.toNat then entry + bv% (1692) else entry + bv% (2020)) := by
    simp only [segClone_version_cond_iff, ← hver_eq_iff]
  unfold segClone_dstSlotsWrittenAt spillSlotsAt at hnext
  unfold segClone_dstSlotsMidAt spillSlotsAt
  simp only [sepConj_assoc] at hnext ⊢
  apply SepWPp.of_sepWP
    (mid := if x.st.version.toNat = x.msg.messageVersion.toNat then entry + bv% (1692) else entry + bv% (2020))
  wp_steps
  refine SepWP.done (by simpa using hpc_ver) (by exact hrun) ?_
  refine SepWPp.weaken_pre ?_
    (hnext _ (by simpa using hpc_ver) (by exact hrun) rfl hsp rfl rfl (by segCloneAssemble_close))
  exact Entails.of_eq (by ac_rfl)

theorem segClone_fields_10_to_11 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (dv : DstVals)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64) (alice' : VecGhost)
    (pqCap' pqPtr' : BitVec 64)
    (scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (kybCap' kybPtr' v08 : BitVec 64) (w14 : BitVec 32) (pendCap' pendPtr' : BitVec 64)
    (w24 w28 w2c : BitVec 32) (w288 w28c : BitVec 32)
    (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x594#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = kybCap')
    (hx20 : s.readReg64 .x20 = pqCap')
    (hx21 : s.readReg64 .x21 = w288.setWidth 64)
    (hx22 : s.readReg64 .x22 = pqPtr')
    (hx23 : s.readReg64 .x23 = w28c.setWidth 64)
    (hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (hx25 : s.readReg64 .x25 = alice'.cap)
    (hx26 : s.readReg64 .x26 = pendCap')
    (hx27 : s.readReg64 .x27 = alice'.ptr)
    (hx28 : s.readReg64 .x28 = chainsPtr')
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ s1 : State,
      s1.pc = (if x.st.version.toNat = x.msg.messageVersion.toNat then
                 (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x69c#64
               else
                 (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x7e4#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x9 = x.msg.messageVersion.setWidth 64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (segClone_dstSlotsWrittenAt s.sp localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
          pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w28 w2c v08 w24
          kybCap' kybPtr' w14 x.st.sessionVersion x.st.previousCounter w288 w28c ∗
          chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
            scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗
          ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (dstSlotsAt s.sp dv ∗
        chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
          scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr localIk'.cap ∗
        ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  refine segClone_assemble_1 dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
    scCap' sq0 sq1 sq2 sq3 sq4 sq5 kybPtr' v08 w14 pendPtr' w24 w28 w2c
    x.st.sessionVersion x.st.previousCounter
    (((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
    hpc hrun hsp hx24 hx28 htr
    fun s1 hpc1 hrun1 hsp1 hspA1 hx8_1 hx9_1 hx10_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx29_1 htr1 => ?_
  rw [← hsp1] at hx24_1 ⊢
  refine SepWPp.weaken_pre
    (P' := segClone_dstSlotsMidAt s1.sp dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
            scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendPtr' ∗
          spillSlotsAt s1.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
            scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗
          ((s1.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
          (chunks96_6QAt (s1.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine segClone_assemble_2 dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
    pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 kybCap' kybPtr' v08 w14 pendCap' pendPtr'
    w24 w28 w2c w288 w28c
    (chunks96_6QAt (s1.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗ F)
    hpc1 hrun1 hspA1 hx8_1 hx9_1 hx10_1
    (by reg_chain) (by reg_chain) (by reg_chain)
    (by reg_chain) (by reg_chain) hx24_1
    (by reg_chain) (by reg_chain) (by reg_chain) htr1
    fun s2 hpc2 hrun2 hsp2 hspA2 hx9_2 hx29_2 htr2 => ?_
  rw [hsp1]
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext s2 hpc2 hrun2 (by reg_chain) hspA2 hx9_2 (by reg_chain) htr2)

/-! ## Relocatable `[LibsignalPlacement]` Destination Slot Assembly -/

abbrev clonePanicPostPlaced [lsmpl : LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (x : RecordDecryptGhost) (R : SepProp) (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (recordDecryptPlacedSpec C A ctl parse S).onPanic x s0 sf ∗ R)

/-- Relocatable `[LibsignalPlacement]` first half of destination slot assembly (`+0x594 → +0x620`, 35 instructions). -/
theorem segClone_assemble_1_placed [lsmpl : LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)} {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (dv : DstVals) (localIk' remoteIk' : VecGhost) (rootPtr' chainsCap' chainsPtr' scCap' : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (v00 v08 : BitVec 64) (w14 : BitVec 32) (pendPtr' : BitVec 64)
    (w24 w28 w2c sessionVersion previousCounter : BitVec 32) (F : SepProp)
    (hpc : s.pc = (blkPl_197).base + 1428#64) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = s.sp + 0xca0#64) (hx28 : s.readReg64 .x28 = chainsPtr')
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ s1 : State,
      s1.pc = (blkPl_197).base + 1568#64 → s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x8 = w2c.setWidth 64 → s1.readReg64 .x9 = w28.setWidth 64 →
      s1.readReg64 .x10 = previousCounter.setWidth 64 → s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 → s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 → s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.sp + 0xca0#64 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 → s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp ((blkPC_197).rebase (blkPl_197).base H) ret s1
        (segClone_dstSlotsMidAt s.sp dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
          scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendPtr' ∗
          chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          spillSlotsAt s.sp v00 v08 w14 pendPtr' w24 w28 w2c chainsCap' sessionVersion
            scCap' rootPtr' previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗ F)
        Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0)) :
    SepWPp ((blkPC_197).rebase (blkPl_197).base H) ret s
      (dstSlotsAt s.sp dv ∗
        chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        spillSlotsAt s.sp v00 v08 w14 pendPtr' w24 w28 w2c chainsCap' sessionVersion
          scCap' rootPtr' previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr localIk'.cap ∗ F)
      Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  unfold segClone_dstSlotsMidAt spillSlotsAt at hnext
  unfold dstSlotsAt spillSlotsAt
  rw [chunks96_6QAt_sp_0xb40 s.sp sq0 sq1 sq2 sq3 sq4 sq5,
      segClone_chunks96_6QAt_sp_0xd38 s.sp dv.q0 dv.q1 dv.q2 dv.q3 dv.q4 dv.q5]
  rw [chunks96_6QAt_sp_0xb40 s.sp sq0 sq1 sq2 sq3 sq4 sq5,
      segClone_chunks96_6QAt_sp_0xd38 s.sp sq0 sq1 sq2 sq3 sq4 sq5] at hnext
  simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hnext ⊢
  apply SepWPp.of_sepWP (mid := (blkPl_197).base + 1568#64)
  wp_steps
  refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
  refine SepWPp.weaken_pre ?_
    (hnext _ (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      (by segCloneAssemble_close) (by segCloneAssemble_close))
  exact Entails.of_eq (by ac_rfl)

/-- Relocatable `[LibsignalPlacement]` second half of destination slot assembly and version check (`+0x620 → +0x69c / +0x7e4`, 31 instructions). -/
theorem segClone_assemble_2_placed [lsmpl : LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)} {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (dv : DstVals) (localIk' remoteIk' : VecGhost) (rootPtr' chainsCap' chainsPtr' : BitVec 64)
    (alice' : VecGhost) (pqCap' pqPtr' scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (kybCap' kybPtr' v08 : BitVec 64) (w14 : BitVec 32) (pendCap' pendPtr' : BitVec 64)
    (w24 w28 w2c w288 w28c : BitVec 32) (F : SepProp)
    (hpc : s.pc = (blkPl_197).base + 1568#64) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = w2c.setWidth 64) (hx9 : s.readReg64 .x9 = w28.setWidth 64)
    (hx10 : s.readReg64 .x10 = x.st.previousCounter.setWidth 64)
    (hx19 : s.readReg64 .x19 = kybCap') (hx20 : s.readReg64 .x20 = pqCap')
    (hx21 : s.readReg64 .x21 = w288.setWidth 64) (hx22 : s.readReg64 .x22 = pqPtr')
    (hx23 : s.readReg64 .x23 = w28c.setWidth 64) (_hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (hx25 : s.readReg64 .x25 = alice'.cap) (hx26 : s.readReg64 .x26 = pendCap')
    (hx27 : s.readReg64 .x27 = alice'.ptr)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ s1 : State,
      s1.pc = (if x.st.version.toNat = x.msg.messageVersion.toNat then
                 (blkPl_197).base + 1692#64 else (blkPl_197).base + 2020#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x9 = x.msg.messageVersion.setWidth 64 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp ((blkPC_197).rebase (blkPl_197).base H) ret s1
        (segClone_dstSlotsWrittenAt s.sp localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
          pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w28 w2c v08 w24
          kybCap' kybPtr' w14 x.st.sessionVersion x.st.previousCounter w288 w28c ∗
          spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
            scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗
          ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
        Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0)) :
    SepWPp ((blkPC_197).rebase (blkPl_197).base H) ret s
      (segClone_dstSlotsMidAt s.sp dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
        scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendPtr' ∗
        spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
          scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr localIk'.cap ∗
        ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
      Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  have hver_eq_iff :
      x.st.version.toNat = x.msg.messageVersion.toNat ↔
        (if x.st.sessionVersion = 0 then 2 else x.st.sessionVersion) =
          x.msg.messageVersion.setWidth 32 := by
    unfold SessionState.version
    constructor
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [h, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.msg.messageVersion.isLt; omega)]
    · intro h
      have ht := congrArg BitVec.toNat h
      rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.msg.messageVersion.isLt; omega)] at ht
  have hpc_ver :
      (if (if x.st.sessionVersion = 0 then 2#64 else BitVec.truncate 64 x.st.sessionVersion) =
          BitVec.zeroExtend 64 x.msg.messageVersion then (blkPl_197).base + 1692#64 else (blkPl_197).base + 2020#64) =
      (if x.st.version.toNat = x.msg.messageVersion.toNat then (blkPl_197).base + 1692#64 else (blkPl_197).base + 2020#64) := by
    simp only [segClone_version_cond_iff, ← hver_eq_iff]
  unfold segClone_dstSlotsWrittenAt spillSlotsAt at hnext
  unfold segClone_dstSlotsMidAt spillSlotsAt
  simp only [sepConj_assoc] at hnext ⊢
  apply SepWPp.of_sepWP
    (mid := if x.st.version.toNat = x.msg.messageVersion.toNat then (blkPl_197).base + 1692#64 else (blkPl_197).base + 2020#64)
  wp_steps
  refine SepWP.done (by simpa using hpc_ver) (by exact hrun) ?_
  refine SepWPp.weaken_pre ?_
    (hnext _ (by simpa using hpc_ver) (by exact hrun) rfl hsp rfl rfl (by segCloneAssemble_close))
  exact Entails.of_eq (by ac_rfl)

theorem segClone_fields_10_to_11_placed [lsmpl : LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)} {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (dv : DstVals) (localIk' remoteIk' : VecGhost) (rootPtr' chainsCap' chainsPtr' : BitVec 64)
    (alice' : VecGhost) (pqCap' pqPtr' scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (kybCap' kybPtr' v08 : BitVec 64) (w14 : BitVec 32) (pendCap' pendPtr' : BitVec 64)
    (w24 w28 w2c w288 w28c : BitVec 32) (F : SepProp)
    (hpc : s.pc = (blkPl_197).base + 1428#64) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = kybCap') (hx20 : s.readReg64 .x20 = pqCap')
    (hx21 : s.readReg64 .x21 = w288.setWidth 64) (hx22 : s.readReg64 .x22 = pqPtr')
    (hx23 : s.readReg64 .x23 = w28c.setWidth 64) (hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (hx25 : s.readReg64 .x25 = alice'.cap) (hx26 : s.readReg64 .x26 = pendCap')
    (hx27 : s.readReg64 .x27 = alice'.ptr) (hx28 : s.readReg64 .x28 = chainsPtr')
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ s1 : State,
      s1.pc = (if x.st.version.toNat = x.msg.messageVersion.toNat then
                 (blkPl_197).base + 1692#64 else (blkPl_197).base + 2020#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x9 = x.msg.messageVersion.setWidth 64 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp ((blkPC_197).rebase (blkPl_197).base H) ret s1
        (segClone_dstSlotsWrittenAt s.sp localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
          pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w28 w2c v08 w24
          kybCap' kybPtr' w14 x.st.sessionVersion x.st.previousCounter w288 w28c ∗
          chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
            scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗
          ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
        Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0)) :
    SepWPp ((blkPC_197).rebase (blkPl_197).base H) ret s
      (dstSlotsAt s.sp dv ∗
        chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
          scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr localIk'.cap ∗
        ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
      Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  refine segClone_assemble_1_placed dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
    scCap' sq0 sq1 sq2 sq3 sq4 sq5 kybPtr' v08 w14 pendPtr' w24 w28 w2c
    x.st.sessionVersion x.st.previousCounter
    (((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
    hpc hrun hsp hx24 hx28 htr
    fun s1 hpc1 hrun1 hsp1 hspA1 hx8_1 hx9_1 hx10_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx29_1 htr1 => ?_
  rw [← hsp1] at hx24_1 ⊢
  refine SepWPp.weaken_pre
    (P' := segClone_dstSlotsMidAt s1.sp dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
            scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendPtr' ∗
          spillSlotsAt s1.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
            scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗
          ((s1.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
          (chunks96_6QAt (s1.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine segClone_assemble_2_placed dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
    pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 kybCap' kybPtr' v08 w14 pendCap' pendPtr'
    w24 w28 w2c w288 w28c
    (chunks96_6QAt (s1.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗ F)
    hpc1 hrun1 hspA1 hx8_1 hx9_1 hx10_1
    (by reg_chain) (by reg_chain) (by reg_chain)
    (by reg_chain) (by reg_chain) hx24_1
    (by reg_chain) (by reg_chain) (by reg_chain) htr1
    fun s2 hpc2 hrun2 hsp2 hspA2 hx9_2 hx29_2 htr2 => ?_
  rw [hsp1]
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext s2 hpc2 hrun2 (by reg_chain) hspA2 hx9_2 (by reg_chain) htr2)

end CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
