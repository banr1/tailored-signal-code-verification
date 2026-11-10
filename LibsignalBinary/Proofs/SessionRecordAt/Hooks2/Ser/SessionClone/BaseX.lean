/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymD
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymE
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneFetch
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SepWPpIn
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Fetch
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `SessionStructure::clone` (`0x240f0`): Stack Layout and Panic/Callee Helpers

Defines the stack decomposition `scSubStackX` below `sp0 - 0x1d0`, extern/callee address bridges,
and allocation-failure panic lemmas for `<SessionStructure as Clone>::clone` (`0x240f0`, Block `80`)
on `SP2Ext` and under relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization.SessionCloneAux

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.E2E.Record.Serialization
open Proofs.libsignal
open Proofs.libsignal.Hooks2
open Proofs.libsignal.Stage1X
open ProofLib.ProgramReflection

set_option maxRecDepth 500000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg
  updateCalleeSavedVRegs

abbrev _root_.Arm64.State.calleeSavedVRegs (s : Arm64.State) :=
  Arm64.calleeSavedVRegs s

@[local arm64_norm, local wp_norm]
theorem _root_.Arm64.State.calleeSavedVRegs_writeReg64_gpr (s : Arm64.State) (idx : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) v).calleeSavedVRegs = s.calleeSavedVRegs :=
  Arm64.calleeSavedVRegs_writeReg64 s (Reg.gpr idx) v

@[local arm64_norm, local wp_norm]
theorem _root_.Arm64.State.calleeSavedVRegs_writeReg32_gpr (s : Arm64.State) (idx : BitVec 5) (v : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) v).calleeSavedVRegs = s.calleeSavedVRegs :=
  Arm64.calleeSavedVRegs_writeReg32 s (Reg.gpr idx) v

@[local arm64_norm, local wp_norm]
theorem _root_.Arm64.State.calleeSavedVRegs_setPC (s : Arm64.State) (pc : BitVec 64) :
    (s.setPC pc).calleeSavedVRegs = s.calleeSavedVRegs :=
  Arm64.calleeSavedVRegs_setPC s pc

@[local arm64_norm, local wp_norm]
theorem _root_.Arm64.State.calleeSavedVRegs_setPState (s : Arm64.State) (ps : PState) :
    (s.setPState ps).calleeSavedVRegs = s.calleeSavedVRegs :=
  Arm64.calleeSavedVRegs_setPState s ps

theorem L1_SessionCloneBaseX : True := trivial

/-! ## Extern hooks, callee address bridges, and panic tails -/

theorem sc_shim_ok_at_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr sessionCloneName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      (Proofs.libsignal.Stage1X.session2ShimSpecX.inImage img) :=
  hC.alloc.shim_ok_at sessionCloneName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
    (by fnoff_eq)

theorem sc_alloc_ok_at_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr sessionCloneName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      ((Proofs.libsignal.Stage1X.rustAllocSpecWithStack A Stage1X.extHookStack).inImage img) :=
  hC.alloc.alloc_ok_at sessionCloneName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
    (by fnoff_eq)

theorem sc_memcpy_ok_at_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr sessionCloneName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      ((LibsignalTripleRatchet.sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img) :=
  hC.memcpy_ok_at sessionCloneName (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
    (by fnoff_eq)

theorem sc_panic_at_handle_error_x {b : BitVec 64} {ext : String → Option (State → State)} :
    (SP2Ext b ext).externAt?
      ((SP2Ext b ext).fnAddr sessionCloneName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")) =
      some Rust.panicked :=
  panic_at_handle_error_ext (b := b) (ext := ext) libsignalSessionCode_fnOff_sym_240f0
    (by fnoff_eq)

theorem fnAddr_sessionClone_to_chainCloneLocal1_x (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr sessionCloneName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone") =
      (SP2Ext b ext).fnAddr chainCloneLocal1Name := by
  have h1 := libsignalSessionCode_fnOff_sym_240f0
  have h2 := libsignalSessionCode_fnOff_sym_24848
  simp only [SP2Ext, contractProg, Program.fnAddr_rebase, sessionCloneName, chainCloneLocal1Name, h1, h2]
  bv_lin

theorem sc_chainClone_ok_at_x {img : Obj.Image} {ext : String → Option (State → State)}
    {α : Type} (spec : Spec α)
    (hcc : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr chainCloneLocal1Name) (spec.inImage img)) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr sessionCloneName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      (spec.inImage img) := by
  rwa [fnAddr_sessionClone_to_chainCloneLocal1_x]

abbrev scPanicPostX (A : RustAlloc) (x : SessionCloneGhost) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (sessionCloneSpecX A).onPanic x s0 sf ∗ R)

theorem sc_onPanic_of_allocFailed_x {A : RustAlloc} {x : SessionCloneGhost}
    {R P_f : SepProp} {s0 sf : State}
    (halloc : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
    (hm : sf.mem ⊨ P_f ∗ R) :
    sf.mem ⊨ (sessionCloneSpecX A).onPanic x s0 sf ∗ R := by
  dsimp only [sessionCloneSpecX, allocPanic]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨halloc, ?_⟩
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap P_f)) hm

theorem sc_onPanic_of_callee_panic_x {A : RustAlloc} {x : SessionCloneGhost}
    {F R : SepProp} {s0 s_call sf : State}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (sessionCloneSpecX A).onPanic x s0 sf ∗ R := by
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  obtain ⟨⟨haf, hpre⟩, hm'⟩ := hm
  unfold allocFailedIn at haf
  rw [htr] at haf hpre
  rw [← sepConj_assoc] at hm'
  exact sc_onPanic_of_allocFailed_x ⟨haf, hpre⟩ hm'

/-! ## Allocation-failure panic steps on `SP2Ext` -/

set_option maxHeartbeats 1600000 in
theorem sc_panic_0x474_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr sessionCloneName + 0x474#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q (scPanicPostX A x R s0) := by
  intro _ _
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  have hpanic := sc_panic_at_handle_error_x (b := img.base) (ext := ext)
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x474 12
  clear hfn
  unfold SP2Ext at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  exact sc_onPanic_of_allocFailed_x (Record.SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

set_option maxHeartbeats 1600000 in
theorem sc_panic_0x480_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr sessionCloneName + 0x480#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q (scPanicPostX A x R s0) := by
  intro _ _
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  have hpanic := sc_panic_at_handle_error_x (b := img.base) (ext := ext)
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x480 12
  clear hfn
  unfold SP2Ext at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  exact sc_onPanic_of_allocFailed_x (Record.SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

set_option maxHeartbeats 1600000 in
theorem sc_panic_0x48c_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr sessionCloneName + 0x48c#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q (scPanicPostX A x R s0) := by
  intro _ _
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  have hpanic := sc_panic_at_handle_error_x (b := img.base) (ext := ext)
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x48c 12
  clear hfn
  unfold SP2Ext at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  exact sc_onPanic_of_allocFailed_x (Record.SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

set_option maxHeartbeats 1600000 in
theorem sc_panic_0x498_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr sessionCloneName + 0x498#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q (scPanicPostX A x R s0) := by
  intro _ _
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  have hpanic := sc_panic_at_handle_error_x (b := img.base) (ext := ext)
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x498 12
  clear hfn
  unfold SP2Ext at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  exact sc_onPanic_of_allocFailed_x (Record.SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

set_option maxHeartbeats 1600000 in
theorem sc_panic_0x4a4_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr sessionCloneName + 0x4a4#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q (scPanicPostX A x R s0) := by
  intro _ _
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  have hpanic := sc_panic_at_handle_error_x (b := img.base) (ext := ext)
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x4a4 12
  clear hfn
  unfold SP2Ext at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  exact sc_onPanic_of_allocFailed_x (Record.SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

set_option maxHeartbeats 1600000 in
theorem sc_panic_0x4b0_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr sessionCloneName + 0x4b0#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q (scPanicPostX A x R s0) := by
  intro _ _
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  have hpanic := sc_panic_at_handle_error_x (b := img.base) (ext := ext)
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x4b0 12
  clear hfn
  unfold SP2Ext at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  exact sc_onPanic_of_allocFailed_x (Record.SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

/-! ## Stack decomposition at `sessionCloneStackX` -/

/-- Sub-stack budget below `sp0 - 0x1d0#64` (`sessionCloneStackX - 0x1d0`). -/
abbrev scSubStackX : Nat := 0xd0 + 0x400 + Stage1X.extHookStack

/-- Decomposition of `stackAt sp0 sessionCloneStackX` around `sp := sp0 - 0x1d0#64`. -/
theorem stackAt_sessionClone_eq_x (sp0 : BitVec 64) :
    stackAt sp0 sessionCloneStackX =
      let sp := sp0 - 0x1d0#64
      memRegion (sp0 - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
      stackAt sp (0xd0 + Stage1X.extHookStack) ∗
      memRegion sp 0x90 ∗
      memRegion (sp + 0x90#64) 96 ∗
      memRegion (sp + 0xf0#64) 8 ∗
      memRegion (sp + 0xf8#64) 104 ∗
      memRegion (sp + 0x160#64) 16 ∗
      memRegion (sp + 0x170#64) 0x60 := by
  dsimp only
  unfold stackAt
  set sp := sp0 - 0x1d0#64
  have hsplit : sessionCloneStackX = 0x400 + (0xd0 + Stage1X.extHookStack) + 0x1d0 := by decide
  rw [memRegion_split' (b := sp0 - BitVec.ofNat 64 sessionCloneStackX)
        (b' := sp - BitVec.ofNat 64 (0xd0 + Stage1X.extHookStack)) (n := 0x400)
        (k := (0xd0 + Stage1X.extHookStack) + 0x1d0)
        (by decide) (by dsimp [sp, sessionCloneStackX]; bv_arith) (by decide),
      memRegion_split' (b := sp - BitVec.ofNat 64 (0xd0 + Stage1X.extHookStack))
        (b' := sp) (n := 0xd0 + Stage1X.extHookStack) (k := 0x1d0)
        rfl (by dsimp [sp, sessionCloneStackX]; bv_arith) (by decide),
      memRegion_split' (b := sp) (b' := sp + 0x90#64) (n := 0x90) (k := 320) rfl rfl (by decide),
      memRegion_split' (b := sp + 0x90#64) (b' := sp + 0xf0#64) (n := 96) (k := 224) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0xf0#64) (b' := sp + 0xf8#64) (n := 8) (k := 216) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0xf8#64) (b' := sp + 0x160#64) (n := 104) (k := 112) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x160#64) (b' := sp + 0x170#64) (n := 16) (k := 96) rfl (by bv_arith) (by decide)]

/-! ## Relocatable `[LibsignalPlacement]` helpers and bridges (Block `80`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem sc_shim_placed_ok_at_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H) :
    subroutine_ok (lsProg_80 H) (lsρ CryptoVerification.lsRustNoAllocShimSym)
      (withLsCl lsmpl Proofs.libsignal.Stage1X.session2ShimSpecX) :=
  hC.alloc.shim (callerProg := lsProg_80 H)

theorem sc_alloc_placed_ok_at_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H) :
    subroutine_ok (lsProg_80 H) (lsρ CryptoVerification.lsRustAllocSym)
      (withLsCl lsmpl (Proofs.libsignal.Stage1X.rustAllocSpecWithStack A Stage1X.extHookStack)) :=
  hC.alloc.alloc (callerProg := lsProg_80 H)

theorem sc_memcpy_placed_ok_at_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H) :
    subroutine_ok (lsProg_80 H) (lsρ CryptoVerification.lsMemcpySym)
      (withLsCl lsmpl (LibsignalTripleRatchet.sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack)) :=
  hC.memcpy (callerProg := lsProg_80 H)

theorem sc_panic_at_handle_error_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H) :
    (lsProg_80 H).externAt? (lsρ CryptoVerification.lsHandleErrorSym) = some Rust.panicked :=
  sc_panic_at_handle_error_placed hC.alloc.panic_handle_error

theorem sc_chainClone_placed_ok_at_x [LibsignalPlacement] {H : LibsignalHooks}
    {α : Type} (spec : Spec α)
    (hcc : subroutine_ok (lsProg_82 H) (blkPl_82).base (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok (lsProg_80 H) (blkPl_82).base (withLsCodeLoaded lsmpl spec) :=
  ls_subroutine_ok_of_callee (callerProg := lsProg_80 H) hcc

theorem sc_panic_0x474_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hC : SerContractsXPlaced A H)
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_80).base + 1140#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s P Q (scPanicPostX A x R s0) :=
  fun _ => sc_panic_0x474_placed (A := A) (sc_panic_at_handle_error_placed_x hC) x s0 s P R hpc hrun htrace

theorem sc_panic_0x480_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hC : SerContractsXPlaced A H)
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_80).base + 1152#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s P Q (scPanicPostX A x R s0) :=
  fun _ => sc_panic_0x480_placed (A := A) (sc_panic_at_handle_error_placed_x hC) x s0 s P R hpc hrun htrace

theorem sc_panic_0x48c_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hC : SerContractsXPlaced A H)
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_80).base + 1164#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s P Q (scPanicPostX A x R s0) :=
  fun _ => sc_panic_0x48c_placed (A := A) (sc_panic_at_handle_error_placed_x hC) x s0 s P R hpc hrun htrace

theorem sc_panic_0x498_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hC : SerContractsXPlaced A H)
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_80).base + 1176#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s P Q (scPanicPostX A x R s0) :=
  fun _ => sc_panic_0x498_placed (A := A) (sc_panic_at_handle_error_placed_x hC) x s0 s P R hpc hrun htrace

theorem sc_panic_0x4a4_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hC : SerContractsXPlaced A H)
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_80).base + 1188#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s P Q (scPanicPostX A x R s0) :=
  fun _ => sc_panic_0x4a4_placed (A := A) (sc_panic_at_handle_error_placed_x hC) x s0 s P R hpc hrun htrace

theorem sc_panic_0x4b0_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hC : SerContractsXPlaced A H)
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_80).base + 1200#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s P Q (scPanicPostX A x R s0) :=
  fun _ => sc_panic_0x4b0_placed (A := A) (sc_panic_at_handle_error_placed_x hC) x s0 s P R hpc hrun htrace

end Placed

end CryptoVerification.E2E.Record.Serialization.SessionCloneAux
