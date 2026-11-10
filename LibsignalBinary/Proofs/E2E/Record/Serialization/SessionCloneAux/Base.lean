/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymD
public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Fetch
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WPp

/-!
# Base stack, heap, and hook helpers for `SessionStructure::clone` (`0x240f0`)
-/

@[expose] public section

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
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [arm64_norm, wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg

/-! ## External hooks, callee offsets, and panic tails -/

theorem sc_shim_ok_at_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr sessionCloneName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      LibsignalTripleRatchet.sessionShimSpec :=
  LibsignalTripleRatchet.shim_ok_at_trap b C abs sessionCloneName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
    (by fnoff_eq)

theorem sc_shim_ok_at {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      LibsignalTripleRatchet.sessionShimSpec :=
  subroutine_ok_kit_of_trTrap sc_shim_ok_at_trap

theorem sc_alloc_ok_at_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr sessionCloneName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      (rustAllocSpec A) :=
  LibsignalTripleRatchet.alloc_ok_at_trap b C A abs hA sessionCloneName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
    (by fnoff_eq)

theorem sc_alloc_ok_at {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      (rustAllocSpec A) :=
  subroutine_ok_kit_of_trTrap (sc_alloc_ok_at_trap hA)

theorem sc_memcpy_ok_at_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr sessionCloneName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      sessionMemcpyRegionSpec :=
  LibsignalTripleRatchet.session_memcpy_region_ok_at_trap b C abs sessionCloneName (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
    (by fnoff_eq)

theorem sc_memcpy_ok_at {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      sessionMemcpyRegionSpec :=
  subroutine_ok_kit_of_trTrap sc_memcpy_ok_at_trap

theorem sc_panic_at_handle_error_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} :
    (trTrapProgAt b C abs).externAt?
      ((trTrapProgAt b C abs).fnAddr sessionCloneName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")) =
      some Rust.panicked :=
  LibsignalTripleRatchet.panic_at_handle_error_trap b C abs sessionCloneName (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
    (by fnoff_eq)

theorem sc_panic_at_handle_error {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    (tripleRatchetProgAt b C ctl abs).externAt?
      ((tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")) =
      some Rust.panicked :=
  LibsignalTripleRatchet.panic_at_handle_error b C ctl abs sessionCloneName (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
    (by fnoff_eq)

theorem fnAddr_sessionClone_to_chainCloneLocal1_ext_trap {b : BitVec 64}
    {ext : String → Option (State → State)} :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone") =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr chainCloneLocal1Name := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    show libsignalSessionCode.fnOff sessionCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone") by fnoff_eq,
    show libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") by fnoff_eq]
  bv_omega

theorem fnAddr_sessionClone_to_chainCloneLocal1_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} :
    (trTrapProgAt b C abs).fnAddr sessionCloneName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone") =
      (trTrapProgAt b C abs).fnAddr chainCloneLocal1Name :=
  fnAddr_sessionClone_to_chainCloneLocal1_ext_trap

theorem fnAddr_sessionClone_to_chainCloneLocal1 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone") =
      (tripleRatchetProgAt b C ctl abs).fnAddr chainCloneLocal1Name :=
  fnAddr_sessionClone_to_chainCloneLocal1_ext_trap

theorem sc_chainClone_ok_at_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hcc : ChainCloneLocal1Ok_trap b C A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr sessionCloneName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      (chainCloneSpec A) := by
  rwa [fnAddr_sessionClone_to_chainCloneLocal1_trap]

theorem sc_chainClone_ok_at {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hcc : ChainCloneLocal1Ok b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      (chainCloneSpec A) := by
  rwa [fnAddr_sessionClone_to_chainCloneLocal1]

theorem sc_senderChainClone_ok_at_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hscc : SenderChainCloneLocal1Ok_trap b C A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr sessionCloneName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      (senderChainCloneSpec A) := by
  rwa [fnAddr_sessionClone_to_chainCloneLocal1_trap]

theorem sc_senderChainClone_ok_at {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hscc : SenderChainCloneLocal1Ok b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      (senderChainCloneSpec A) := by
  rwa [fnAddr_sessionClone_to_chainCloneLocal1]

structure ScExternKit_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  shim : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
    ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
    LibsignalTripleRatchet.sessionShimSpec
  alloc : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
    ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
    (rustAllocSpec A)
  memcpy : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
    ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
    sessionMemcpyRegionSpec
  panic_err : (libsignalSessionCode.rebase b (Rust.withPanics ext)).externAt?
    ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")) =
    some Rust.panicked

theorem scExternKit_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    ScExternKit_trap b A (trTrapExterns C abs) :=
  ⟨sc_shim_ok_at_trap, sc_alloc_ok_at_trap hA, sc_memcpy_ok_at_trap, sc_panic_at_handle_error_trap⟩

theorem scExternKit_kit_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    ScExternKit_trap b A (tripleRatchetExterns C ctl abs) :=
  ⟨sc_shim_ok_at, sc_alloc_ok_at hA, sc_memcpy_ok_at, sc_panic_at_handle_error⟩

abbrev scPanicPost (A : RustAlloc) (x : SessionCloneGhost) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (sessionCloneSpec A).onPanic x s0 sf ∗ R)

theorem sc_onPanic_of_allocFailed {A : RustAlloc} {x : SessionCloneGhost}
    {R P_f : SepProp} {s0 sf : State}
    (halloc : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
    (hm : sf.mem ⊨ P_f ∗ R) :
    sf.mem ⊨ (sessionCloneSpec A).onPanic x s0 sf ∗ R := by
  dsimp only [sessionCloneSpec, allocPanic]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨halloc, ?_⟩
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap P_f)) hm

theorem sc_onPanic_of_callee_panic {A : RustAlloc} {x : SessionCloneGhost}
    {F R : SepProp} {s0 s_call sf : State}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (sessionCloneSpec A).onPanic x s0 sf ∗ R := by
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  obtain ⟨⟨haf, hpre⟩, hm'⟩ := hm
  unfold allocFailedIn at haf
  rw [htr] at haf hpre
  rw [← sepConj_assoc] at hm'
  exact sc_onPanic_of_allocFailed ⟨haf, hpre⟩ hm'

theorem sc_panic_0x474_ext_trap {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hpanic : (libsignalSessionCode.rebase b (Rust.withPanics ext)).externAt?
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")) =
      some Rust.panicked)
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x474#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s P Q (scPanicPost A x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  sessionClone_fetches b (Rust.withPanics ext) hfn 0x474 12
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches; apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")); wp_steps
  refine SepWP.done rfl hrun (SepWPp.panic hrun hpanic fun hm => ?_)
  exact sc_onPanic_of_allocFailed (Record.SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem sc_panic_0x474_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x474#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (trTrapProgAt b C abs) ret s P Q (scPanicPost A x R s0) :=
  sc_panic_0x474_ext_trap sc_panic_at_handle_error_trap x s0 s P R hpc hrun htrace

theorem sc_panic_0x474 {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x474#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (scPanicPost A x R s0) :=
  sc_panic_0x474_ext_trap sc_panic_at_handle_error x s0 s P R hpc hrun htrace

theorem sc_panic_0x480_ext_trap {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hpanic : (libsignalSessionCode.rebase b (Rust.withPanics ext)).externAt?
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")) =
      some Rust.panicked)
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x480#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s P Q (scPanicPost A x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  sessionClone_fetches b (Rust.withPanics ext) hfn 0x480 12
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches; apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")); wp_steps
  refine SepWP.done rfl hrun (SepWPp.panic hrun hpanic fun hm => ?_)
  exact sc_onPanic_of_allocFailed (Record.SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem sc_panic_0x480_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x480#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (trTrapProgAt b C abs) ret s P Q (scPanicPost A x R s0) :=
  sc_panic_0x480_ext_trap sc_panic_at_handle_error_trap x s0 s P R hpc hrun htrace

theorem sc_panic_0x480 {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x480#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (scPanicPost A x R s0) :=
  sc_panic_0x480_ext_trap sc_panic_at_handle_error x s0 s P R hpc hrun htrace

theorem sc_panic_0x48c_ext_trap {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hpanic : (libsignalSessionCode.rebase b (Rust.withPanics ext)).externAt?
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")) =
      some Rust.panicked)
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x48c#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s P Q (scPanicPost A x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  sessionClone_fetches b (Rust.withPanics ext) hfn 0x48c 12
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches; apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")); wp_steps
  refine SepWP.done rfl hrun (SepWPp.panic hrun hpanic fun hm => ?_)
  exact sc_onPanic_of_allocFailed (Record.SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem sc_panic_0x48c_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x48c#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (trTrapProgAt b C abs) ret s P Q (scPanicPost A x R s0) :=
  sc_panic_0x48c_ext_trap sc_panic_at_handle_error_trap x s0 s P R hpc hrun htrace

theorem sc_panic_0x48c {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x48c#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (scPanicPost A x R s0) :=
  sc_panic_0x48c_ext_trap sc_panic_at_handle_error x s0 s P R hpc hrun htrace

theorem sc_panic_0x498_ext_trap {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hpanic : (libsignalSessionCode.rebase b (Rust.withPanics ext)).externAt?
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")) =
      some Rust.panicked)
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x498#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s P Q (scPanicPost A x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  sessionClone_fetches b (Rust.withPanics ext) hfn 0x498 12
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches; apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")); wp_steps
  refine SepWP.done rfl hrun (SepWPp.panic hrun hpanic fun hm => ?_)
  exact sc_onPanic_of_allocFailed (Record.SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem sc_panic_0x498_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x498#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (trTrapProgAt b C abs) ret s P Q (scPanicPost A x R s0) :=
  sc_panic_0x498_ext_trap sc_panic_at_handle_error_trap x s0 s P R hpc hrun htrace

theorem sc_panic_0x498 {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x498#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (scPanicPost A x R s0) :=
  sc_panic_0x498_ext_trap sc_panic_at_handle_error x s0 s P R hpc hrun htrace

theorem sc_panic_0x4a4_ext_trap {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hpanic : (libsignalSessionCode.rebase b (Rust.withPanics ext)).externAt?
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")) =
      some Rust.panicked)
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x4a4#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s P Q (scPanicPost A x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  sessionClone_fetches b (Rust.withPanics ext) hfn 0x4a4 12
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches; apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")); wp_steps
  refine SepWP.done rfl hrun (SepWPp.panic hrun hpanic fun hm => ?_)
  exact sc_onPanic_of_allocFailed (Record.SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem sc_panic_0x4a4_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x4a4#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (trTrapProgAt b C abs) ret s P Q (scPanicPost A x R s0) :=
  sc_panic_0x4a4_ext_trap sc_panic_at_handle_error_trap x s0 s P R hpc hrun htrace

theorem sc_panic_0x4a4 {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x4a4#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (scPanicPost A x R s0) :=
  sc_panic_0x4a4_ext_trap sc_panic_at_handle_error x s0 s P R hpc hrun htrace

theorem sc_panic_0x4b0_ext_trap {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hpanic : (libsignalSessionCode.rebase b (Rust.withPanics ext)).externAt?
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")) =
      some Rust.panicked)
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x4b0#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s P Q (scPanicPost A x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  sessionClone_fetches b (Rust.withPanics ext) hfn 0x4b0 12
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches; apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")); wp_steps
  refine SepWP.done rfl hrun (SepWPp.panic hrun hpanic fun hm => ?_)
  exact sc_onPanic_of_allocFailed (Record.SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem sc_panic_0x4b0_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x4b0#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (trTrapProgAt b C abs) ret s P Q (scPanicPost A x R s0) :=
  sc_panic_0x4b0_ext_trap sc_panic_at_handle_error_trap x s0 s P R hpc hrun htrace

theorem sc_panic_0x4b0 {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x4b0#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (scPanicPost A x R s0) :=
  sc_panic_0x4b0_ext_trap sc_panic_at_handle_error x s0 s P R hpc hrun htrace

/-! ## Frame-pointer and stack-offset normalization -/

@[arm64_norm, wp_norm]
theorem fp_sub_120 (sp : BitVec 64) :
    (sp + 0x170#64) - 120#64 = sp + 0xf8#64 := by bv_omega

@[arm64_norm, wp_norm]
theorem fp_add_neg_120 (sp : BitVec 64) :
    (sp + 0x170#64) + bv% (2 ^ 64 - 120) = sp + 0xf8#64 := by bv_omega

@[arm64_norm, wp_norm]
theorem fp_add_neg_120_hex (sp : BitVec 64) :
    (sp + 0x170#64) + 0xffffffffffffff88#64 = sp + 0xf8#64 := by bv_omega

@[arm64_norm, wp_norm]
theorem fp_add_neg_112_hex (sp : BitVec 64) :
    (sp + 0x170#64) + 0xffffffffffffff90#64 = sp + 0x100#64 := by bv_omega

@[arm64_norm, wp_norm]
theorem fp_add_neg_104_hex (sp : BitVec 64) :
    (sp + 0x170#64) + 0xffffffffffffff98#64 = sp + 0x108#64 := by bv_omega

@[arm64_norm, wp_norm]
theorem fp_add_neg_24 (sp : BitVec 64) :
    (sp + 0x170#64) + bv% (2 ^ 64 - 24) = sp + 0x158#64 := by bv_omega

theorem chunks104W6QAt_sp_0xf8 (sp : BitVec 64) (w0 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    chunks104W6QAt (sp + 0xf8#64) w0 q0 q1 q2 q3 q4 q5 =
      ((sp + 0xf8#64) ↦₆₄ w0) ∗
      (((sp + 0xf8#64) + 0x8#64) ↦₁₂₈ q0) ∗
      (((sp + 0xf8#64) + 0x18#64) ↦₁₂₈ q1) ∗
      (((sp + 0xf8#64) + 0x28#64) ↦₁₂₈ q2) ∗
      (((sp + 0xf8#64) + 0x38#64) ↦₁₂₈ q3) ∗
      (((sp + 0xf8#64) + 0x48#64) ↦₁₂₈ q4) ∗
      (((sp + 0xf8#64) + 0x58#64) ↦₁₂₈ q5) := rfl

theorem chunks96_6QAt_sp_0x90 (sp : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    chunks96_6QAt (sp + 0x90#64) q0 q1 q2 q3 q4 q5 =
      ((sp + 0x90#64) ↦₁₂₈ q0) ∗ ((sp + 0xa0#64) ↦₁₂₈ q1) ∗
      ((sp + 0xb0#64) ↦₁₂₈ q2) ∗ ((sp + 0xc0#64) ↦₁₂₈ q3) ∗
      ((sp + 0xd0#64) ↦₁₂₈ q4) ∗ ((sp + 0xe0#64) ↦₁₂₈ q5) := by
  unfold chunks96_6QAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem chunks104_6QWAt_sp_0xf8 (sp : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    chunks104_6QWAt (sp + 0xf8#64) q0 q1 q2 q3 q4 q5 w6 =
      ((sp + 0xf8#64) ↦₁₂₈ q0) ∗
      ((sp + 0x108#64) ↦₁₂₈ q1) ∗
      ((sp + 0x118#64) ↦₁₂₈ q2) ∗
      ((sp + 0x128#64) ↦₁₂₈ q3) ∗
      ((sp + 0x138#64) ↦₁₂₈ q4) ∗
      ((sp + 0x148#64) ↦₁₂₈ q5) ∗
      ((sp + 0x158#64) ↦₆₄ w6) := by
  unfold chunks104_6QWAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-! ## Stack frame, spill slots, and saved registers -/

/-- Spatial layout of the 144-byte spill area `sp .. sp + 0x90` in `SessionStructure::clone`. -/
def scSpillSlotsAt (sp : BitVec 64)
    (v0c : BitVec 32) (v10 v18 v20 : BitVec 64)
    (v28 v2c : BitVec 32) (v30 : BitVec 64) (v3c : BitVec 32)
    (v40 v48 : BitVec 64) (v54 : BitVec 32) (v58 v60 v68 v70 v78 : BitVec 64)
    (v84 : BitVec 32) (v88 : BitVec 64) : SepProp :=
  memRegion sp 12 ∗ ((sp + 0x0c#64) ↦₃₂ v0c) ∗
  ((sp + 0x10#64) ↦₆₄ v10) ∗ ((sp + 0x18#64) ↦₆₄ v18) ∗ ((sp + 0x20#64) ↦₆₄ v20) ∗
  ((sp + 0x28#64) ↦₃₂ v28) ∗ ((sp + 0x2c#64) ↦₃₂ v2c) ∗
  ((sp + 0x30#64) ↦₆₄ v30) ∗
  memRegion (sp + 0x38#64) 4 ∗ ((sp + 0x3c#64) ↦₃₂ v3c) ∗
  ((sp + 0x40#64) ↦₆₄ v40) ∗ ((sp + 0x48#64) ↦₆₄ v48) ∗
  memRegion (sp + 0x50#64) 4 ∗ ((sp + 0x54#64) ↦₃₂ v54) ∗
  ((sp + 0x58#64) ↦₆₄ v58) ∗ ((sp + 0x60#64) ↦₆₄ v60) ∗
  ((sp + 0x68#64) ↦₆₄ v68) ∗ ((sp + 0x70#64) ↦₆₄ v70) ∗ ((sp + 0x78#64) ↦₆₄ v78) ∗
  memRegion (sp + 0x80#64) 4 ∗ ((sp + 0x84#64) ↦₃₂ v84) ∗
  ((sp + 0x88#64) ↦₆₄ v88)

structure ScSpillVals where
  v0c : BitVec 32
  v10 : BitVec 64
  v18 : BitVec 64
  v20 : BitVec 64
  v28 : BitVec 32
  v2c : BitVec 32
  v30 : BitVec 64
  v3c : BitVec 32
  v40 : BitVec 64
  v48 : BitVec 64
  v54 : BitVec 32
  v58 : BitVec 64
  v60 : BitVec 64
  v68 : BitVec 64
  v70 : BitVec 64
  v78 : BitVec 64
  v84 : BitVec 32
  v88 : BitVec 64

theorem memRegion_0x90_entails_scSpillSlotsAt (sp : BitVec 64) :
    memRegion sp 0x90 ⊢
      ∃∗ sv : ScSpillVals,
        scSpillSlotsAt sp sv.v0c sv.v10 sv.v18 sv.v20 sv.v28 sv.v2c sv.v30 sv.v3c
          sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78 sv.v84 sv.v88 := by
  rw [← sepConj_emp (memRegion sp 0x90)]
  refine elim_region_skip (b' := sp + 0x0c#64) (n := 12) (rem := 132) rfl rfl (by decide) ?_
  refine elim_region4 (b' := sp + 0x10#64) (rem := 128) rfl (by bv_arith) (by decide) fun v0c => ?_
  refine elim_region8 (b' := sp + 0x18#64) (rem := 120) rfl (by bv_arith) (by decide) fun v10 => ?_
  refine elim_region8 (b' := sp + 0x20#64) (rem := 112) rfl (by bv_arith) (by decide) fun v18 => ?_
  refine elim_region8 (b' := sp + 0x28#64) (rem := 104) rfl (by bv_arith) (by decide) fun v20 => ?_
  refine elim_region4 (b' := sp + 0x2c#64) (rem := 100) rfl (by bv_arith) (by decide) fun v28 => ?_
  refine elim_region4 (b' := sp + 0x30#64) (rem := 96) rfl (by bv_arith) (by decide) fun v2c => ?_
  refine elim_region8 (b' := sp + 0x38#64) (rem := 88) rfl (by bv_arith) (by decide) fun v30 => ?_
  refine elim_region_skip (b' := sp + 0x3c#64) (n := 4) (rem := 84) rfl (by bv_arith) (by decide) ?_
  refine elim_region4 (b' := sp + 0x40#64) (rem := 80) rfl (by bv_arith) (by decide) fun v3c => ?_
  refine elim_region8 (b' := sp + 0x48#64) (rem := 72) rfl (by bv_arith) (by decide) fun v40 => ?_
  refine elim_region8 (b' := sp + 0x50#64) (rem := 64) rfl (by bv_arith) (by decide) fun v48 => ?_
  refine elim_region_skip (b' := sp + 0x54#64) (n := 4) (rem := 60) rfl (by bv_arith) (by decide) ?_
  refine elim_region4 (b' := sp + 0x58#64) (rem := 56) rfl (by bv_arith) (by decide) fun v54 => ?_
  refine elim_region8 (b' := sp + 0x60#64) (rem := 48) rfl (by bv_arith) (by decide) fun v58 => ?_
  refine elim_region8 (b' := sp + 0x68#64) (rem := 40) rfl (by bv_arith) (by decide) fun v60 => ?_
  refine elim_region8 (b' := sp + 0x70#64) (rem := 32) rfl (by bv_arith) (by decide) fun v68 => ?_
  refine elim_region8 (b' := sp + 0x78#64) (rem := 24) rfl (by bv_arith) (by decide) fun v70 => ?_
  refine elim_region8 (b' := sp + 0x80#64) (rem := 16) rfl (by bv_arith) (by decide) fun v78 => ?_
  refine elim_region_skip (b' := sp + 0x84#64) (n := 4) (rem := 12) rfl (by bv_arith) (by decide) ?_
  refine elim_region4 (b' := sp + 0x88#64) (rem := 8) rfl (by bv_arith) (by decide) fun v84 => ?_
  refine elim_region8 (b' := sp + 0x90#64) (rem := 0) rfl (by bv_arith) (by decide) fun v88 => ?_
  rw [ProofLib.memRegion_zero]
  refine Entails.sepExists_right
    ⟨v0c, v10, v18, v20, v28, v2c, v30, v3c, v40, v48, v54, v58, v60, v68, v70, v78, v84, v88⟩ ?_
  unfold scSpillSlotsAt
  exact Entails.of_eq (by ac_rfl)

theorem scSpillSlotsAt_entails_memRegion_0x90 (sp : BitVec 64)
    (v0c : BitVec 32) (v10 v18 v20 : BitVec 64)
    (v28 v2c : BitVec 32) (v30 : BitVec 64) (v3c : BitVec 32)
    (v40 v48 : BitVec 64) (v54 : BitVec 32) (v58 v60 v68 v70 v78 : BitVec 64)
    (v84 : BitVec 32) (v88 : BitVec 64) :
    scSpillSlotsAt sp v0c v10 v18 v20 v28 v2c v30 v3c
      v40 v48 v54 v58 v60 v68 v70 v78 v84 v88 ⊢
      memRegion sp 0x90 := by
  unfold scSpillSlotsAt
  rw [memRegion_split' (b := sp) (b' := sp + 0x0c#64) (n := 12) (k := 132) rfl rfl (by decide),
      memRegion_split' (b := sp + 0x0c#64) (b' := sp + 0x10#64) (n := 4) (k := 128) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x10#64) (b' := sp + 0x18#64) (n := 8) (k := 120) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x18#64) (b' := sp + 0x20#64) (n := 8) (k := 112) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x20#64) (b' := sp + 0x28#64) (n := 8) (k := 104) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x28#64) (b' := sp + 0x2c#64) (n := 4) (k := 100) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x2c#64) (b' := sp + 0x30#64) (n := 4) (k := 96) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x30#64) (b' := sp + 0x38#64) (n := 8) (k := 88) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x38#64) (b' := sp + 0x3c#64) (n := 4) (k := 84) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3c#64) (b' := sp + 0x40#64) (n := 4) (k := 80) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x40#64) (b' := sp + 0x48#64) (n := 8) (k := 72) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x48#64) (b' := sp + 0x50#64) (n := 8) (k := 64) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x50#64) (b' := sp + 0x54#64) (n := 4) (k := 60) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x54#64) (b' := sp + 0x58#64) (n := 4) (k := 56) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x58#64) (b' := sp + 0x60#64) (n := 8) (k := 48) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x60#64) (b' := sp + 0x68#64) (n := 8) (k := 40) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x68#64) (b' := sp + 0x70#64) (n := 8) (k := 32) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x70#64) (b' := sp + 0x78#64) (n := 8) (k := 24) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x78#64) (b' := sp + 0x80#64) (n := 8) (k := 16) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x80#64) (b' := sp + 0x84#64) (n := 4) (k := 12) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x84#64) (b' := sp + 0x88#64) (n := 4) (k := 8) rfl (by bv_arith) (by decide)]
  refine sepConj_mono (Entails.refl _) <|
    sepConj_mono (pointsTo32_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo32_entails_memRegion _ _) <|
    sepConj_mono (pointsTo32_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (Entails.refl _) <|
    sepConj_mono (pointsTo32_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (Entails.refl _) <|
    sepConj_mono (pointsTo32_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (Entails.refl _) <|
    sepConj_mono (pointsTo32_entails_memRegion _ _) <|
    pointsTo64_entails_memRegion _ _

/-- Callee-saved register save area `sp + 0x170 .. sp + 0x1d0` (96 bytes). -/
def scSavedRegsAt (sp : BitVec 64)
    (r29 r30 r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 : BitVec 64) : SepProp :=
  ((sp + 0x170#64) ↦₆₄ r29) ∗ ((sp + 0x178#64) ↦₆₄ r30) ∗
  ((sp + 0x180#64) ↦₆₄ r28) ∗ ((sp + 0x188#64) ↦₆₄ r27) ∗
  ((sp + 0x190#64) ↦₆₄ r26) ∗ ((sp + 0x198#64) ↦₆₄ r25) ∗
  ((sp + 0x1a0#64) ↦₆₄ r24) ∗ ((sp + 0x1a8#64) ↦₆₄ r23) ∗
  ((sp + 0x1b0#64) ↦₆₄ r22) ∗ ((sp + 0x1b8#64) ↦₆₄ r21) ∗
  ((sp + 0x1c0#64) ↦₆₄ r20) ∗ ((sp + 0x1c8#64) ↦₆₄ r19)

structure ScSavedVals where
  r29 : BitVec 64
  r30 : BitVec 64
  r28 : BitVec 64
  r27 : BitVec 64
  r26 : BitVec 64
  r25 : BitVec 64
  r24 : BitVec 64
  r23 : BitVec 64
  r22 : BitVec 64
  r21 : BitVec 64
  r20 : BitVec 64
  r19 : BitVec 64

theorem memRegion_0x170_0x60_entails_scSavedRegsAt (sp : BitVec 64) :
    memRegion (sp + 0x170#64) 0x60 ⊢
      ∃∗ rv : ScSavedVals,
        scSavedRegsAt sp rv.r29 rv.r30 rv.r28 rv.r27 rv.r26 rv.r25
          rv.r24 rv.r23 rv.r22 rv.r21 rv.r20 rv.r19 := by
  rw [← sepConj_emp (memRegion (sp + 0x170#64) 0x60)]
  refine elim_region8 (b' := sp + 0x178#64) (rem := 88) rfl (by bv_arith) (by decide) fun r29 => ?_
  refine elim_region8 (b' := sp + 0x180#64) (rem := 80) rfl (by bv_arith) (by decide) fun r30 => ?_
  refine elim_region8 (b' := sp + 0x188#64) (rem := 72) rfl (by bv_arith) (by decide) fun r28 => ?_
  refine elim_region8 (b' := sp + 0x190#64) (rem := 64) rfl (by bv_arith) (by decide) fun r27 => ?_
  refine elim_region8 (b' := sp + 0x198#64) (rem := 56) rfl (by bv_arith) (by decide) fun r26 => ?_
  refine elim_region8 (b' := sp + 0x1a0#64) (rem := 48) rfl (by bv_arith) (by decide) fun r25 => ?_
  refine elim_region8 (b' := sp + 0x1a8#64) (rem := 40) rfl (by bv_arith) (by decide) fun r24 => ?_
  refine elim_region8 (b' := sp + 0x1b0#64) (rem := 32) rfl (by bv_arith) (by decide) fun r23 => ?_
  refine elim_region8 (b' := sp + 0x1b8#64) (rem := 24) rfl (by bv_arith) (by decide) fun r22 => ?_
  refine elim_region8 (b' := sp + 0x1c0#64) (rem := 16) rfl (by bv_arith) (by decide) fun r21 => ?_
  refine elim_region8 (b' := sp + 0x1c8#64) (rem := 8) rfl (by bv_arith) (by decide) fun r20 => ?_
  refine elim_region8 (b' := sp + 0x1d0#64) (rem := 0) rfl (by bv_arith) (by decide) fun r19 => ?_
  rw [ProofLib.memRegion_zero]
  refine Entails.sepExists_right ⟨r29, r30, r28, r27, r26, r25, r24, r23, r22, r21, r20, r19⟩ ?_
  unfold scSavedRegsAt
  exact Entails.of_eq (by ac_rfl)

theorem scSavedRegsAt_entails_memRegion_0x170_0x60 (sp : BitVec 64)
    (r29 r30 r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    scSavedRegsAt sp r29 r30 r28 r27 r26 r25 r24 r23 r22 r21 r20 r19 ⊢
      memRegion (sp + 0x170#64) 0x60 := by
  unfold scSavedRegsAt
  rw [memRegion_split' (b := sp + 0x170#64) (b' := sp + 0x178#64) (n := 8) (k := 88) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x178#64) (b' := sp + 0x180#64) (n := 8) (k := 80) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x180#64) (b' := sp + 0x188#64) (n := 8) (k := 72) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x188#64) (b' := sp + 0x190#64) (n := 8) (k := 64) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x190#64) (b' := sp + 0x198#64) (n := 8) (k := 56) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x198#64) (b' := sp + 0x1a0#64) (n := 8) (k := 48) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x1a0#64) (b' := sp + 0x1a8#64) (n := 8) (k := 40) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x1a8#64) (b' := sp + 0x1b0#64) (n := 8) (k := 32) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x1b0#64) (b' := sp + 0x1b8#64) (n := 8) (k := 24) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x1b8#64) (b' := sp + 0x1c0#64) (n := 8) (k := 16) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x1c0#64) (b' := sp + 0x1c8#64) (n := 8) (k := 8) rfl (by bv_arith) (by decide)]
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    pointsTo64_entails_memRegion _ _

theorem stackAt_sessionClone_eq (sp0 : BitVec 64) :
    stackAt sp0 sessionCloneStack =
      let sp := sp0 - 0x1d0#64
      memRegion (sp0 - BitVec.ofNat 64 sessionCloneStack) 0x400 ∗
      stackAt sp chainCloneStack ∗
      memRegion sp 0x90 ∗
      memRegion (sp + 0x90#64) 96 ∗
      memRegion (sp + 0xf0#64) 8 ∗
      memRegion (sp + 0xf8#64) 104 ∗
      memRegion (sp + 0x160#64) 16 ∗
      memRegion (sp + 0x170#64) 0x60 := by
  dsimp only
  unfold stackAt
  set sp := sp0 - 0x1d0#64
  rw [memRegion_split' (b := sp0 - BitVec.ofNat 64 sessionCloneStack)
        (b' := sp - BitVec.ofNat 64 chainCloneStack) (n := 0x400) (k := chainCloneStack + 0x1d0)
        (by decide) (by dsimp [sp, sessionCloneStack, chainCloneStack, allocHookStack]; bv_arith) (by decide),
      memRegion_split' (b := sp - BitVec.ofNat 64 chainCloneStack)
        (b' := sp) (n := chainCloneStack) (k := 0x1d0)
        rfl (by dsimp [sp, chainCloneStack, allocHookStack]; bv_arith) (by decide),
      memRegion_split' (b := sp) (b' := sp + 0x90#64) (n := 0x90) (k := 320) rfl rfl (by decide),
      memRegion_split' (b := sp + 0x90#64) (b' := sp + 0xf0#64) (n := 96) (k := 224) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0xf0#64) (b' := sp + 0xf8#64) (n := 8) (k := 216) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0xf8#64) (b' := sp + 0x160#64) (n := 104) (k := 112) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x160#64) (b' := sp + 0x170#64) (n := 16) (k := 96) rfl (by bv_arith) (by decide)]

/-! ## Source `sessionStateAt` and destination `scDstSlotsAt` layouts -/

theorem sc_sessionStateAt_eq (A : RustAlloc) (src : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A src G st =
      ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
        (match st.remoteIdentity with
         | none => G.remoteIk.bytes = []
         | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
        G.chains.length = st.receiverChains.length ∧
        G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
        G.localIk.bytes.length = 33 ∧
        (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
      vecGhostAt A G.localIk src ∗
      vecGhostAt A G.remoteIk (src + 0x18#64) ∗
      vecU8At A (src + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
      vecAt A 104 8 (chainAt A) (src + 0x48#64) G.chainsCap G.chainsPtr
        (G.chains.zip st.receiverChains) ∗
      vecGhostAt A G.alice (src + 0x60#64) ∗
      vecU8At A (src + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
      optSenderChainAt A (src + 0x90#64) G.sender st.senderChain ∗
      optTailVecAt A 48 (src + 0xf8#64) G.pending ∗
      optTailVecAt A 32 (src + 0x128#64) G.kyber ∗
      ((src + 0x148#64) ↦₃₂ st.sessionVersion) ∗
      ((src + 0x14c#64) ↦₃₂ st.previousCounter) ∗
      ((src + 0x150#64) ↦ₛ G.regIds) := by
  unfold sessionStateAt
  ac_rfl

theorem sc_vecAt_0x48_chains_eq (A : RustAlloc) (src cap ptr : BitVec 64)
    (gs : List ChainGhost) (rcs : List ReceiverChain)
    (hlen : gs.length = rcs.length) :
    vecAt A 104 8 (chainAt A) (src + 0x48#64) cap ptr (gs.zip rcs) =
      ((src + 0x48#64) ↦₆₄ cap) ∗ ((src + 0x50#64) ↦₆₄ ptr) ∗
      ((src + 0x58#64) ↦₆₄ BitVec.ofNat 64 rcs.length) ∗
      vecBuf A 104 8 (chainAt A) cap ptr (gs.zip rcs) := by
  unfold vecAt vecHeader
  have h1 : src + 0x48#64 + 8#64 = src + 0x50#64 := by bv_arith
  have h2 : src + 0x48#64 + 16#64 = src + 0x58#64 := by bv_arith
  have h3 : (gs.zip rcs).length = rcs.length := by simp [hlen]
  rw [h1, h2, h3]
  ac_rfl

/-- Spatial layout of the 344-byte destination `SessionStructure` slot at `dst`. -/
def scDstSlotsAt (dst : BitVec 64) (dv : DstVals) : SepProp :=
  (dst ↦₆₄ dv.w_ca0) ∗ ((dst + 0x08#64) ↦₆₄ dv.w_ca8) ∗ ((dst + 0x10#64) ↦₆₄ dv.w_cb0) ∗
  ((dst + 0x18#64) ↦₆₄ dv.w_cb8) ∗ ((dst + 0x20#64) ↦₆₄ dv.w_cc0) ∗ ((dst + 0x28#64) ↦₆₄ dv.w_cc8) ∗
  ((dst + 0x30#64) ↦₆₄ dv.w_cd0) ∗ ((dst + 0x38#64) ↦₆₄ dv.w_cd8) ∗ ((dst + 0x40#64) ↦₆₄ dv.w_ce0) ∗
  ((dst + 0x48#64) ↦₆₄ dv.w_ce8) ∗ ((dst + 0x50#64) ↦₆₄ dv.w_cf0) ∗ ((dst + 0x58#64) ↦₆₄ dv.w_cf8) ∗
  ((dst + 0x60#64) ↦₆₄ dv.w_d00) ∗ ((dst + 0x68#64) ↦₆₄ dv.w_d08) ∗ ((dst + 0x70#64) ↦₆₄ dv.w_d10) ∗
  ((dst + 0x78#64) ↦₆₄ dv.w_d18) ∗ ((dst + 0x80#64) ↦₆₄ dv.w_d20) ∗ ((dst + 0x88#64) ↦₆₄ dv.w_d28) ∗
  ((dst + 0x90#64) ↦₆₄ dv.w_d30) ∗
  chunks96_6QAt (dst + 0x98#64) dv.q0 dv.q1 dv.q2 dv.q3 dv.q4 dv.q5 ∗
  ((dst + 0xf8#64) ↦₆₄ dv.w_d98) ∗ ((dst + 0x100#64) ↦₆₄ dv.w_da0) ∗ ((dst + 0x108#64) ↦₆₄ dv.w_da8) ∗
  ((dst + 0x110#64) ↦₃₂ dv.w_db0) ∗ ((dst + 0x114#64) ↦₃₂ dv.w_db4) ∗ ((dst + 0x118#64) ↦₆₄ dv.w_db8) ∗
  ((dst + 0x120#64) ↦₃₂ dv.w_dc0) ∗ memRegion (dst + 0x124#64) 4 ∗
  ((dst + 0x128#64) ↦₆₄ dv.w_dc8) ∗ ((dst + 0x130#64) ↦₆₄ dv.w_dd0) ∗ ((dst + 0x138#64) ↦₆₄ dv.w_dd8) ∗
  ((dst + 0x140#64) ↦₃₂ dv.w_de0) ∗ memRegion (dst + 0x144#64) 4 ∗
  ((dst + 0x148#64) ↦₃₂ dv.w_de8) ∗ ((dst + 0x14c#64) ↦₃₂ dv.w_dec) ∗
  ((dst + 0x150#64) ↦₃₂ dv.w_df0) ∗ ((dst + 0x154#64) ↦₃₂ dv.w_df4)

theorem memRegion_344_entails_scDstSlotsAt (dst : BitVec 64) :
    memRegion dst 344 ⊢ ∃∗ dv : DstVals, scDstSlotsAt dst dv := by
  have h := memRegion_344_entails_dstSlotsAt (dst - 0xca0#64)
  have h0 : dst - 0xca0#64 + 0xca0#64 = dst := by bv_omega
  have hd : ∀ dv : DstVals, dstSlotsAt (dst - 0xca0#64) dv = scDstSlotsAt dst dv := by
    intro dv
    unfold dstSlotsAt scDstSlotsAt
    have hsub : ∀ k : BitVec 64, dst - 0xca0#64 + k = dst + (k - 0xca0#64) := by
      intro k; bv_omega
    simp only [h0, hsub, BitVec.reduceSub]
  rw [h0] at h
  refine Entails.trans h ?_
  apply Entails.sepExists_elim; intro dv
  rw [hd dv]
  exact Entails.sepExists_right dv (Entails.refl _)

def scDstSlotsWrittenAt (dst : BitVec 64)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64) (alice' : VecGhost)
    (pqCap' pqPtr' : BitVec 64)
    (scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (pendCap' pendPtr' : BitVec 64) (w23 w24 : BitVec 32) (v18 : BitVec 64) (v2c : BitVec 32)
    (kybCap' kybPtr' : BitVec 64) (v28 : BitVec 32)
    (sessVer prevCnt w288 w28c : BitVec 32) : SepProp :=
  (dst ↦₆₄ localIk'.cap) ∗ ((dst + 0x08#64) ↦₆₄ localIk'.ptr) ∗ ((dst + 0x10#64) ↦₆₄ localIk'.cap) ∗
  ((dst + 0x18#64) ↦₆₄ remoteIk'.cap) ∗ ((dst + 0x20#64) ↦₆₄ remoteIk'.ptr) ∗ ((dst + 0x28#64) ↦₆₄ remoteIk'.cap) ∗
  ((dst + 0x30#64) ↦₆₄ 32#64) ∗ ((dst + 0x38#64) ↦₆₄ rootPtr') ∗ ((dst + 0x40#64) ↦₆₄ 32#64) ∗
  ((dst + 0x48#64) ↦₆₄ chainsCap') ∗ ((dst + 0x50#64) ↦₆₄ chainsPtr') ∗ ((dst + 0x58#64) ↦₆₄ chainsCap') ∗
  ((dst + 0x60#64) ↦₆₄ alice'.cap) ∗ ((dst + 0x68#64) ↦₆₄ alice'.ptr) ∗ ((dst + 0x70#64) ↦₆₄ alice'.cap) ∗
  ((dst + 0x78#64) ↦₆₄ pqCap') ∗ ((dst + 0x80#64) ↦₆₄ pqPtr') ∗ ((dst + 0x88#64) ↦₆₄ pqCap') ∗
  ((dst + 0x90#64) ↦₆₄ scCap') ∗
  chunks96_6QAt (dst + 0x98#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
  ((dst + 0xf8#64) ↦₆₄ pendCap') ∗ ((dst + 0x100#64) ↦₆₄ pendPtr') ∗ ((dst + 0x108#64) ↦₆₄ pendCap') ∗
  ((dst + 0x110#64) ↦₃₂ w23) ∗ ((dst + 0x114#64) ↦₃₂ w24) ∗ ((dst + 0x118#64) ↦₆₄ v18) ∗
  ((dst + 0x120#64) ↦₃₂ v2c) ∗ memRegion (dst + 0x124#64) 4 ∗
  ((dst + 0x128#64) ↦₆₄ kybCap') ∗ ((dst + 0x130#64) ↦₆₄ kybPtr') ∗ ((dst + 0x138#64) ↦₆₄ kybCap') ∗
  ((dst + 0x140#64) ↦₃₂ v28) ∗ memRegion (dst + 0x144#64) 4 ∗
  ((dst + 0x148#64) ↦₃₂ sessVer) ∗ ((dst + 0x14c#64) ↦₃₂ prevCnt) ∗
  ((dst + 0x150#64) ↦₃₂ w288) ∗ ((dst + 0x154#64) ↦₃₂ w28c)

theorem sc_chunks96_6QAt_dst_0x98 (dst : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    chunks96_6QAt (dst + 0x98#64) q0 q1 q2 q3 q4 q5 =
      ((dst + 0x98#64) ↦₁₂₈ q0) ∗ ((dst + 0xa8#64) ↦₁₂₈ q1) ∗
      ((dst + 0xb8#64) ↦₁₂₈ q2) ∗ ((dst + 0xc8#64) ↦₁₂₈ q3) ∗
      ((dst + 0xd8#64) ↦₁₂₈ q4) ∗ ((dst + 0xe8#64) ↦₁₂₈ q5) := by
  unfold chunks96_6QAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-! ## Optional pre-key clone invariants and `encSessionMem` preservation -/

def ScOptPendClone (A : RustAlloc) (orig : Option TailVecGhost)
    (pendCap' pendPtr' : BitVec 64) (w23 w24 : BitVec 32) (v18 : BitVec 64) (v2c : BitVec 32) : SepProp :=
  match orig with
  | none => ⌜pendCap' = noneCap⌝
  | some gp =>
    ⌜pendCap' = BitVec.ofNat 64 gp.vec.bytes.length ∧
      ∃ tw4 : BitVec 32,
        gp.tail = unpack32 w23 ++ unpack32 w24 ++ unpack64 v18 ++ unpack32 v2c ++ unpack32 tw4⌝ ∗
      vecU8Buf A pendCap' pendPtr' gp.vec.bytes

def ScOptKybClone (A : RustAlloc) (orig : Option TailVecGhost)
    (kybCap' kybPtr' : BitVec 64) (v28 : BitVec 32) : SepProp :=
  match orig with
  | none => ⌜kybCap' = noneCap⌝
  | some gk =>
    ⌜kybCap' = BitVec.ofNat 64 gk.vec.bytes.length ∧
      ∃ kw1 : BitVec 32, gk.tail = unpack32 v28 ++ unpack32 kw1⌝ ∗
      vecU8Buf A kybCap' kybPtr' gk.vec.bytes

theorem PendingRel_of_tail_eq (g g' : TailVecGhost) {p}
    (hvec : g'.vec.bytes = g.vec.bytes)
    (w23 w24 : BitVec 32) (v18 : BitVec 64) (v2c tw4 w4' : BitVec 32)
    (hg : g.tail = unpack32 w23 ++ unpack32 w24 ++ unpack64 v18 ++ unpack32 v2c ++ unpack32 tw4)
    (hg' : g'.tail = unpack32 w23 ++ unpack32 w24 ++ unpack64 v18 ++ unpack32 v2c ++ unpack32 w4')
    (hrel : PendingRel (some g) p) :
    PendingRel (some g') p := by
  cases p with
  | none => exact hrel
  | some pp =>
    dsimp only [PendingRel] at hrel ⊢
    have ht4 : g'.tail.take 4 = g.tail.take 4 := by
      rw [hg, hg']; simp [unpack32]
    have hd4 : (g'.tail.drop 4).take 4 = (g.tail.drop 4).take 4 := by
      rw [hg, hg']; simp [unpack32]
    have hd8 : (g'.tail.drop 8).take 8 = (g.tail.drop 8).take 8 := by
      rw [hg, hg']; simp [unpack32, unpack64]
    have hd16 : (g'.tail.drop 16).take 4 = (g.tail.drop 16).take 4 := by
      rw [hg, hg']; simp [unpack32, unpack64]
    have hopt : OptU32Rel g'.tail pp.preKeyId := by
      cases hpk : pp.preKeyId <;> simp only [OptU32Rel, ht4, hd4]
      · simpa [OptU32Rel, hpk] using hrel.2.1
      · simpa [OptU32Rel, hpk] using hrel.2.1
    rw [hvec, hd8, hd16]
    exact ⟨hrel.1, hopt, hrel.2.2.1, hrel.2.2.2⟩

theorem KyberRel_of_tail_eq (g g' : TailVecGhost) {k}
    (hvec : g'.vec.bytes = g.vec.bytes)
    (v28 kw1 kw1' : BitVec 32)
    (hg : g.tail = unpack32 v28 ++ unpack32 kw1)
    (hg' : g'.tail = unpack32 v28 ++ unpack32 kw1')
    (hrel : KyberRel (some g) k) :
    KyberRel (some g') k := by
  cases k with
  | none => exact hrel
  | some kk =>
    dsimp only [KyberRel] at hrel ⊢
    have ht4 : g'.tail.take 4 = g.tail.take 4 := by
      rw [hg, hg']; simp [unpack32]
    rw [hvec, ht4]
    exact hrel

theorem optTailVecAt_48_of_scOptPendClone (A : RustAlloc) (a : BitVec 64)
    (orig : Option TailVecGhost) (p)
    (pendCap' pendPtr' : BitVec 64) (w23 w24 : BitVec 32) (v18 : BitVec 64) (v2c : BitVec 32)
    (hrel : PendingRel orig p) :
    ((a ↦₆₄ pendCap') ∗ ((a + 8#64) ↦₆₄ pendPtr') ∗ ((a + 16#64) ↦₆₄ pendCap') ∗
      ((a + 24#64) ↦₃₂ w23) ∗ ((a + 28#64) ↦₃₂ w24) ∗ ((a + 32#64) ↦₆₄ v18) ∗
      ((a + 40#64) ↦₃₂ v2c) ∗ memRegion (a + 44#64) 4 ∗
      ScOptPendClone A orig pendCap' pendPtr' w23 w24 v18 v2c) ⊢
      ∃∗ pend' : Option TailVecGhost,
        ⌜pend'.isSome = orig.isSome ∧ PendingRel pend' p ∧
          encPendingFieldMem pend' p = encPendingFieldMem orig p⌝ ∗
          optTailVecAt A 48 a pend' := by
  cases orig with
  | none =>
    dsimp only [ScOptPendClone]
    rw [show ((a ↦₆₄ pendCap') ∗ ((a + 8#64) ↦₆₄ pendPtr') ∗ ((a + 16#64) ↦₆₄ pendCap') ∗
          ((a + 24#64) ↦₃₂ w23) ∗ ((a + 28#64) ↦₃₂ w24) ∗ ((a + 32#64) ↦₆₄ v18) ∗
          ((a + 40#64) ↦₃₂ v2c) ∗ memRegion (a + 44#64) 4 ∗ ⌜pendCap' = noneCap⌝) =
        (⌜pendCap' = noneCap⌝ ∗ (a ↦₆₄ pendCap') ∗ ((a + 8#64) ↦₆₄ pendPtr') ∗
          ((a + 16#64) ↦₆₄ pendCap') ∗ ((a + 24#64) ↦₃₂ w23) ∗ ((a + 28#64) ↦₃₂ w24) ∗
          ((a + 32#64) ↦₆₄ v18) ∗ ((a + 40#64) ↦₃₂ v2c) ∗ memRegion (a + 44#64) 4) by ac_rfl]
    apply Entails.pure_left; rintro rfl
    refine Entails.sepExists_right none ?_
    apply Entails.pure_right ⟨rfl, hrel, rfl⟩
    unfold optTailVecAt
    apply sepConj_mono_right
    rw [memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 32) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k := 24) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 24#64) (b' := a + 28#64) (n := 4) (k := 20) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 28#64) (b' := a + 32#64) (n := 4) (k := 16) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 32#64) (b' := a + 40#64) (n := 8) (k := 8) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 40#64) (b' := a + 44#64) (n := 4) (k := 4) rfl (by bv_arith) (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _) <|
      sepConj_mono (pointsTo64_entails_memRegion _ _) <|
      sepConj_mono (pointsTo32_entails_memRegion _ _) <|
      sepConj_mono (pointsTo32_entails_memRegion _ _) <|
      sepConj_mono (pointsTo64_entails_memRegion _ _) <|
      sepConj_mono (pointsTo32_entails_memRegion _ _) (Entails.refl _)
  | some gp =>
    dsimp only [ScOptPendClone]
    rw [memRegion_four (a + 44#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w4'
    rw [show ((a ↦₆₄ pendCap') ∗ ((a + 8#64) ↦₆₄ pendPtr') ∗ ((a + 16#64) ↦₆₄ pendCap') ∗
          ((a + 24#64) ↦₃₂ w23) ∗ ((a + 28#64) ↦₃₂ w24) ∗ ((a + 32#64) ↦₆₄ v18) ∗
          ((a + 40#64) ↦₃₂ v2c) ∗ ((a + 44#64) ↦₃₂ w4') ∗
          ⌜pendCap' = BitVec.ofNat 64 gp.vec.bytes.length ∧
            ∃ tw4 : BitVec 32,
              gp.tail = unpack32 w23 ++ unpack32 w24 ++ unpack64 v18 ++ unpack32 v2c ++ unpack32 tw4⌝ ∗
          vecU8Buf A pendCap' pendPtr' gp.vec.bytes) =
        (⌜pendCap' = BitVec.ofNat 64 gp.vec.bytes.length ∧
            ∃ tw4 : BitVec 32,
              gp.tail = unpack32 w23 ++ unpack32 w24 ++ unpack64 v18 ++ unpack32 v2c ++ unpack32 tw4⌝ ∗
          (((a ↦₆₄ pendCap') ∗ ((a + 8#64) ↦₆₄ pendPtr') ∗ ((a + 16#64) ↦₆₄ pendCap')) ∗
            vecU8Buf A pendCap' pendPtr' gp.vec.bytes) ∗
          (((a + 24#64) ↦₃₂ w23) ∗ ((a + 28#64) ↦₃₂ w24) ∗ ((a + 32#64) ↦₆₄ v18) ∗
            ((a + 40#64) ↦₃₂ v2c) ∗ ((a + 44#64) ↦₃₂ w4'))) by ac_rfl]
    apply Entails.pure_left; rintro ⟨rfl, tw4, hgp_tail⟩
    set tail := unpack32 w23 ++ unpack32 w24 ++ unpack64 v18 ++ unpack32 v2c ++ unpack32 w4'
    have htail_len : tail.length = 24 := by simp [tail]
    have htail_eq :
        ((a + 24#64) ↦ₛ tail) =
          ((a + 24#64) ↦₃₂ w23) ∗ ((a + 28#64) ↦₃₂ w24) ∗ ((a + 32#64) ↦₆₄ v18) ∗
          ((a + 40#64) ↦₃₂ v2c) ∗ ((a + 44#64) ↦₃₂ w4') := by
      unfold tail
      simp only [List.append_assoc, pointsToBytes_append, unpack32_length, unpack64_length,
        ← pointsTo32_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]
      have h28 : a + 24#64 + BitVec.ofNat 64 4 = a + 28#64 := by bv_arith
      have h32 : a + 28#64 + BitVec.ofNat 64 4 = a + 32#64 := by bv_arith
      have h40 : a + 32#64 + BitVec.ofNat 64 8 = a + 40#64 := by bv_arith
      have h44 : a + 40#64 + BitVec.ofNat 64 4 = a + 44#64 := by bv_arith
      rw [h28, h32, h40, h44]
    rw [← htail_eq]
    set g' : TailVecGhost := ⟨⟨BitVec.ofNat 64 gp.vec.bytes.length, pendPtr', gp.vec.bytes⟩, tail⟩
    refine Entails.sepExists_right (some g') ?_
    have hrel' : PendingRel (some g') p :=
      PendingRel_of_tail_eq gp g' rfl w23 w24 v18 v2c tw4 w4' hgp_tail rfl hrel
    have henc' : encPendingFieldMem (some g') p = encPendingFieldMem (some gp) p := by
      cases p <;> rfl
    apply Entails.pure_right ⟨rfl, hrel', henc'⟩
    unfold optTailVecAt
    apply Entails.pure_right htail_len
    unfold vecGhostAt
    rw [vecU8At_eq_header_sep_buf]
    exact Entails.refl _

theorem optTailVecAt_32_of_scOptKybClone (A : RustAlloc) (a : BitVec 64)
    (orig : Option TailVecGhost) (k)
    (kybCap' kybPtr' : BitVec 64) (v28 : BitVec 32)
    (hrel : KyberRel orig k) :
    ((a ↦₆₄ kybCap') ∗ ((a + 8#64) ↦₆₄ kybPtr') ∗ ((a + 16#64) ↦₆₄ kybCap') ∗
      ((a + 24#64) ↦₃₂ v28) ∗ memRegion (a + 28#64) 4 ∗
      ScOptKybClone A orig kybCap' kybPtr' v28) ⊢
      ∃∗ kyb' : Option TailVecGhost,
        ⌜KyberRel kyb' k⌝ ∗ optTailVecAt A 32 a kyb' := by
  cases orig with
  | none =>
    dsimp only [ScOptKybClone]
    rw [show ((a ↦₆₄ kybCap') ∗ ((a + 8#64) ↦₆₄ kybPtr') ∗ ((a + 16#64) ↦₆₄ kybCap') ∗
          ((a + 24#64) ↦₃₂ v28) ∗ memRegion (a + 28#64) 4 ∗ ⌜kybCap' = noneCap⌝) =
        (⌜kybCap' = noneCap⌝ ∗ (a ↦₆₄ kybCap') ∗ ((a + 8#64) ↦₆₄ kybPtr') ∗
          ((a + 16#64) ↦₆₄ kybCap') ∗ ((a + 24#64) ↦₃₂ v28) ∗ memRegion (a + 28#64) 4) by ac_rfl]
    apply Entails.pure_left; rintro rfl
    refine Entails.sepExists_right none ?_
    apply Entails.pure_right hrel
    unfold optTailVecAt
    apply sepConj_mono_right
    rw [memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 16) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k := 8) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 24#64) (b' := a + 28#64) (n := 4) (k := 4) rfl (by bv_arith) (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _) <|
      sepConj_mono (pointsTo64_entails_memRegion _ _) <|
      sepConj_mono (pointsTo32_entails_memRegion _ _) (Entails.refl _)
  | some gk =>
    dsimp only [ScOptKybClone]
    rw [memRegion_four (a + 28#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro kw1'
    rw [show ((a ↦₆₄ kybCap') ∗ ((a + 8#64) ↦₆₄ kybPtr') ∗ ((a + 16#64) ↦₆₄ kybCap') ∗
          ((a + 24#64) ↦₃₂ v28) ∗ ((a + 28#64) ↦₃₂ kw1') ∗
          ⌜kybCap' = BitVec.ofNat 64 gk.vec.bytes.length ∧
            ∃ kw1 : BitVec 32, gk.tail = unpack32 v28 ++ unpack32 kw1⌝ ∗
          vecU8Buf A kybCap' kybPtr' gk.vec.bytes) =
        (⌜kybCap' = BitVec.ofNat 64 gk.vec.bytes.length ∧
            ∃ kw1 : BitVec 32, gk.tail = unpack32 v28 ++ unpack32 kw1⌝ ∗
          (((a ↦₆₄ kybCap') ∗ ((a + 8#64) ↦₆₄ kybPtr') ∗ ((a + 16#64) ↦₆₄ kybCap')) ∗
            vecU8Buf A kybCap' kybPtr' gk.vec.bytes) ∗
          (((a + 24#64) ↦₃₂ v28) ∗ ((a + 28#64) ↦₃₂ kw1'))) by ac_rfl]
    apply Entails.pure_left; rintro ⟨rfl, kw1, hgk_tail⟩
    set tail := unpack32 v28 ++ unpack32 kw1'
    have htail_len : tail.length = 8 := by simp [tail]
    have htail_eq :
        ((a + 24#64) ↦ₛ tail) =
          ((a + 24#64) ↦₃₂ v28) ∗ ((a + 28#64) ↦₃₂ kw1') := by
      unfold tail
      rw [pointsToBytes_append, unpack32_length,
          ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
      have h28 : a + 24#64 + BitVec.ofNat 64 4 = a + 28#64 := by bv_arith
      rw [h28]
    rw [← htail_eq]
    set g' : TailVecGhost := ⟨⟨BitVec.ofNat 64 gk.vec.bytes.length, kybPtr', gk.vec.bytes⟩, tail⟩
    refine Entails.sepExists_right (some g') ?_
    have hrel' : KyberRel (some g') k :=
      KyberRel_of_tail_eq gk g' rfl v28 kw1 kw1' hgk_tail rfl hrel
    apply Entails.pure_right hrel'
    unfold optTailVecAt
    apply Entails.pure_right htail_len
    unfold vecGhostAt
    rw [vecU8At_eq_header_sep_buf]
    exact Entails.refl _

theorem sc_srcSessionAt_reassemble (A : RustAlloc) (x : SessionCloneGhost)
    (w288 w28c : BitVec 32)
    (h_pend_rel : PendingRel x.G.pending x.s.pendingPreKey)
    (h_kyb_rel : KyberRel x.G.kyber x.s.pendingKyberPreKey)
    (h_alice_eq : x.G.alice.bytes = x.s.aliceBaseKey)
    (h_rem_reg : x.G.regIds.take 4 = leBytes 4 x.s.remoteRegistrationId.toNat)
    (h_loc_reg : (x.G.regIds.drop 4).take 4 = leBytes 4 x.s.localRegistrationId.toNat)
    (h_loc_deser : PublicKey.deserialize x.G.localIk.bytes = .ok x.s.state.localIdentity.publicKey)
    (h_rem_deser : match x.s.state.remoteIdentity with
      | none => x.G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey)
    (h_chains_len : x.G.chains.length = x.s.state.receiverChains.length)
    (h_pend_some : x.G.pending.isSome = x.s.state.pendingPreKey)
    (h_reg_len : x.G.regIds.length = 8)
    (h_loc_len : x.G.localIk.bytes.length = 33)
    (h_rem_len : x.s.state.remoteIdentity.isSome → x.G.remoteIk.bytes.length = 33)
    (h_reg_pts : ∀ a : BitVec 64, (a ↦ₛ x.G.regIds) = (a ↦₃₂ w288) ∗ ((a + 4#64) ↦₃₂ w28c)) :
    (vecGhostAt A x.G.localIk x.src ∗
      vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
      vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
      vecAt A 104 8 (chainAt A) (x.src + 0x48#64) x.G.chainsCap x.G.chainsPtr
        (x.G.chains.zip x.s.state.receiverChains) ∗
      vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
      vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
      optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
      optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
      optTailVecAt A 32 (x.src + 0x128#64) x.G.kyber ∗
      ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
      ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
      ((x.src + 0x150#64) ↦₃₂ w288) ∗
      ((x.src + 0x154#64) ↦₃₂ w28c)) ⊢
      sessionStateReprAt A x.src x.G x.s := by
  unfold sessionStateReprAt
  apply Entails.pure_right ⟨h_pend_rel, h_kyb_rel, h_alice_eq, h_rem_reg, h_loc_reg⟩
  rw [sc_sessionStateAt_eq]
  apply Entails.pure_right ⟨h_loc_deser, h_rem_deser, h_chains_len, h_pend_some, h_reg_len, h_loc_len, h_rem_len⟩
  have h154 : x.src + 0x150#64 + 4#64 = x.src + 0x154#64 := by bv_arith
  rw [h_reg_pts (x.src + 0x150#64), h154]
  exact Entails.of_eq (by ac_rfl)

theorem scDstSlotsWrittenAt_entails_sessionAt
    (A : RustAlloc) (x : SessionCloneGhost)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost)
    (alice' : VecGhost) (pqCap' pqPtr' : BitVec 64)
    (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (pendCap' pendPtr' : BitVec 64) (w23 w24 : BitVec 32) (v18 : BitVec 64) (v2c : BitVec 32)
    (kybCap' kybPtr' : BitVec 64) (v28 : BitVec 32)
    (w288 w28c : BitVec 32)
    (h_pend_rel : PendingRel x.G.pending x.s.pendingPreKey)
    (h_kyb_rel : KyberRel x.G.kyber x.s.pendingKyberPreKey)
    (h_alice_eq : x.G.alice.bytes = x.s.aliceBaseKey)
    (h_rem_reg : x.G.regIds.take 4 = leBytes 4 x.s.remoteRegistrationId.toNat)
    (h_loc_reg : (x.G.regIds.drop 4).take 4 = leBytes 4 x.s.localRegistrationId.toNat)
    (h_loc_deser : PublicKey.deserialize x.G.localIk.bytes = .ok x.s.state.localIdentity.publicKey)
    (h_rem_deser : match x.s.state.remoteIdentity with
      | none => x.G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey)
    (h_pend_some : x.G.pending.isSome = x.s.state.pendingPreKey)
    (h_reg_len : x.G.regIds.length = 8)
    (h_loc_len : x.G.localIk.bytes.length = 33)
    (h_rem_len : x.s.state.remoteIdentity.isSome → x.G.remoteIk.bytes.length = 33)
    (h_reg_pts : ∀ a : BitVec 64, (a ↦ₛ x.G.regIds) = (a ↦₃₂ w288) ∗ ((a + 4#64) ↦₃₂ w28c))
    (hloc_bytes : localIk'.bytes = x.G.localIk.bytes)
    (hloc_cap : localIk'.cap = BitVec.ofNat 64 x.G.localIk.bytes.length)
    (hrem_bytes : remoteIk'.bytes = x.G.remoteIk.bytes)
    (hrem_cap : remoteIk'.cap = BitVec.ofNat 64 x.G.remoteIk.bytes.length)
    (hchains_len : chains'.length = x.s.state.receiverChains.length)
    (hchains_cap : chainsCap' = BitVec.ofNat 64 x.s.state.receiverChains.length)
    (hchains_enc : ((chains'.zip x.s.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)) =
      ((x.G.chains.zip x.s.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)))
    (halice_bytes : alice'.bytes = x.G.alice.bytes)
    (halice_cap : alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length)
    (hpq_cap : pqCap' = BitVec.ofNat 64 x.s.state.pqRatchetState.length)
    (hsc_inl : OptSenderChainInline sender' x.s.state.senderChain
      (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5))
    (hsc_enc : encSenderFieldMem sender' x.s.state.senderChain =
      encSenderFieldMem x.G.sender x.s.state.senderChain) :
    (scDstSlotsWrittenAt x.dst localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
        pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w23 w24 v18 v2c
        kybCap' kybPtr' v28 x.s.state.sessionVersion x.s.state.previousCounter w288 w28c ∗
      vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
      vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
      vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
      vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
      vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
      vecU8Buf A pqCap' pqPtr' x.s.state.pqRatchetState ∗
      optSenderChainHeap A sender' x.s.state.senderChain ∗
      ScOptPendClone A x.G.pending pendCap' pendPtr' w23 w24 v18 v2c ∗
      ScOptKybClone A x.G.kyber kybCap' kybPtr' v28) ⊢
      ∃∗ G' : SessionGhost,
        ⌜encSessionMem G' x.s = encSessionMem x.G x.s⌝ ∗
        sessionStateReprAt A x.dst G' x.s := by
  have hloc_hdr :
      (x.dst ↦₆₄ localIk'.cap) ∗ ((x.dst + 0x08#64) ↦₆₄ localIk'.ptr) ∗
        ((x.dst + 0x10#64) ↦₆₄ localIk'.cap) ∗
        vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes =
      vecGhostAt A localIk' x.dst := by
    unfold vecGhostAt
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h3 : BitVec.ofNat 64 localIk'.bytes.length = localIk'.cap := by
      rw [hloc_bytes, ← hloc_cap]
    rw [h3]; ac_rfl
  have hrem_hdr :
      ((x.dst + 0x18#64) ↦₆₄ remoteIk'.cap) ∗ ((x.dst + 0x20#64) ↦₆₄ remoteIk'.ptr) ∗
        ((x.dst + 0x28#64) ↦₆₄ remoteIk'.cap) ∗
        vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes =
      vecGhostAt A remoteIk' (x.dst + 0x18#64) := by
    unfold vecGhostAt
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h1 : x.dst + 0x18#64 + 8#64 = x.dst + 0x20#64 := by bv_arith
    have h2 : x.dst + 0x18#64 + 16#64 = x.dst + 0x28#64 := by bv_arith
    have h3 : BitVec.ofNat 64 remoteIk'.bytes.length = remoteIk'.cap := by
      rw [hrem_bytes, ← hrem_cap]
    rw [h1, h2, h3]; ac_rfl
  have hroot_hdr :
      ((x.dst + 0x30#64) ↦₆₄ 32#64) ∗ ((x.dst + 0x38#64) ↦₆₄ rootPtr') ∗
        ((x.dst + 0x40#64) ↦₆₄ 32#64) ∗
        vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) =
      vecU8At A (x.dst + 0x30#64) 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) := by
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h1 : x.dst + 0x30#64 + 8#64 = x.dst + 0x38#64 := by bv_arith
    have h2 : x.dst + 0x30#64 + 16#64 = x.dst + 0x40#64 := by bv_arith
    have h3 : BitVec.ofNat 64 (keyToBytes32 x.s.state.rootKey).length = 32#64 := by
      simp [keyToBytes32]
    rw [h1, h2, h3]; ac_rfl
  have hchains_hdr :
      ((x.dst + 0x48#64) ↦₆₄ chainsCap') ∗ ((x.dst + 0x50#64) ↦₆₄ chainsPtr') ∗
        ((x.dst + 0x58#64) ↦₆₄ chainsCap') ∗
        vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) =
      vecAt A 104 8 (chainAt A) (x.dst + 0x48#64) chainsCap' chainsPtr'
        (chains'.zip x.s.state.receiverChains) := by
    unfold vecAt vecHeader
    have h1 : x.dst + 0x48#64 + 8#64 = x.dst + 0x50#64 := by bv_arith
    have h2 : x.dst + 0x48#64 + 16#64 = x.dst + 0x58#64 := by bv_arith
    have h3 : BitVec.ofNat 64 (chains'.zip x.s.state.receiverChains).length = chainsCap' := by
      simp [hchains_len, hchains_cap]
    rw [h1, h2, h3]; ac_rfl
  have halice_hdr :
      ((x.dst + 0x60#64) ↦₆₄ alice'.cap) ∗ ((x.dst + 0x68#64) ↦₆₄ alice'.ptr) ∗
        ((x.dst + 0x70#64) ↦₆₄ alice'.cap) ∗
        vecU8Buf A alice'.cap alice'.ptr alice'.bytes =
      vecGhostAt A alice' (x.dst + 0x60#64) := by
    unfold vecGhostAt
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h1 : x.dst + 0x60#64 + 8#64 = x.dst + 0x68#64 := by bv_arith
    have h2 : x.dst + 0x60#64 + 16#64 = x.dst + 0x70#64 := by bv_arith
    have h3 : BitVec.ofNat 64 alice'.bytes.length = alice'.cap := by
      rw [halice_bytes, ← halice_cap]
    rw [h1, h2, h3]; ac_rfl
  have hpq_hdr :
      ((x.dst + 0x78#64) ↦₆₄ pqCap') ∗ ((x.dst + 0x80#64) ↦₆₄ pqPtr') ∗
        ((x.dst + 0x88#64) ↦₆₄ pqCap') ∗
        vecU8Buf A pqCap' pqPtr' x.s.state.pqRatchetState =
      vecU8At A (x.dst + 0x78#64) pqCap' pqPtr' x.s.state.pqRatchetState := by
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h1 : x.dst + 0x78#64 + 8#64 = x.dst + 0x80#64 := by bv_arith
    have h2 : x.dst + 0x78#64 + 16#64 = x.dst + 0x88#64 := by bv_arith
    rw [h1, h2, ← hpq_cap]; ac_rfl
  have hsc_reasm :
      (((x.dst + 0x90#64) ↦₆₄ scCap') ∗
        chunks96_6QAt (x.dst + 0x98#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        optSenderChainHeap A sender' x.s.state.senderChain) ⊢
      optSenderChainAt A (x.dst + 0x90#64) sender' x.s.state.senderChain := by
    have h8 : x.dst + 0x90#64 + 0x8#64 = x.dst + 0x98#64 := by bv_arith
    rw [← h8, ← sepConj_assoc, ← chunks104W6QAt_eq_word_sep_chunks96]
    exact optSenderChainAt_of_chunks104W6Q A (x.dst + 0x90#64) sender' x.s.state.senderChain hsc_inl
  have hpend_reasm :
      (((x.dst + 0xf8#64) ↦₆₄ pendCap') ∗ ((x.dst + 0x100#64) ↦₆₄ pendPtr') ∗
        ((x.dst + 0x108#64) ↦₆₄ pendCap') ∗ ((x.dst + 0x110#64) ↦₃₂ w23) ∗
        ((x.dst + 0x114#64) ↦₃₂ w24) ∗ ((x.dst + 0x118#64) ↦₆₄ v18) ∗
        ((x.dst + 0x120#64) ↦₃₂ v2c) ∗ memRegion (x.dst + 0x124#64) 4 ∗
        ScOptPendClone A x.G.pending pendCap' pendPtr' w23 w24 v18 v2c) ⊢
      ∃∗ pend' : Option TailVecGhost,
        ⌜pend'.isSome = x.G.pending.isSome ∧ PendingRel pend' x.s.pendingPreKey ∧
          encPendingFieldMem pend' x.s.pendingPreKey = encPendingFieldMem x.G.pending x.s.pendingPreKey⌝ ∗
          optTailVecAt A 48 (x.dst + 0xf8#64) pend' := by
    have h8 : x.dst + 0xf8#64 + 8#64 = x.dst + 0x100#64 := by bv_arith
    have h16 : x.dst + 0xf8#64 + 16#64 = x.dst + 0x108#64 := by bv_arith
    have h24 : x.dst + 0xf8#64 + 24#64 = x.dst + 0x110#64 := by bv_arith
    have h28 : x.dst + 0xf8#64 + 28#64 = x.dst + 0x114#64 := by bv_arith
    have h32 : x.dst + 0xf8#64 + 32#64 = x.dst + 0x118#64 := by bv_arith
    have h40 : x.dst + 0xf8#64 + 40#64 = x.dst + 0x120#64 := by bv_arith
    have h44 : x.dst + 0xf8#64 + 44#64 = x.dst + 0x124#64 := by bv_arith
    rw [← h8, ← h16, ← h24, ← h28, ← h32, ← h40, ← h44]
    exact optTailVecAt_48_of_scOptPendClone A (x.dst + 0xf8#64) x.G.pending x.s.pendingPreKey
      pendCap' pendPtr' w23 w24 v18 v2c h_pend_rel
  have hkyb_reasm :
      (((x.dst + 0x128#64) ↦₆₄ kybCap') ∗ ((x.dst + 0x130#64) ↦₆₄ kybPtr') ∗
        ((x.dst + 0x138#64) ↦₆₄ kybCap') ∗ ((x.dst + 0x140#64) ↦₃₂ v28) ∗
        memRegion (x.dst + 0x144#64) 4 ∗
        ScOptKybClone A x.G.kyber kybCap' kybPtr' v28) ⊢
      ∃∗ kyb' : Option TailVecGhost,
        ⌜KyberRel kyb' x.s.pendingKyberPreKey⌝ ∗
          optTailVecAt A 32 (x.dst + 0x128#64) kyb' := by
    have h8 : x.dst + 0x128#64 + 8#64 = x.dst + 0x130#64 := by bv_arith
    have h16 : x.dst + 0x128#64 + 16#64 = x.dst + 0x138#64 := by bv_arith
    have h24 : x.dst + 0x128#64 + 24#64 = x.dst + 0x140#64 := by bv_arith
    have h28 : x.dst + 0x128#64 + 28#64 = x.dst + 0x144#64 := by bv_arith
    rw [← h8, ← h16, ← h24, ← h28]
    exact optTailVecAt_32_of_scOptKybClone A (x.dst + 0x128#64) x.G.kyber x.s.pendingKyberPreKey
      kybCap' kybPtr' v28 h_kyb_rel
  have htail_eq :
      ((x.dst + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
        ((x.dst + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
        ((x.dst + 0x150#64) ↦₃₂ w288) ∗ ((x.dst + 0x154#64) ↦₃₂ w28c) =
      ((x.dst + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
        ((x.dst + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
        ((x.dst + 0x150#64) ↦ₛ x.G.regIds) := by
    have h154 : x.dst + 0x150#64 + 4#64 = x.dst + 0x154#64 := by bv_arith
    rw [h_reg_pts (x.dst + 0x150#64), h154]
  unfold scDstSlotsWrittenAt
  refine Entails.trans
    (Q := (((x.dst + 0xf8#64) ↦₆₄ pendCap') ∗ ((x.dst + 0x100#64) ↦₆₄ pendPtr') ∗
            ((x.dst + 0x108#64) ↦₆₄ pendCap') ∗ ((x.dst + 0x110#64) ↦₃₂ w23) ∗
            ((x.dst + 0x114#64) ↦₃₂ w24) ∗ ((x.dst + 0x118#64) ↦₆₄ v18) ∗
            ((x.dst + 0x120#64) ↦₃₂ v2c) ∗ memRegion (x.dst + 0x124#64) 4 ∗
            ScOptPendClone A x.G.pending pendCap' pendPtr' w23 w24 v18 v2c) ∗
          (((x.dst + 0x128#64) ↦₆₄ kybCap') ∗ ((x.dst + 0x130#64) ↦₆₄ kybPtr') ∗
            ((x.dst + 0x138#64) ↦₆₄ kybCap') ∗ ((x.dst + 0x140#64) ↦₃₂ v28) ∗
            memRegion (x.dst + 0x144#64) 4 ∗
            ScOptKybClone A x.G.kyber kybCap' kybPtr' v28) ∗
          (((x.dst + 0x90#64) ↦₆₄ scCap') ∗
            chunks96_6QAt (x.dst + 0x98#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
            optSenderChainHeap A sender' x.s.state.senderChain) ∗
          ((x.dst ↦₆₄ localIk'.cap) ∗ ((x.dst + 0x08#64) ↦₆₄ localIk'.ptr) ∗
            ((x.dst + 0x10#64) ↦₆₄ localIk'.cap) ∗
            vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes) ∗
          (((x.dst + 0x18#64) ↦₆₄ remoteIk'.cap) ∗ ((x.dst + 0x20#64) ↦₆₄ remoteIk'.ptr) ∗
            ((x.dst + 0x28#64) ↦₆₄ remoteIk'.cap) ∗
            vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes) ∗
          (((x.dst + 0x30#64) ↦₆₄ 32#64) ∗ ((x.dst + 0x38#64) ↦₆₄ rootPtr') ∗
            ((x.dst + 0x40#64) ↦₆₄ 32#64) ∗
            vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey)) ∗
          (((x.dst + 0x48#64) ↦₆₄ chainsCap') ∗ ((x.dst + 0x50#64) ↦₆₄ chainsPtr') ∗
            ((x.dst + 0x58#64) ↦₆₄ chainsCap') ∗
            vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains)) ∗
          (((x.dst + 0x60#64) ↦₆₄ alice'.cap) ∗ ((x.dst + 0x68#64) ↦₆₄ alice'.ptr) ∗
            ((x.dst + 0x70#64) ↦₆₄ alice'.cap) ∗
            vecU8Buf A alice'.cap alice'.ptr alice'.bytes) ∗
          (((x.dst + 0x78#64) ↦₆₄ pqCap') ∗ ((x.dst + 0x80#64) ↦₆₄ pqPtr') ∗
            ((x.dst + 0x88#64) ↦₆₄ pqCap') ∗
            vecU8Buf A pqCap' pqPtr' x.s.state.pqRatchetState) ∗
          (((x.dst + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
            ((x.dst + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
            ((x.dst + 0x150#64) ↦₃₂ w288) ∗ ((x.dst + 0x154#64) ↦₃₂ w28c)))
    (Entails.of_eq (by ac_rfl)) ?_
  rw [hloc_hdr, hrem_hdr, hroot_hdr, hchains_hdr, halice_hdr, hpq_hdr, htail_eq]
  refine Entails.trans
    (sepConj_mono hpend_reasm (sepConj_mono hkyb_reasm (sepConj_mono_left hsc_reasm))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro kyb'
  apply Entails.sepExists_elim; intro pend'
  rw [sepConj_assoc]
  apply Entails.pure_left; rintro ⟨hpend'_some, hpend'_rel, hpend'_enc⟩
  rw [show (optTailVecAt A 48 (x.dst + 0xf8#64) pend' ∗
        (⌜KyberRel kyb' x.s.pendingKyberPreKey⌝ ∗
          optTailVecAt A 32 (x.dst + 0x128#64) kyb') ∗
        optSenderChainAt A (x.dst + 0x90#64) sender' x.s.state.senderChain ∗
        vecGhostAt A localIk' x.dst ∗
        vecGhostAt A remoteIk' (x.dst + 0x18#64) ∗
        vecU8At A (x.dst + 0x30#64) 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
        vecAt A 104 8 (chainAt A) (x.dst + 0x48#64) chainsCap' chainsPtr'
          (chains'.zip x.s.state.receiverChains) ∗
        vecGhostAt A alice' (x.dst + 0x60#64) ∗
        vecU8At A (x.dst + 0x78#64) pqCap' pqPtr' x.s.state.pqRatchetState ∗
        ((x.dst + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
        ((x.dst + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
        ((x.dst + 0x150#64) ↦ₛ x.G.regIds)) =
      (⌜KyberRel kyb' x.s.pendingKyberPreKey⌝ ∗
        optTailVecAt A 48 (x.dst + 0xf8#64) pend' ∗
        optTailVecAt A 32 (x.dst + 0x128#64) kyb' ∗
        optSenderChainAt A (x.dst + 0x90#64) sender' x.s.state.senderChain ∗
        vecGhostAt A localIk' x.dst ∗
        vecGhostAt A remoteIk' (x.dst + 0x18#64) ∗
        vecU8At A (x.dst + 0x30#64) 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
        vecAt A 104 8 (chainAt A) (x.dst + 0x48#64) chainsCap' chainsPtr'
          (chains'.zip x.s.state.receiverChains) ∗
        vecGhostAt A alice' (x.dst + 0x60#64) ∗
        vecU8At A (x.dst + 0x78#64) pqCap' pqPtr' x.s.state.pqRatchetState ∗
        ((x.dst + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
        ((x.dst + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
        ((x.dst + 0x150#64) ↦ₛ x.G.regIds)) by ac_rfl]
  apply Entails.pure_left; intro hkyb'_rel
  let G' : SessionGhost :=
    { localIk := localIk'
      remoteIk := remoteIk'
      root := ⟨32#64, rootPtr'⟩
      chainsCap := chainsCap'
      chainsPtr := chainsPtr'
      chains := chains'
      alice := alice'
      pq := ⟨pqCap', pqPtr'⟩
      sender := sender'
      pending := pend'
      kyber := kyb'
      regIds := x.G.regIds }
  refine Entails.sepExists_right G' ?_
  have henc : encSessionMem G' x.s = encSessionMem x.G x.s := by
    unfold encSessionMem
    dsimp only [G']
    rw [hloc_bytes, hrem_bytes, hsc_enc, hchains_enc, hpend'_enc]
  apply Entails.pure_right henc
  unfold sessionStateReprAt
  have hpure_s :
      PendingRel G'.pending x.s.pendingPreKey ∧
      KyberRel G'.kyber x.s.pendingKyberPreKey ∧
      G'.alice.bytes = x.s.aliceBaseKey ∧
      G'.regIds.take 4 = leBytes 4 x.s.remoteRegistrationId.toNat ∧
      (G'.regIds.drop 4).take 4 = leBytes 4 x.s.localRegistrationId.toNat := by
    dsimp [G']
    rw [halice_bytes]
    exact ⟨hpend'_rel, hkyb'_rel, h_alice_eq, h_rem_reg, h_loc_reg⟩
  apply Entails.pure_right hpure_s
  unfold sessionStateAt
  have hpure_st :
      PublicKey.deserialize G'.localIk.bytes = .ok x.s.state.localIdentity.publicKey ∧
      (match x.s.state.remoteIdentity with
       | none => G'.remoteIk.bytes = []
       | some ik => PublicKey.deserialize G'.remoteIk.bytes = .ok ik.publicKey) ∧
      G'.chains.length = x.s.state.receiverChains.length ∧
      G'.pending.isSome = x.s.state.pendingPreKey ∧ G'.regIds.length = 8 ∧
      G'.localIk.bytes.length = 33 ∧
      (x.s.state.remoteIdentity.isSome → G'.remoteIk.bytes.length = 33) := by
    dsimp [G']
    rw [hloc_bytes, hrem_bytes, hpend'_some]
    exact ⟨h_loc_deser, h_rem_deser, hchains_len, h_pend_some, h_reg_len, h_loc_len, h_rem_len⟩
  apply Entails.pure_right hpure_st
  dsimp only [G']
  exact Entails.of_eq (by ac_rfl)

/-! ## Relocatable `[LibsignalPlacement]` helpers (block `80`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

/-- Lifts a `SepWP` basic block into `SepWPp` while preserving `LibsignalCodeLoaded`. -/
theorem sepWPp_of_sepWP_lscl_sc {prog : Program} {pl : MultiPlacement} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h fun _ _ _ _ hclm hnext => hnext hclm)

theorem sepWPp_call_frame_lscl_sc {α : Type} {prog : Program} {pl : MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hpre' : s.mem ⊨ (withLsCodeLoaded pl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [hP, sepConj_assoc] at hm
    rw [hspec, sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hcl.of_keepsFrozen hsteps.keepsFrozen)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · exact (hexit sm code _ hex hpost).elim
  · dsimp only [withLsCodeLoaded] at hpost
    rw [hoom sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

theorem sc_chainClone_placed_ok_at [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hcc : ChainCloneLocal1PlacedOk A H) :
    subroutine_ok (lsProg_80 H) (blkPl_82).base (withLsCodeLoaded lsmpl (chainCloneSpec A)) :=
  ls_subroutine_ok_of_block (callerProg := lsProg_80 H)
    (subroutine_ok_withLsCodeLoaded_of_plain hcc)

theorem sc_senderChainClone_placed_ok_at [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hscc : SenderChainCloneLocal1PlacedOk A H) :
    subroutine_ok (lsProg_80 H) (blkPl_82).base (withLsCodeLoaded lsmpl (senderChainCloneSpec A)) :=
  ls_subroutine_ok_of_block (callerProg := lsProg_80 H)
    (subroutine_ok_withLsCodeLoaded_of_plain hscc)

theorem sc_panic_at_handle_error_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    (lsProg_80 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked := by
  rw [ls_externAt?_of_mem, hpanic]

structure ScExternKit_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop where
  shim : subroutine_ok (lsProg_80 H) (lsρ lsRustNoAllocShimSym)
    LibsignalTripleRatchet.sessionShimSpec
  alloc : subroutine_ok (lsProg_80 H) (lsρ lsRustAllocSym) (rustAllocSpec A)
  memcpy : subroutine_ok (lsProg_80 H) (lsρ lsMemcpySym) sessionMemcpyRegionSpec
  panic_err : (lsProg_80 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked

theorem scExternKit_placed_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    ScExternKit_placed A H :=
  ⟨ls_hook_ok_of_mem hshim, ls_hook_ok_of_mem halloc, ls_hook_ok_of_mem hmemcpy,
    sc_panic_at_handle_error_placed hpanic⟩

theorem sc_panic_0x474_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hpanic : (lsProg_80 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_80).base + 0x474#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_80 H) ret s P Q (scPanicPost A x R s0) := by
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  refine SepWP.done rfl hrun (SepWPp.panic hrun hpanic fun hm => ?_)
  exact sc_onPanic_of_allocFailed (Record.SegCloneSteps.allocFailedIn_of_eq
    (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem sc_panic_0x480_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hpanic : (lsProg_80 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_80).base + 0x480#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_80 H) ret s P Q (scPanicPost A x R s0) := by
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  refine SepWP.done rfl hrun (SepWPp.panic hrun hpanic fun hm => ?_)
  exact sc_onPanic_of_allocFailed (Record.SegCloneSteps.allocFailedIn_of_eq
    (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem sc_panic_0x48c_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hpanic : (lsProg_80 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_80).base + 0x48c#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_80 H) ret s P Q (scPanicPost A x R s0) := by
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  refine SepWP.done rfl hrun (SepWPp.panic hrun hpanic fun hm => ?_)
  exact sc_onPanic_of_allocFailed (Record.SegCloneSteps.allocFailedIn_of_eq
    (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem sc_panic_0x498_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hpanic : (lsProg_80 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_80).base + 0x498#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_80 H) ret s P Q (scPanicPost A x R s0) := by
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  refine SepWP.done rfl hrun (SepWPp.panic hrun hpanic fun hm => ?_)
  exact sc_onPanic_of_allocFailed (Record.SegCloneSteps.allocFailedIn_of_eq
    (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem sc_panic_0x4a4_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hpanic : (lsProg_80 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_80).base + 0x4a4#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_80 H) ret s P Q (scPanicPost A x R s0) := by
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  refine SepWP.done rfl hrun (SepWPp.panic hrun hpanic fun hm => ?_)
  exact sc_onPanic_of_allocFailed (Record.SegCloneSteps.allocFailedIn_of_eq
    (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem sc_panic_0x4b0_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hpanic : (lsProg_80 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_80).base + 0x4b0#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_80 H) ret s P Q (scPanicPost A x R s0) := by
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  refine SepWP.done rfl hrun (SepWPp.panic hrun hpanic fun hm => ?_)
  exact sc_onPanic_of_allocFailed (Record.SegCloneSteps.allocFailedIn_of_eq
    (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

end Placed

end CryptoVerification.E2E.Record.Serialization.SessionCloneAux
