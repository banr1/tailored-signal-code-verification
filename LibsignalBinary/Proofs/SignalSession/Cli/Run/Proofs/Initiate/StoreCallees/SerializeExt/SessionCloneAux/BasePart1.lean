/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase
public import LibsignalBinary.Proofs.Common.InImageKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.ChainCloneBasePart1
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.WPX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Base Helpers, Panic Stubs, and Stack/Slot Layouts for `SessionStructure::clone`
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.ChainCloneLocal1
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.E2E.Record.Serialization
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [scoped arm64_norm, scoped wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg

/-! ## 1. Extern Hooks, Callee Address Bridges, and Panic Tails -/

def scShimSpec (A : RustAlloc) : Spec Unit where
  pre := fun _ s0 => A.pool ∗ stackAt s0.sp extHookStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp extHookStack

def scMemcpySpec (A : RustAlloc) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length⌝ ∗
    memRegion dst bs.length ∗
    (src ↦ₛ bs) ∗
    A.pool ∗ stackAt s0.sp extHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
    (dst ↦ₛ bs) ∗
    (src ↦ₛ bs) ∗
    A.pool ∗ stackAt s0.sp extHookStack

open Lean Elab Tactic Meta in
elab "wpx_clear_invs" : tactic => do
  let g0 ← getMainGoal
  let invs ← g0.withContext do
    let mut acc : Array FVarId := #[]
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail then
        let dty ← instantiateMVars decl.type
        if (inImageKitFindImg? dty).isSome then
          acc := acc.push decl.fvarId
    return acc
  if !invs.isEmpty then
    let g1 ← g0.tryClearMany invs
    setGoals ([g1] ++ (← getGoals).tail)

theorem sc_shim_ok_at {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      ((scShimSpec A).inImage img) := by
  have hraw := hA.session_shim_ok_at sessionCloneName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
    (hk := by simp only [fnOff_sessionClone, shimName, arm64_norm])
  refine subroutine_ok_frame_weaken_inImage (fun _ _ => A.pool) hraw
    (fun _ _ => ?_) (fun _ _ _ => ?_) (fun _ _ _ => Entails.pure_left False.elim)
  · simp only [scShimSpec, withStack, LibsignalTripleRatchet.sessionShimSpec, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)
  · simp only [scShimSpec, withStack, LibsignalTripleRatchet.sessionShimSpec]
    exact Entails.of_eq (by ac_rfl)

theorem sc_alloc_ok_at {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      ((rustAllocSpecWithStack A extHookStack).inImage img) :=
  hA.alloc_ok_at sessionCloneName
    (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
    (hk := by simp only [fnOff_sessionClone, allocName, arm64_norm])

theorem sc_memcpy_ok_at {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      ((scMemcpySpec A).inImage img) := by
  have hraw := hA.session_memcpy_ok_at sessionCloneName
    (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
    (hk := by simp only [fnOff_sessionClone, memcpyName, arm64_norm])
  refine subroutine_ok_frame_weaken_inImage (fun _ _ => A.pool) hraw
    (fun _ _ => ?_) (fun _ _ _ => ?_) (fun _ _ _ => Entails.pure_left False.elim)
  · simp only [scMemcpySpec, LibsignalTripleRatchet.sessionMemcpySpec, libcMemcpySpec]
    exact Entails.of_eq (by ac_rfl)
  · simp only [scMemcpySpec, LibsignalTripleRatchet.sessionMemcpySpec, libcMemcpySpec]
    exact Entails.of_eq (by ac_rfl)

theorem sc_panic_at_handle_error {img : Obj.Image}
    {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt img.base ext).externAt?
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")) =
      some Rust.panicked :=
  panic_at_panicSymbol fnOff_sessionClone (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
    (by decide) (by decide) (ls_hook% "alloc::raw_vec::handle_error") (by simp [Rust.isPanicSymbol])

theorem fnAddr_sessionClone_to_chainCloneLocal1 {img : Obj.Image} {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone") =
      (tripleRatchetProgAtExt img.base ext).fnAddr chainCloneLocal1Name := by
  change (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff sessionCloneName)) + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone") =
    img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff chainCloneLocal1Name)
  rw [fnOff_sessionClone, fnOff_chainCloneLocal1]
  bv_omega

theorem sc_chainClone_ok_at {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hcc : ChainCloneLocal1Ok img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      ((chainCloneSpecX A).inImage img) := by
  rwa [fnAddr_sessionClone_to_chainCloneLocal1]

theorem sc_senderChainClone_ok_at {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hscc : SenderChainCloneLocal1Ok img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      ((senderChainCloneSpecX A).inImage img) := by
  rwa [fnAddr_sessionClone_to_chainCloneLocal1]

abbrev scPanicPost (A : RustAlloc) (x : SessionCloneGhost) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (sessionCloneSpecX A).onPanic x s0 sf ∗ R)

theorem sc_onPanic_of_allocFailed {A : RustAlloc} {x : SessionCloneGhost}
    {R P_f : SepProp} {s0 sf : State}
    (halloc : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
    (hm : sf.mem ⊨ P_f ∗ R) :
    sf.mem ⊨ (sessionCloneSpecX A).onPanic x s0 sf ∗ R := by
  dsimp only [sessionCloneSpecX, allocPanic]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨halloc, ?_⟩
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap P_f)) hm

theorem sc_onPanic_of_callee_panic {A : RustAlloc} {x : SessionCloneGhost}
    {F R : SepProp} {s0 s_call sf : State}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (sessionCloneSpecX A).onPanic x s0 sf ∗ R := by
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  obtain ⟨⟨haf, hpre⟩, hm'⟩ := hm
  unfold allocFailedIn at haf
  rw [htr] at haf hpre
  rw [← sepConj_assoc] at hm'
  exact sc_onPanic_of_allocFailed ⟨haf, hpre⟩ hm'

theorem sc_panic_0x474 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x474#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  have hpanic := sc_panic_at_handle_error (img := img) (ext := ext)
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x474 12
  clear hfn; unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches; apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")); wp_steps
  refine SepWP.done rfl hrun (SepWPpX.panic hrun hpanic fun hm => ?_)
  exact sc_onPanic_of_allocFailed (Record.SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem sc_panic_0x480 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x480#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  have hpanic := sc_panic_at_handle_error (img := img) (ext := ext)
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x480 12
  clear hfn; unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches; apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")); wp_steps
  refine SepWP.done rfl hrun (SepWPpX.panic hrun hpanic fun hm => ?_)
  exact sc_onPanic_of_allocFailed (Record.SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem sc_panic_0x48c {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x48c#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  have hpanic := sc_panic_at_handle_error (img := img) (ext := ext)
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x48c 12
  clear hfn; unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches; apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")); wp_steps
  refine SepWP.done rfl hrun (SepWPpX.panic hrun hpanic fun hm => ?_)
  exact sc_onPanic_of_allocFailed (Record.SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem sc_panic_0x498 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x498#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  have hpanic := sc_panic_at_handle_error (img := img) (ext := ext)
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x498 12
  clear hfn; unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches; apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")); wp_steps
  refine SepWP.done rfl hrun (SepWPpX.panic hrun hpanic fun hm => ?_)
  exact sc_onPanic_of_allocFailed (Record.SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem sc_panic_0x4a4 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x4a4#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  have hpanic := sc_panic_at_handle_error (img := img) (ext := ext)
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x4a4 12
  clear hfn; unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches; apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")); wp_steps
  refine SepWP.done rfl hrun (SepWPpX.panic hrun hpanic fun hm => ?_)
  exact sc_onPanic_of_allocFailed (Record.SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem sc_panic_0x4b0 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : SessionCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x4b0#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  have hpanic := sc_panic_at_handle_error (img := img) (ext := ext)
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x4b0 12
  clear hfn; unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches; apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")); wp_steps
  refine SepWP.done rfl hrun (SepWPpX.panic hrun hpanic fun hm => ?_)
  exact sc_onPanic_of_allocFailed (Record.SegCloneSteps.allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

/-! ## 2. Frame-Pointer (`x29 = sp + 0x170`) and Stack Normalization -/

@[scoped arm64_norm, scoped wp_norm]
theorem fp_sub_120 (sp : BitVec 64) :
    (sp + 0x170#64) - 120#64 = sp + 0xf8#64 := by bv_omega

@[scoped arm64_norm, scoped wp_norm]
theorem fp_add_neg_120 (sp : BitVec 64) :
    (sp + 0x170#64) + bv% (2 ^ 64 - 120) = sp + 0xf8#64 := by bv_omega

@[scoped arm64_norm, scoped wp_norm]
theorem fp_add_neg_120_hex (sp : BitVec 64) :
    (sp + 0x170#64) + 0xffffffffffffff88#64 = sp + 0xf8#64 := by bv_omega

@[scoped arm64_norm, scoped wp_norm]
theorem fp_add_neg_112_hex (sp : BitVec 64) :
    (sp + 0x170#64) + 0xffffffffffffff90#64 = sp + 0x100#64 := by bv_omega

@[scoped arm64_norm, scoped wp_norm]
theorem fp_add_neg_104_hex (sp : BitVec 64) :
    (sp + 0x170#64) + 0xffffffffffffff98#64 = sp + 0x108#64 := by bv_omega

@[scoped arm64_norm, scoped wp_norm]
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

/-! ## 3. Stack Frame (`sessionCloneStackX`), Spill Slots (`sp .. sp + 0x90`), and Saved Regs -/

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

/-- Decomposition of `stackAt sp0 sessionCloneStackX` around `sp = sp0 - 0x1d0#64`. -/
theorem stackAt_sessionClone_eq (sp0 : BitVec 64) :
    stackAt sp0 sessionCloneStackX =
      let sp := sp0 - 0x1d0#64
      memRegion (sp0 - BitVec.ofNat 64 sessionCloneStackX) 0x400 ∗
      stackAt sp chainCloneStackX ∗
      memRegion sp 0x90 ∗
      memRegion (sp + 0x90#64) 96 ∗
      memRegion (sp + 0xf0#64) 8 ∗
      memRegion (sp + 0xf8#64) 104 ∗
      memRegion (sp + 0x160#64) 16 ∗
      memRegion (sp + 0x170#64) 0x60 := by
  dsimp only
  unfold stackAt
  set sp := sp0 - 0x1d0#64
  rw [memRegion_split' (b := sp0 - BitVec.ofNat 64 sessionCloneStackX)
        (b' := sp - BitVec.ofNat 64 chainCloneStackX) (n := 0x400) (k := chainCloneStackX + 0x1d0)
        (by decide) (by dsimp [sp, sessionCloneStackX, chainCloneStackX, extHookStack]; bv_arith) (by decide),
      memRegion_split' (b := sp - BitVec.ofNat 64 chainCloneStackX)
        (b' := sp) (n := chainCloneStackX) (k := 0x1d0)
        rfl (by dsimp [sp, chainCloneStackX, extHookStack]; bv_arith) (by decide),
      memRegion_split' (b := sp) (b' := sp + 0x90#64) (n := 0x90) (k := 320) rfl rfl (by decide),
      memRegion_split' (b := sp + 0x90#64) (b' := sp + 0xf0#64) (n := 96) (k := 224) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0xf0#64) (b' := sp + 0xf8#64) (n := 8) (k := 216) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0xf8#64) (b' := sp + 0x160#64) (n := 104) (k := 112) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x160#64) (b' := sp + 0x170#64) (n := 16) (k := 96) rfl (by bv_arith) (by decide)]

/-! ## 4. Source `sessionStateAt` and Destination `scDstSlotsAt` at Arbitrary Pointers -/

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

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
