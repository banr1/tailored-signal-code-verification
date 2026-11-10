/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.Defs
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.FetchClone
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Base Helpers and Panic Tails for CLI `SegClone`

Provides extern hook bridges, `Chain::clone` callee address equations, OOM `handle_error` panic
tails (`+0x25f8 .. +0x263c`), and byte-slice/`Vec<u8>` helpers for CLI `SegClone`.
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

/-! ## Extern Hooks, Callee Bridges, and Panic Tails -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_shim_ok_at {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + bv% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      sessionShimSpec :=
  hA.shim_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_cli_ratchet::decrypt_signal"))
    (by fnoff_eq)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_alloc_ok_at {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + bv% ((2^64 + ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      (rustAllocSpec A) :=
  hA.alloc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal"))
    (by fnoff_eq)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_memcpy_ok_at {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + bv% ((2^64 + ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      sessionMemcpyRegionSpec :=
  hA.session_memcpy_region_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName (num% (ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal"))
    (by fnoff_eq)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_at_handle_error {b : BitVec 64}
    {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64)) =
      some Rust.panicked :=
  panic_at_handle_error_ext b ext CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_cli_ratchet::decrypt_signal"))
    (by fnoff_eq)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.fnAddr_msgDecrypt_to_chainClone {b : BitVec 64}
    {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + bv% ((2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]") - (ls_off% "libsignal_cli_ratchet::decrypt_signal")) % 2 ^ 64) =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName := by
  dsimp only [tripleRatchetProgAtExt]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    show libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") by fnoff_eq,
    show libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]") by fnoff_eq]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_chainClone_ok_at {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hcc : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + bv% ((2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]") - (ls_off% "libsignal_cli_ratchet::decrypt_signal")) % 2 ^ 64))
      (chainCloneSpec A) := by
  rwa [CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.fnAddr_msgDecrypt_to_chainClone]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_senderChainClone_ok_at {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hscc : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + bv% ((2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]") - (ls_off% "libsignal_cli_ratchet::decrypt_signal")) % 2 ^ 64))
      (senderChainCloneSpec A) := by
  rwa [CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.fnAddr_msgDecrypt_to_chainClone]

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (img : Obj.Image)
    (x : RecordDecryptGhost) (R : SepProp) (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img).onPanic x s0 sf ∗ R)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.onPanic_of_allocFailed {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : RecordDecryptGhost} {R P_f : SepProp} {s0 sf : State}
    (halloc : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
    (hm : sf.mem ⊨ P_f ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  simpa only [CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec, Spec.inImage, sepConj_assoc] using
    allowPanic_panicked ⟨Or.inr (Or.inr halloc.1), halloc.2⟩ hm

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x25f8 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x25f8#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8
  have hpanic := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_at_handle_error (b := img.base) (ext := ext)
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x25f8 12
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
  wp_steps
  refine SepWP.done rfl hrun ?_
  refine SepWPp.panic hrun hpanic fun hm => ?_
  exact CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.onPanic_of_allocFailed (allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x2604 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x2604#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8
  have hpanic := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_at_handle_error (b := img.base) (ext := ext)
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x2604 12
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
  wp_steps
  refine SepWP.done rfl hrun ?_
  refine SepWPp.panic hrun hpanic fun hm => ?_
  exact CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.onPanic_of_allocFailed (allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x2610 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x2610#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8
  have hpanic := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_at_handle_error (b := img.base) (ext := ext)
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x2610 12
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
  wp_steps
  refine SepWP.done rfl hrun ?_
  refine SepWPp.panic hrun hpanic fun hm => ?_
  exact CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.onPanic_of_allocFailed (allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x261c {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x261c#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8
  have hpanic := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_at_handle_error (b := img.base) (ext := ext)
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x261c 12
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
  wp_steps
  refine SepWP.done rfl hrun ?_
  refine SepWPp.panic hrun hpanic fun hm => ?_
  exact CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.onPanic_of_allocFailed (allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x2628 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x2628#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8
  have hpanic := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_at_handle_error (b := img.base) (ext := ext)
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x2628 12
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
  wp_steps
  refine SepWP.done rfl hrun ?_
  refine SepWPp.panic hrun hpanic fun hm => ?_
  exact CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.onPanic_of_allocFailed (allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x2634 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x2634#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8
  have hpanic := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_at_handle_error (b := img.base) (ext := ext)
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x2634 12
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
  wp_steps
  refine SepWP.done rfl hrun ?_
  refine SepWPp.panic hrun hpanic fun hm => ?_
  exact CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.onPanic_of_allocFailed (allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

/-! ## Arithmetic, Byte-Slice, and `Vec<u8>` Helpers -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.onPanic_of_callee_panic {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : RecordDecryptGhost} {F R : SepProp} {s0 s_call sf : State}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  obtain ⟨⟨haf, hpre⟩, hm'⟩ := hm
  unfold allocFailedIn at haf
  rw [htr] at haf hpre
  rw [← sepConj_assoc] at hm'
  exact CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.onPanic_of_allocFailed ⟨haf, hpre⟩ hm'

set_option linter.unusedVariables false in
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fixedRest (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : RecordDecryptGhost) (sp : BitVec 64) : SepProp :=
  ((sp + 0x80#64) ↦₆₄ x.sret) ∗ ((sp + 0x88#64) ↦₆₄ x.locA) ∗ ((sp + 0x90#64) ↦₆₄ x.msgA) ∗
  memRegion (sp + 0x98#64) 4 ∗
  ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
  ((sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
  memRegion (sp + 0x4b0#64) 48 ∗ memRegion (sp + 0x4e0#64) 0xd0 ∗
  ((sp + 0x5b0#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x5b8#64) 4 ∗
  ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗ memRegion (sp + 0x5bd#64) 3 ∗
  ((sp + 0x5c0#64) ↦₆₄ (sp + 0x5bc#64)) ∗ ((sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
  ((sp + 0x5d0#64) ↦₆₄ (sp + 0x5b0#64)) ∗
  errsAt A (sp + 0x5d8#64) [] ∗
  memRegion (sp + 0x658#64) 0x4e8 ∗ memRegion (sp + 0xba0#64) 0x100 ∗
  memRegion (sp + 0xdf8#64) 8 ∗
  protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗
  CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗
  memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fixedRest_reassemble (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : RecordDecryptGhost) (sp : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v00 v08 : BitVec 64) (v14 : BitVec 32) (v18 : BitVec 64)
    (v24 v28 v2c : BitVec 32) (v30 : BitVec 64) (v3c : BitVec 32)
    (v40 v48 : BitVec 64) (v54 : BitVec 32) (v58 v60 v68 v70 v78 : BitVec 64) :
    (spillSlotsAt sp v00 v08 v14 v18 v24 v28 v2c v30 v3c v40 v48 v54 v58 v60 v68 v70 v78 ∗
      chunks96_6QAt (sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
      memRegion (sp + 0x5f0#64) 104 ∗
      ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
      memRegion (sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
      stackAt sp allocHookStack ∗ A.pool ∗
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fixedRest A ctl img x sp) ⊢
      (recFrame A img x sp ∗ errsAt A (sp + 0x5d8#64) [] ∗
        memRegion (sp + 0x4b0#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest) := by
  refine Entails.trans
    (sepConj_mono
      (spillSlotsAt_entails_memRegion_0x80 sp v00 v08 v14 v18 v24 v28 v2c v30 v3c v40 v48 v54 v58 v60 v68 v70 v78)
      (sepConj_mono_left (chunks96_6QAt_entails_memRegion (sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5))) ?_
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fixedRest recFrame
  rw [memRegion_0x5f0_0x6b0_eq sp, stackAt_root_eq_chainClone sp, stackAt_chainClone_eq_alloc sp]
  exact Entails.of_eq (by ac_rfl)

set_option linter.unusedVariables false in
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_clonePost (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : RecordDecryptGhost) (s0 sf : State) (P_f : SepProp) : Prop :=
  sf.sp = s0.sp ∧ sf.spAligned = true ∧
    sf.readReg64 .x29 = s0.readReg64 .x29 ∧ sf.trace = s0.trace ∧
    sf.readReg64 .x9 = x.msg.messageVersion.setWidth 64 ∧
    (P_f ⊢ ∃∗ G₁ : SessionGhost,
      ⌜CloneRel x.G G₁⌝ ∗
      recFrame A img x s0.sp ∗
      sessionStateAt A (s0.sp + 0x138#64) x.G x.st ∗
      sessionStateAt A (s0.sp + 0xca0#64) G₁ x.st ∗
      errsAt A (s0.sp + 0x5d8#64) [] ∗
      memRegion (s0.sp + 0x4b0#64) 48 ∗
      CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest)

end CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
