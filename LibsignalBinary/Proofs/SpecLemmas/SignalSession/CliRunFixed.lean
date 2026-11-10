/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliRun

@[expose] public section

set_option autoImplicit false

/-!
# Fixed-Image Hook Table, Extern Map, and Load Base

**Checked by Lean.** Fixed-image extern definitions for the `libsignal-cli` CLI: demangled I/O
stub names (`readFileName`, `writeFileName`, `readStdinName`, `writeStdoutName`), hook table
`cliHookTable`, panic-wrapped extern map `cliExterns`, and fixed load base `cliBase = 0x400000`.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib

/-- Demangled extern stub name for `libsignal_cli_io::read_file`. -/
def readFileName : String := "libsignal_cli_io::read_file"

def writeFileName : String := "libsignal_cli_io::write_file"

def readStdinName : String := "libsignal_cli_io::read_stdin"

def writeStdoutName : String := "libsignal_cli_io::write_stdout"


/-- Fixed-image `(stubName, hook)` table combining the 18 PQXDH/SPQR hooks of
`E2E.pqxdhHookTable W.C W.Q` with the 28 allocator, libc, I/O, `core`/`std`, and session-crypto
hooks. -/
noncomputable def cliHookTable (W : CliHooks) : List (String × (State → State)) :=
  E2E.pqxdhHookTable W.C W.Q ++ [
  -- Allocator (`__rust_dealloc` is a no-op, DEV-E6).
  ("__rustc::__rust_no_alloc_shim_is_unstable_v2", hookNoop),
  ("__rustc::__rust_alloc", E2E.allocHook0),
  ("__rustc::__rust_dealloc", E2E.deallocHook),
  ("__rustc::__rust_realloc", E2E.reallocHook0),
  ("__rustc::__rust_alloc_zeroed", E2E.allocZeroedHook0),
  -- libc.
  ("memset", hookMemset),
  ("memmove", hookMemmove),
  ("memcpy", hookMemcpy),
  ("bcmp", cliBcmpHook W.bcmp),
  ("strlen", strlenHook),
  -- I/O crate.
  (readFileName, readFileHook),
  (writeFileName, writeFileHook),
  (readStdinName, readStdinHook),
  (writeStdoutName, writeStdoutHook),
  -- `core` / `std`.
  ("core::slice::memchr::memrchr", memrchrHook),
  ("core::str::converts::from_utf8", fromUtf8Hook W.utf8Err),
  ("core::fmt::write", E2E.fmtWriteHook0),
  ("alloc::fmt::format::format_inner", E2E.formatInnerHook0),
  ("<std::time::SystemTime>::duration_since", durationSinceExactHook),
  ("<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add",
    E2E.timeAddHook),
  -- `subtle::black_box`: identity on the low byte.
  ("subtle::black_box::<u8>", LibsignalSession.blackBoxHook),
  -- Session crypto primitives `W.C`.
  ("sha2::sha256::compress256", LibsignalHmac.compress256Hook W.C.F),
  ("signal_crypto::aes_cbc::aes_256_cbc_encrypt", E2E.aesEncHook0 W.C.E),
  ("signal_crypto::aes_cbc::aes_256_cbc_decrypt", E2E.aesDecHook0 W.C.D),
  ("<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from",
    LibsignalTripleRatchet.pubFromSecretHook W.C.pubKey),
  ("<x25519_dalek::x25519::StaticSecret>::diffie_hellman",
    LibsignalTripleRatchet.diffieHellmanHook W.C.X),
  -- Secret zeroization on drop.
  ("<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop",
    LibsignalTripleRatchet.zeroizeSecretHook),
  ("<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop",
    LibsignalTripleRatchet.zeroizeSecretHook)]

/-- Unreached `InMem*Store` hashbrown `Fallibility` `#1` panic stubs (`0x488548`, `0x488550`),
left as zero (`udf #0`) words in the CLI ELF and excluded from `isCliPanicSymbol`. -/
def deadCliHashbrownPanicNames : List String :=
  ["<hashbrown::raw::Fallibility>::capacity_overflow#1",
   "<hashbrown::raw::Fallibility>::alloc_err#1"]

/-- Fixed-image CLI panic predicate: `E2E.isImagePanicSymbol` excluding
`deadCliHashbrownPanicNames`. -/
def isCliPanicSymbol (s : String) : Bool :=
  E2E.isImagePanicSymbol s && !(deadCliHashbrownPanicNames.contains s)

/-- Overrides `hooks` with `some Rust.panicked` on every `isCliPanicSymbol`. -/
def withCliPanics (hooks : String → Option (State → State)) :
    String → Option (State → State) :=
  fun s => if isCliPanicSymbol s then some Rust.panicked else hooks s

private theorem not_isPanicSymbol_capacityOverflow1 :
    Rust.isPanicSymbol "<hashbrown::raw::Fallibility>::capacity_overflow#1" = false := by
  simp [Rust.isPanicSymbol]

private theorem not_isPanicSymbol_allocErr1 :
    Rust.isPanicSymbol "<hashbrown::raw::Fallibility>::alloc_err#1" = false := by
  simp [Rust.isPanicSymbol]

theorem isCliPanicSymbol_of_isPanicSymbol {s : String} (h : Rust.isPanicSymbol s = true) :
    isCliPanicSymbol s = true := by
  have hc : s ≠ "<hashbrown::raw::Fallibility>::capacity_overflow#1" := by
    rintro rfl
    rw [not_isPanicSymbol_capacityOverflow1] at h
    cases h
  have ha : s ≠ "<hashbrown::raw::Fallibility>::alloc_err#1" := by
    rintro rfl
    rw [not_isPanicSymbol_allocErr1] at h
    cases h
  simp [isCliPanicSymbol, E2E.isImagePanicSymbol, deadCliHashbrownPanicNames, h, hc, ha]

theorem isCliPanicSymbol_eq_false_of_isImagePanicSymbol_false {s : String}
    (h : E2E.isImagePanicSymbol s = false) : isCliPanicSymbol s = false := by
  simp [isCliPanicSymbol, h]

theorem withPanics_withCliPanics (X : String → Option (State → State)) :
    Rust.withPanics (withCliPanics X) = withCliPanics X := by
  funext s
  by_cases h : Rust.isPanicSymbol s = true
  · simp [Rust.withPanics, withCliPanics, h, isCliPanicSymbol_of_isPanicSymbol h]
  · simp [Rust.withPanics, h]

@[simp] theorem withCliPanics_of_isImagePanicSymbol_false
    (hooks : String → Option (State → State)) {s : String}
    (h : E2E.isImagePanicSymbol s = false) :
    withCliPanics hooks s = hooks s := by
  simp [withCliPanics, isCliPanicSymbol, h]

@[simp] theorem withCliPanics_of_isCliPanicSymbol_false
    (hooks : String → Option (State → State)) {s : String}
    (h : isCliPanicSymbol s = false) :
    withCliPanics hooks s = hooks s := by
  simp [withCliPanics, h]

@[simp] theorem withCliPanics_of_isCliPanicSymbol_true
    (hooks : String → Option (State → State)) {s : String}
    (h : isCliPanicSymbol s = true) :
    withCliPanics hooks s = some Rust.panicked := by
  simp [withCliPanics, h]

@[simp] theorem withCliPanics_of_isPanicSymbol_true
    (hooks : String → Option (State → State)) {s : String}
    (h : Rust.isPanicSymbol s = true) :
    withCliPanics hooks s = some Rust.panicked := by
  simp [withCliPanics, isCliPanicSymbol_of_isPanicSymbol h]

/-- Fixed-image extern map combining `withCliPanics` over `cliHookTable W` (`none` elsewhere). -/
noncomputable def cliExterns (W : CliHooks) : String → Option (State → State) :=
  withCliPanics fun name => (cliHookTable W).lookup name

/-- Fixed load base address `0x400000` (`snapshot-link --base`). -/
def cliBase : BitVec 64 := 0x400000#64

end CryptoVerification.SignalSession
