/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Specifications.SignalSession.CliRun
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRunFixed
public import GeneratedLean.LibsignalSessionObj

/-!
# Guards for the `signal-session` CLI Image and Hook Table

**Checked by Lean.** Kernel-checked guards (`rfl_kernel`, `decide`) for the `signal-session` CLI
specification (`LibsignalBinary/Specifications/SignalSession/`); see
`Computational/docs/TRUSTED_BASE.md`. Verifies distinctness of the party identity keys, the single
`.tpoff 0x10` GOT entry of `libsignalSessionImage`, uniqueness and panic-disjointness of the 46
hooked stub names in `cliHookTable`, unique stub resolution in `libsignalSessionImage.stubs`, and
unique symbol resolution of `"main"`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

open Arm64 ProofLib
open CryptoVerification.LibsignalSpqrV1
  (mlkemFromSeedName mlkemPk1Name mlkemPk2Name mlkemEncaps1Name mlkemEncaps2Name
   mlkemDecapsName mlkemValidatePkName libcruxHmacName)

theorem idOfE_ne_cli : CryptoVerification.E2E.partyIdentityKey .A ≠ CryptoVerification.E2E.partyIdentityKey .B := by
  decide

set_option maxRecDepth 1000000 in
open ProofLib.ProgramReflection in
theorem session_got_tpoff : CryptoVerification.libsignalSessionImage.got = [.tpoff 0x10] := by
  rfl_kernel

/-- The 46 hooked stub names of `cliHookTable W` in table order: 10 PQXDH curve/SHA-512/Kyber
stubs, 8 SPQR V1 stubs, and 28 allocator, libc, I/O, `core`/`std`, `subtle`, and primitive stubs. -/
def cliHookStubNames : List String :=
  ["sha2::sha512::compress512",
   "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards",
   "<curve25519_dalek::edwards::EdwardsPoint>::compress",
   "<curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Neg>::neg",
   "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free",
   "<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint",
   "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order",
   "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide",
   "libcrux_ml_kem::mlkem1024::kyber::encapsulate",
   "libcrux_ml_kem::mlkem1024::kyber::decapsulate",
   mlkemFromSeedName,
   mlkemPk1Name,
   mlkemPk2Name,
   mlkemEncaps1Name,
   mlkemEncaps2Name,
   mlkemDecapsName,
   mlkemValidatePkName,
   libcruxHmacName,
   "__rustc::__rust_no_alloc_shim_is_unstable_v2",
   "__rustc::__rust_alloc",
   "__rustc::__rust_dealloc",
   "__rustc::__rust_realloc",
   "__rustc::__rust_alloc_zeroed",
   "memset",
   "memmove",
   "memcpy",
   "bcmp",
   "strlen",
   readFileName,
   writeFileName,
   readStdinName,
   writeStdoutName,
   "core::slice::memchr::memrchr",
   "core::str::converts::from_utf8",
   "core::fmt::write",
   "alloc::fmt::format::format_inner",
   "<std::time::SystemTime>::duration_since",
   "<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add",
   "subtle::black_box::<u8>",
   "sha2::sha256::compress256",
   "signal_crypto::aes_cbc::aes_256_cbc_encrypt",
   "signal_crypto::aes_cbc::aes_256_cbc_decrypt",
   "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from",
   "<x25519_dalek::x25519::StaticSecret>::diffie_hellman",
   "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop",
   "<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop"]

/-- Image-specific panic wrapper stub mapped to `Rust.panicked` outside `Arm64.Rust.isPanicSymbol`. -/
def cliExtraPanicStubNames : List String :=
  ["<alloc::vec::Vec<_, _>>::remove::assert_failed"]

theorem cliHookTable_names_eq (W : CliHooks) :
    (cliHookTable W).map Prod.fst = cliHookStubNames :=
  rfl

theorem cliHookStubNames_nodup : cliHookStubNames.Nodup := by
  decide +kernel

theorem cliHookTable_nodup (W : CliHooks) : ((cliHookTable W).map Prod.fst).Nodup := by
  rw [cliHookTable_names_eq]
  exact cliHookStubNames_nodup

set_option maxRecDepth 1000000 in
open ProofLib.ProgramReflection in
theorem cliHookStubNames_notRustPanic :
    cliHookStubNames.all (fun n => !Arm64.Rust.isPanicSymbol n) = true := by
  rfl_kernel

theorem cliHookStubNames_notExtraPanic :
    cliHookStubNames.all (fun n => !cliExtraPanicStubNames.contains n) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
open ProofLib.ProgramReflection in
/-- Every stub in `cliHookStubNames` and `cliExtraPanicStubNames` resolves to a unique offset in
`libsignalSessionImage.stubs` and is absent from `libsignalSessionImage.symbols`. -/
theorem cliHookStubs_resolve :
    (cliHookStubNames ++ cliExtraPanicStubNames).all (fun n =>
      match Obj.lookupUnique n CryptoVerification.libsignalSessionImage.stubs with
      | some o =>
        !CryptoVerification.libsignalSessionImage.symbols.any (·.1 == n) &&
          (CryptoVerification.libsignalSessionImage.stubs.filter (·.2 == o)).length == 1
      | none => false) = true := by
  rfl_kernel

set_option maxRecDepth 1000000 in
open ProofLib.ProgramReflection in
theorem cliMain_resolves :
    ((Obj.lookupUnique "main" CryptoVerification.libsignalSessionImage.symbols).isSome &&
      !CryptoVerification.libsignalSessionImage.stubs.any (·.1 == "main")) = true := by
  rfl_kernel

end CryptoVerification.SignalSession
