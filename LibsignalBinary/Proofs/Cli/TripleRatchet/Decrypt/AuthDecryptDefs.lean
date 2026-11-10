/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefs

/-!
# Authenticated-Decryption Definitions & Stub Bridges for CLI `try_decrypt_with_state`

Provides instruction-fetch wrappers, segment entry-address equations, and extern stub bridges
for `try_decrypt_with_state::<signal_session_ratchet::Coins>` on the CLI image.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.Decrypt

open CryptoVerification.LibsignalSession

open ProofLib.ProgramReflection


set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] BitVec.toNat_zero

namespace AuthDecryptFacts

end AuthDecryptFacts

/-- Fetch hypotheses for `try_decrypt_with_state::<signal_session_ratchet::Coins>`,
    from fn-relative offset `k0`, `len` bytes. -/
macro "decrypt_fetches_cli " b:term:max C:term:max ctl:term:max abs:term:max
    hfn:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode libsignalTripleRatchetBinCli $b
    (Rust.withPanics (tripleRatchetExterns $C $ctl $abs)) $hfn (num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")) $k0 $len)

/-- Fetch hypotheses for `try_decrypt_with_state::<signal_session_ratchet::Coins>` on `tripleRatchetProgAtExt b ext`. -/
macro "decrypt_fetches_ext_cli " b:term:max ext:term:max
    hfn:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode libsignalTripleRatchetBinCli $b
    (Rust.withPanics $ext) $hfn (num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")) $k0 $len)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.hfn_tryDecrypt : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") :=
  (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")

/-! ## 1. Entry / PC Rewriting and Callee / Hook Wrappers -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.tryDecryptEntry_eq_fnAddr_ext {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName :=
  entryOf_eq_tripleRatchetProgAtExt ext himg CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.tryDecryptEntry_eq_fnAddr {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName :=
  entryOf_eq_tripleRatchetProgAt himg CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.segS7PC_eq_ext {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segVerifyMacPC img = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 0x63c := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segVerifyMacPC, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.tryDecryptEntry_eq_fnAddr_ext himg]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.segS7PC_eq {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segVerifyMacPC img = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 0x63c := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segVerifyMacPC, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.tryDecryptEntry_eq_fnAddr himg]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.segS8PC_eq_ext {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segAesDecryptPC img = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 0x678 := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segAesDecryptPC, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.tryDecryptEntry_eq_fnAddr_ext himg]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.segS8PC_eq {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segAesDecryptPC img = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 0x678 := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segAesDecryptPC, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.tryDecryptEntry_eq_fnAddr himg]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.segS9PC_eq_ext {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segApplyRatchetPC img = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 0x6a4 := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segApplyRatchetPC, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.tryDecryptEntry_eq_fnAddr_ext himg]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.segS9PC_eq {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segApplyRatchetPC img = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 0x6a4 := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segApplyRatchetPC, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.tryDecryptEntry_eq_fnAddr himg]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.errTailPC_eq_ext {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.errTailPC img = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 0x30c := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.errTailPC, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.tryDecryptEntry_eq_fnAddr_ext himg]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.errTailPC_eq {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.errTailPC img = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 0x30c := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.errTailPC, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.tryDecryptEntry_eq_fnAddr himg]

/-- Backward BL at `+0x65c` (`1628 + (-95320#64) = 18446744073709457276#64`) targets
`verifyMacWithAddressesName` (`0x1d5a0`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.bl_verifyMac_target_ext (img : Obj.Image) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")) =
      (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"), (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses")]
  bv_omega

/-- Backward BL at `+0x4e8` (`1256 + (-97424#64) = 18446744073709454800#64`) targets
`trApplyName` (`0x1cbf4`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.bl_trApply_target_ext (img : Obj.Image) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::apply_to_session_state") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")) =
      (tripleRatchetProgAtExt img.base ext).fnAddr trApplyName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"), (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::TripleRatchet>::apply_to_session_state")]
  bv_omega

/-- Backward BL at `+0x4f0` (`1264 + (-140424#64) = 18446744073709411808#64`) targets
`clearUpkName` (`0x12404`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.bl_clearUpk_target_ext (img : Obj.Image) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionState>::clear_unacknowledged_pre_key_message") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")) =
      (tripleRatchetProgAtExt img.base ext).fnAddr clearUpkName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"), (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::clear_unacknowledged_pre_key_message")]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.shim_ok_at_ext_trap (img : Obj.Image) {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts_trap img.base C A uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      sessionShimSpec :=
  hC.toAllocContracts.shim_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))

/-- Stub hook `shimName` at `+0x13b84` on `tripleRatchetProgAtExt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.shim_ok_at_ext (img : Obj.Image) {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      sessionShimSpec :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.shim_ok_at_ext_trap img hC.to_trap

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.shim_ok_at_trap (img : Obj.Image) (C : Crypto)
    (abs : String → Option (State → State)) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      sessionShimSpec :=
  hook_ok_at (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") (by decide) (by decide)
    (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2") (by simp [Rust.isPanicSymbol])
    ⟨hookNoop, rfl, sessionShim_hookOk⟩

/-- Stub hook `shimName` at `+0x13b84`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.shim_ok_at (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      sessionShimSpec := by
  rw [← (trapsOnly_trTrap_kit img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName]
  exact subroutine_ok_kit_of_trTrap
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.shim_ok_at_trap img C abs)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.memcpy_ok_at_ext_trap (img : Obj.Image) {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts_trap img.base C A uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      sessionMemcpyRegionSpec :=
  hC.toAllocContracts.session_memcpy_region_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "memcpy" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))

/-- Stub hook `memcpyName` at `+0x13bb4` on `tripleRatchetProgAtExt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.memcpy_ok_at_ext (img : Obj.Image) {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      sessionMemcpyRegionSpec :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.memcpy_ok_at_ext_trap img hC.to_trap

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.memcpy_ok_at_trap (img : Obj.Image) (C : Crypto)
    (abs : String → Option (State → State)) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      sessionMemcpyRegionSpec :=
  hook_ok_at (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") (by decide) (by decide)
    (ls_hook% "memcpy") (by simp [Rust.isPanicSymbol])
    ⟨hookMemcpy, rfl, sessionMemcpyRegion_hookOk⟩

/-- Stub hook `memcpyName` at `+0x13bb4`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.memcpy_ok_at (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      sessionMemcpyRegionSpec := by
  rw [← (trapsOnly_trTrap_kit img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName]
  exact subroutine_ok_kit_of_trTrap
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.memcpy_ok_at_trap img C abs)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.alloc_ok_at_ext_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hC : Stage2Contracts_trap img.base C A uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (rustAllocSpec A) :=
  hC.toAllocContracts.alloc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))

/-- Stub hook `allocName` at `+0x13b88` on `tripleRatchetProgAtExt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.alloc_ok_at_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (rustAllocSpec A) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.alloc_ok_at_ext_trap img C A S ext hC.to_trap

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.alloc_ok_at_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (rustAllocSpec A) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.alloc_ok_at_ext_trap img C A S _ (Stage2Contracts_trap.of_tripleRatchetProgAt'_trap hS)

/-- Stub hook `allocName` at `+0x13b88`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.alloc_ok_at (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (rustAllocSpec A) := by
  rw [← (trapsOnly_trTrap_kit img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName]
  exact subroutine_ok_kit_of_trTrap
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.alloc_ok_at_trap img C A S abs hS)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.dealloc_ok_at_ext_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hC : Stage2Contracts_trap img.base C A uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (rustDeallocSpec A) :=
  hC.toAllocContracts.dealloc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))

/-- Stub hook `deallocName` at `+0x13b94` on `tripleRatchetProgAtExt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.dealloc_ok_at_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (rustDeallocSpec A) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.dealloc_ok_at_ext_trap img C A S ext hC.to_trap

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.dealloc_ok_at_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (rustDeallocSpec A) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.dealloc_ok_at_ext_trap img C A S _ (Stage2Contracts_trap.of_tripleRatchetProgAt'_trap hS)

/-- Stub hook `deallocName` at `+0x13b94`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.dealloc_ok_at (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (rustDeallocSpec A) := by
  rw [← (trapsOnly_trTrap_kit img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName]
  exact subroutine_ok_kit_of_trTrap
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.dealloc_ok_at_trap img C A S abs hS)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.formatInner_ok_at_ext_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hC : Stage2Contracts_trap img.base C A uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (formatInnerSpec A) :=
  sub_ok_at_of_fnAddr hC.format_inner CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
    (num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))
    (by simp only [arm64_norm])

/-- Stub hook `formatInnerName` at `+0x13c60` on `tripleRatchetProgAtExt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.formatInner_ok_at_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (formatInnerSpec A) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.formatInner_ok_at_ext_trap img C A S ext hC.to_trap

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.formatInner_ok_at_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (formatInnerSpec A) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.formatInner_ok_at_ext_trap img C A S _ (Stage2Contracts_trap.of_tripleRatchetProgAt'_trap hS)

/-- Stub hook `formatInnerName` at `+0x13c60`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.formatInner_ok_at (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (formatInnerSpec A) := by
  rw [← (trapsOnly_trTrap_kit img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName]
  exact subroutine_ok_kit_of_trTrap
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.formatInner_ok_at_trap img C A S abs hS)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.aesDec_ok_at_ext_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hC : Stage2Contracts_trap img.base C A uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (aesDecSpec C.D A) :=
  sub_ok_at_of_fnAddr hC.aes_dec CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
    (num% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))
    (by simp only [arm64_norm])

/-- Stub hook `aesDecName` at `+0x13da4` on `tripleRatchetProgAtExt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.aesDec_ok_at_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (aesDecSpec C.D A) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.aesDec_ok_at_ext_trap img C A S ext hC.to_trap

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.aesDec_ok_at_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (aesDecSpec C.D A) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.aesDec_ok_at_ext_trap img C A S _ (Stage2Contracts_trap.of_tripleRatchetProgAt'_trap hS)

/-- Stub hook `aesDecName` at `+0x13da4`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.aesDec_ok_at (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      (aesDecSpec C.D A) := by
  rw [← (trapsOnly_trTrap_kit img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName]
  exact subroutine_ok_kit_of_trTrap
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.aesDec_ok_at_trap img C A S abs hS)

/-- Panic stub `handleErrorName` at `+0x13bd0` on `tripleRatchetProgAtExt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.externAt_handle_error_ext (img : Obj.Image) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt img.base ext).externAt?
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))) =
      some Rust.panicked :=
  panic_at_handle_error_ext img.base ext CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))

/-- Panic stub `handleErrorName` at `+0x13bd0`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.externAt_handle_error (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt img.base C ctl abs).externAt?
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))) =
      some Rust.panicked :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.externAt_handle_error_ext img (tripleRatchetExterns C ctl abs)

/-! ## 2. `SepWPp` Segment, Representation & Panic Bridge Lemmas -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.tryDecrypt_onPanic_of_callee (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (x : TryDecryptGhost) (s0 sm sf : State) (F R : SepProp)
    (h0m : s0.trace <+: sm.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec Spec.inImage
  exact allowPanic_frame
    (fun ⟨haf, hmf⟩ => ⟨Or.inr (Or.inr (allocFailedIn_trans h0m haf)), h0m.trans hmf⟩) hm

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.tryDecrypt_onPanic_of_direct (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (x : TryDecryptGhost) (s0 sf : State) (P R : SepProp)
    (haf : allocFailedIn s0 sf) (htr : s0.trace <+: sf.trace)
    (hm : sf.mem ⊨ P ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec Spec.inImage
  exact allowPanic_panicked ⟨Or.inr (Or.inr haf), htr⟩ hm

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.SepWPp.panic_direct_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (ext : String → Option (State → State))
    (x : TryDecryptGhost) (s0 s : State) (ret panic_pc : BitVec 64)
    (P R : SepProp) {Q : State → SepProp → Prop}
    (hpc : s.pc = panic_pc) (hrun : s.status = .Running)
    (hext : (tripleRatchetProgAtExt img.base ext).externAt? panic_pc = some Rust.panicked)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => sf.status = .Panicked → (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R)) := by
  refine SepWPp.panic_at hpc hrun hext fun _ hm_pan => ?_
  have htr_f : (Rust.panicked s).trace = s0.trace ++ [allocFailedEvent] := htr
  have haf : allocFailedIn s0 (Rust.panicked s) := by
    unfold allocFailedIn
    rw [htr_f, List.drop_left]
    exact List.Mem.head _
  have hpre : s0.trace <+: (Rust.panicked s).trace := by
    rw [htr_f]
    exact ⟨[allocFailedEvent], rfl⟩
  exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.tryDecrypt_onPanic_of_direct C A ctl S img x s0 (Rust.panicked s) P R haf hpre hm_pan

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.shim_ok_at_x (img : Obj.Image) {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      ((withStack sessionShimSpec extHookStack).inImage img) :=
  hC.shim_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.memcpy_ok_at_x (img : Obj.Image) {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      ((withStack sessionMemcpyRegionSpec extHookStack).inImage img) :=
  hC.session_memcpy_region_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "memcpy" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.alloc_ok_at_x (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (ext : String → Option (State → State))
    (hC : Stage2ContractsX img C A encFn decFn ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      ((rustAllocSpecWithStack A extHookStack).inImage img) :=
  hC.alloc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.dealloc_ok_at_x (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (ext : String → Option (State → State))
    (hC : Stage2ContractsX img C A encFn decFn ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  hC.dealloc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.formatInner_ok_at_x (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (ext : String → Option (State → State))
    (hC : Stage2ContractsX img C A encFn decFn ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      ((formatInnerSpec A).inImage img) :=
  hC.format_inner_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.aesDec_ok_at_x (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (ext : String → Option (State → State))
    (hC : Stage2ContractsX img C A encFn decFn ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
      ((aesDecFnSpec decFn A).inImage img) :=
  hC.aes_dec_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.tryDecryptFn_onPanic_of_callee (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (x : TryDecryptGhost) (s0 sm sf : State) (F R : SepProp)
    (h0m : s0.trace <+: sm.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec Spec.inImage
  exact allowPanic_frame
    (fun ⟨haf, hmf⟩ => ⟨Or.inr (Or.inr (allocFailedIn_trans h0m haf)), h0m.trans hmf⟩) hm

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.tryDecryptFn_onPanic_of_direct (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (x : TryDecryptGhost) (s0 sf : State) (P R : SepProp)
    (haf : allocFailedIn s0 sf) (htr : s0.trace <+: sf.trace)
    (hm : sf.mem ⊨ P ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec Spec.inImage
  exact allowPanic_panicked ⟨Or.inr (Or.inr haf), htr⟩ hm

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.SepWPp.panic_direct_fn_ext (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (ext : String → Option (State → State))
    (x : TryDecryptGhost) (s0 s : State) (ret panic_pc : BitVec 64)
    (P R : SepProp) {Q : State → SepProp → Prop}
    (hpc : s.pc = panic_pc) (hrun : s.status = .Running)
    (hext : (tripleRatchetProgAtExt img.base ext).externAt? panic_pc = some Rust.panicked)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => sf.status = .Panicked → (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 sf ∗ R)) := by
  refine SepWPp.panic_at hpc hrun hext fun _ hm_pan => ?_
  have htr_f : (Rust.panicked s).trace = s0.trace ++ [allocFailedEvent] := htr
  have haf : allocFailedIn s0 (Rust.panicked s) := by
    unfold allocFailedIn
    rw [htr_f, List.drop_left]
    exact List.Mem.head _
  have hpre : s0.trace <+: (Rust.panicked s).trace := by
    rw [htr_f]
    exact ⟨[allocFailedEvent], rfl⟩
  exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.tryDecryptFn_onPanic_of_direct C decFn A ctl S img x s0 (Rust.panicked s) P R haf hpre hm_pan

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.logFilterAddr_eq_at_c00_ext {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    CryptoVerification.LibsignalSession.logFilterAddr img =
      ((((libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 3072#64 &&&
        bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>" + 3072))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096)) := by
  have halign := ProofLib.ObjectLoad.base_aligned_of_loads himg
  unfold CryptoVerification.LibsignalSession.logFilterAddr
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")]
  revert halign; bv_kernel

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.logOff_eq_at_c00_ext {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    logOff img =
      (((((libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 3072#64 &&&
        bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>" + 3072))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096)) ↦₆₄ 0#64) := by
  unfold logOff
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.logFilterAddr_eq_at_c00_ext himg ext]

end CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt
