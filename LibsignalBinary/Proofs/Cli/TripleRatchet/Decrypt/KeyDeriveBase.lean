/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.Defs
import all Init.Data.String.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBase
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplay
import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep

/-!
# `try_decrypt_with_state` Key-Derivation Fetch and Callee Helpers

Shared instruction-fetch lemmas and callee address/contract bridges (`spqr::recv`,
`<ProtocolAddress as Display>::fmt`, `format_inner`, `__rust_dealloc`) for segments S4–S6 of
`try_decrypt_with_state`.
-/

@[expose] public section

/-- Resolves `<P>Cli_decode_…` in the current scope when present, falling back to `<P>_decode_…`. -/
private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n


namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Decrypt

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc

attribute [local wp_norm] BitVec.add_assoc

macro "decrypt_fetches_cli " b:term:max H:term:max hfn:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode libsignalTripleRatchetBinCli $b $H
    $hfn (num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")) $k0 $len)

namespace KeyDeriveCallees

@[irreducible] noncomputable def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext (b : BitVec 64)
    (ext : String → Option (State → State)) : BitVec 64 :=
  (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext b ext := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext
  rfl

@[irreducible] noncomputable def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : BitVec 64 :=
  (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt b C ctl abs := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt
  rfl

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnOff_tryDecrypt :
    CryptoVerification.libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") :=
  (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")

/-- `spqr::recv` as a wrapping offset from `try_decrypt_with_state`: in the CLI image `spqr::recv` lies
below it, so the callee lemmas are applied at `spqr::recv`'s own entry (`k = 0`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.tryDecrypt_add_spqrRecv_eq_fnAddr (b : BitVec 64) (H : String → Option (State → State)) :
    (CryptoVerification.libsignalSessionCode.rebase b H).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + bv% ((2^64 + ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64) =
      (CryptoVerification.libsignalSessionCode.rebase b H).fnAddr spqrRecvName + BitVec.ofNat 64 0 := by
  change (b + BitVec.ofNat 64 (CryptoVerification.libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)) + bv% ((2^64 + ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64) =
    (b + BitVec.ofNat 64 (CryptoVerification.libsignalSessionCode.fnOff spqrRecvName)) + BitVec.ofNat 64 0
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnOff_tryDecrypt, fnOff_spqrRecv]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.hk_formatInner :
    CryptoVerification.libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") =
      CryptoVerification.libsignalSessionCode.fnOff formatInnerName := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnOff_tryDecrypt, fnOff_formatInner]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.hk_dealloc :
    CryptoVerification.libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") =
      CryptoVerification.libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnOff_tryDecrypt, (ls_stub% "__rustc::__rust_dealloc")]

/-- `ProtocolAddress as Display>::fmt` as a wrapping offset from `try_decrypt_with_state`: in the CLI image it
lies below it, so the callee lemmas are applied at its own entry (`k = 0`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.tryDecrypt_add_addrDisplay_eq_fnAddr (b : BitVec 64) (H : String → Option (State → State)) :
    (CryptoVerification.libsignalSessionCode.rebase b H).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + bv% ((2^64 + ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64) =
      (CryptoVerification.libsignalSessionCode.rebase b H).fnAddr addrDisplayName + BitVec.ofNat 64 0 := by
  change (b + BitVec.ofNat 64 (CryptoVerification.libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)) + bv% ((2^64 + ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64) =
    (b + BitVec.ofNat 64 (CryptoVerification.libsignalSessionCode.fnOff addrDisplayName)) + BitVec.ofNat 64 0
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnOff_tryDecrypt, fnOff_addrDisplay]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fetch_tryDecrypt_at_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {entry : BitVec 64}
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext b ext = entry)
    {k off_k : Nat} {inst : Instr}
    (hadd : (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") + k = off_k)
    (htext : Nat.ble off_k (num% (ls_field% textEnd - 1)) = true)
    (h : CryptoVerification.libsignalSessionCode_tree.fetchDecodeAt off_k = some inst) :
    (tripleRatchetProgAtExt b ext).fetch (entry + BitVec.ofNat 64 k) = some inst := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq]
  subst hadd
  have hlt : (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") + k < num% (ls_field% textEnd) := Nat.lt_succ_of_le (Nat.le_of_ble_eq_true htext)
  exact CryptoVerification.libsignalSessionCode_fetch_fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnOff_tryDecrypt hlt h (lt_two_pow_64_of_lt_text hlt)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fetch_tryDecrypt_at {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {entry : BitVec 64}
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt b C ctl abs = entry)
    {k off_k : Nat} {inst : Instr}
    (hadd : (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") + k = off_k)
    (htext : Nat.ble off_k (num% (ls_field% textEnd - 1)) = true)
    (h : CryptoVerification.libsignalSessionCode_tree.fetchDecodeAt off_k = some inst) :
    (tripleRatchetProgAt b C ctl abs).fetch (entry + BitVec.ofNat 64 k) = some inst := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_eq]
  subst hadd
  have hlt : (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") + k < num% (ls_field% textEnd) := Nat.lt_succ_of_le (Nat.le_of_ble_eq_true htext)
  exact CryptoVerification.libsignalSessionCode_fetch_fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnOff_tryDecrypt hlt h (lt_two_pow_64_of_lt_text hlt)

open Lean Elab Tactic in
elab "decrypt_fetches_at_ext_cli " hentry:ident k0:num len:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let off := num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")
  let k0 := k0.getNat
  let len := len.getNat
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let off_k := off + k
    let dec := mkIdent (portCliPickCli portEnv portOpts portNs portOd ((`libsignalTripleRatchetBinCli).appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 off_k)}"))
    let kq := Syntax.mkNumLit (toString k)
    let offkq := Syntax.mkNumLit (toString off_k)
    evalTactic (← `(tactic|
      have := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fetch_tryDecrypt_at_ext $hentry (k := $kq) (off_k := $offkq) rfl rfl $dec))

open Lean Elab Tactic in
elab "decrypt_fetches_at_cli " hentry:ident k0:num len:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let off := num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")
  let k0 := k0.getNat
  let len := len.getNat
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let off_k := off + k
    let dec := mkIdent (portCliPickCli portEnv portOpts portNs portOd ((`libsignalTripleRatchetBinCli).appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 off_k)}"))
    let kq := Syntax.mkNumLit (toString k)
    let offkq := Syntax.mkNumLit (toString off_k)
    evalTactic (← `(tactic|
      have := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fetch_tryDecrypt_at $hentry (k := $kq) (off_k := $offkq) rfl rfl $dec))

end KeyDeriveCallees

namespace KeyDeriveCallees

/-- `spqr::recv` is in-image code and `Stage2Contracts` does not carry it: the
`Q`-restricted recv contract `hrecv` on `tripleRatchetProgAtExt img.base ext` is taken explicitly. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.spqrRecv_ok_at_entry_ext {Q : List (BitVec 8) → Prop} {A : RustAlloc} {S : SpqrModel}
    {img : Obj.Image} {ext : String → Option (State → State)} {entry : BitVec 64}
    (hrecv : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
      ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes)))
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% ((2^64 + ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
      ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes)) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq]
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.tryDecrypt_add_spqrRecv_eq_fnAddr]
  exact sub_ok_at_of_fnAddr hrecv spqrRecvName 0 (Nat.add_zero _)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.spqrRecv_ok_at_entry_extQF {Q : List (BitVec 8) → Prop} {Pstk : Nat → Prop} {F : SepProp}
    {A : RustAlloc} {S : SpqrModel} {img : Obj.Image}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hrecv : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
      (spqrRecvSpecQF Q Pstk F A S img))
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (entry + bv% ((2^64 + ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
      (spqrRecvSpecQF Q Pstk F A S img) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq]
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.tryDecrypt_add_spqrRecv_eq_fnAddr]
  exact sub_ok_at_of_fnAddr hrecv spqrRecvName 0 (Nat.add_zero _)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.spqrRecv_ok_at_entry {Q : List (BitVec 8) → Prop} {A : RustAlloc} {S : SpqrModel}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {img : Obj.Image} {entry : BitVec 64}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hrecv : SpqrRecvOkQ Q C A ctl S abs img)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt img.base C ctl abs = entry) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (entry + bv% ((2^64 + ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
      ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes)) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_eq]
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.tryDecrypt_add_spqrRecv_eq_fnAddr]
  exact spqrRecv_ok_at_tripleRatchet hloads hrecv (name := spqrRecvName) (k := 0) (Nat.add_zero _)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.formatInner_ok_at_entry_ext_trap {A : RustAlloc} {S : SpqrModel} {b : BitVec 64} {C : Crypto}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hC : Stage2Contracts_trap b C A uuidTryParse S ext)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext b ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64)) (formatInnerSpec A) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq]
  exact sub_ok_at_of_fnAddr hC.format_inner CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
    (num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.hk_formatInner

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.formatInner_ok_at_entry_ext {A : RustAlloc} {S : SpqrModel} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hC : Stage2Contracts b C A ctl uuidTryParse S ext)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext b ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64)) (formatInnerSpec A) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.formatInner_ok_at_entry_ext_trap hC.to_trap hentry

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.formatInner_ok_at_entry_trap {A : RustAlloc} {S : SpqrModel} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {entry : BitVec 64}
    (hS : TripleRatchetHooks C A S abs)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext b (trTrapExterns C abs) = entry) :
    subroutine_ok (trTrapProgAt b C abs) (entry + bv% ((2^64 + ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64)) (formatInnerSpec A) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.formatInner_ok_at_entry_ext_trap
    (Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hS) hentry

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.formatInner_ok_at_entry {A : RustAlloc} {S : SpqrModel} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {entry : BitVec 64}
    (hS : TripleRatchetHooks C A S abs)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt b C ctl abs = entry) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) (entry + bv% ((2^64 + ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64)) (formatInnerSpec A) := by
  have hentry_trap : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext b (trTrapExterns C abs) = entry := by
    rw [← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq,
      (trapsOnly_trTrap_kit b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName,
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_eq, hentry]
  exact subroutine_ok_kit_of_trTrap
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.formatInner_ok_at_entry_trap hS hentry_trap)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.dealloc_ok_at_entry_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (halloc : AllocContracts b A ext)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext b ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64)) (rustDeallocSpec A) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq]
  exact halloc.dealloc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")) CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.hk_dealloc

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.dealloc_ok_at_entry_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {entry : BitVec 64}
    (halloc : AllocHooks A abs)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext b (trTrapExterns C abs) = entry) :
    subroutine_ok (trTrapProgAt b C abs) (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64)) (rustDeallocSpec A) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.dealloc_ok_at_entry_ext
    (AllocContracts.of_tripleRatchetProgAt_trap b C A abs halloc) hentry

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.dealloc_ok_at_entry {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {entry : BitVec 64}
    (halloc : AllocHooks A abs)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt b C ctl abs = entry) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64)) (rustDeallocSpec A) := by
  have hentry_trap : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext b (trTrapExterns C abs) = entry := by
    rw [← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq,
      (trapsOnly_trTrap_kit b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName,
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_eq, hentry]
  exact subroutine_ok_kit_of_trTrap
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.dealloc_ok_at_entry_trap halloc hentry_trap)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.addrDisplay_ok_at_entry_ext_trap {A : RustAlloc} {S : SpqrModel} {b : BitVec 64} {C : Crypto}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hC : Stage2Contracts_trap b C A uuidTryParse S ext)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext b ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64)) (addrDisplaySpec A) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq]
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.tryDecrypt_add_addrDisplay_eq_fnAddr]
  exact inImage_ok_at_rebase (Nat.add_zero _)
    (addrDisplay_ok_of_contract b A (Rust.withPanics ext)
      (sub_ok_at_of_fnAddr hC.fmt_write addrDisplayName (num% (ls_off% "core::fmt::write" - ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt"))
        (by rw [(ls_lemma% fnOff "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt"),
              (ls_stub% "core::fmt::write")])))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.addrDisplay_ok_at_entry_ext {A : RustAlloc} {S : SpqrModel} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hC : Stage2Contracts b C A ctl uuidTryParse S ext)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext b ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% ((2^64 + ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64)) (addrDisplaySpec A) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.addrDisplay_ok_at_entry_ext_trap hC.to_trap hentry

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.addrDisplay_ok_at_entry_trap {A : RustAlloc} {S : SpqrModel} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {entry : BitVec 64}
    (hS : TripleRatchetHooks C A S abs)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext b (trTrapExterns C abs) = entry) :
    subroutine_ok (trTrapProgAt b C abs) (entry + bv% ((2^64 + ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64)) (addrDisplaySpec A) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.addrDisplay_ok_at_entry_ext_trap
    (Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hS) hentry

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.addrDisplay_ok_at_entry {A : RustAlloc} {S : SpqrModel} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {entry : BitVec 64}
    (hS : TripleRatchetHooks C A S abs)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt b C ctl abs = entry) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) (entry + bv% ((2^64 + ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64)) (addrDisplaySpec A) := by
  have hentry_trap : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext b (trTrapExterns C abs) = entry := by
    rw [← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq,
      (trapsOnly_trTrap_kit b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName,
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_eq, hentry]
  exact subroutine_ok_kit_of_trTrap
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.addrDisplay_ok_at_entry_trap hS hentry_trap)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.entry_eq_base_ext {b : BitVec 64} {ext : String → Option (State → State)} {entry : BitVec 64}
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext b ext = entry) :
    entry = b + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq, Program.fnAddr_rebase, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnOff_tryDecrypt]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.entry_eq_base {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {entry : BitVec 64}
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt b C ctl abs = entry) :
    entry = b + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_eq, Program.fnAddr_rebase, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnOff_tryDecrypt]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.spqrRecvEmptyAny_ok_at_entry_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% ((2^64 + ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
      ((spqrRecvEmptyAnySpec A).inImage img) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq]
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.tryDecrypt_add_spqrRecv_eq_fnAddr]
  exact hC.spqr_recv_ok_at spqrRecvName 0 (Nat.add_zero _)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.formatInner_ok_at_entry_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% ((2^64 + ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
      ((formatInnerSpec A).inImage img) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq]
  exact hC.format_inner_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")) CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.hk_formatInner

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.dealloc_ok_at_entry_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (halloc : AllocContractsX img A ext)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq]
  exact halloc.dealloc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")) CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.hk_dealloc

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.addrDisplay_ok_at_entry_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% ((2^64 + ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
      ((addrDisplaySpec A).inImage img) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq]
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.tryDecrypt_add_addrDisplay_eq_fnAddr]
  exact addr_display_ok_at_ext_x img C A ext hC addrDisplayName 0 (Nat.add_zero _)

end KeyDeriveCallees

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.msg_pqRatchet_lt_of_commonHeap {A : RustAlloc} {ctl : BitVec 64} {img : Obj.Image}
    {x : TryDecryptGhost} {draws : Nat} {s0 : State} {m : Memory} {P Q : SepProp}
    (h : m ⊨ P ∗ CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ Q) :
    x.msg.pqRatchet.length < 2 ^ 40 := by
  rw [sepConj_left_comm] at h
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap signalMessageAt at h
  simp only [sepConj_assoc] at h
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, satisfies_pure_sepConj] at h
  exact h.1.2.2.2.1

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.onPanic_drop_frame {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {F R : SepProp} {s0 s' : State}
    (h : s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ (F ∗ R)) :
    s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  rcases h with ⟨hcond, hmem⟩
  rw [← sepConj_assoc] at hmem
  exact ⟨hcond, Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hmem⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.onPanic_of_spqrRecv {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {st msg : VecArg} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (hst : st.bytes = x.st.pqRatchetState)
    (hmsg : msg.bytes = x.msg.pqRatchet)
    (h : sf.mem ⊨ ((spqrRecvSpec A S img).onPanic (st, msg, ret) sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  dsimp only [spqrRecvSpec, CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨⟨hpan, hpref⟩, hmem⟩
  rw [← sepConj_assoc] at hmem
  rw [hst, hmsg, allocFailedIn, htrace, ← allocFailedIn] at hpan
  rw [htrace] at hpref
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨?_, hpref⟩, ?_⟩
  · rcases hpan with ha | hp
    · exact Or.inr (Or.inr ha)
    · exact Or.inr (Or.inl hp)
  · exact Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hmem

set_option maxRecDepth 2000000 in
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.rodata_0x45416_eq :
    (libsignalSessionImage.data.drop (num% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>" + 2456)) - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 7 = utf8 "decrypt" := by
  rfl_kernel

set_option maxRecDepth 2000000 in
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.rodata_decrypt_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>" + 2456))) ↦ᵣ utf8 "decrypt") ∗ P := by
  have hdlen : num% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>" + 2456)) - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)) + 7 ≤ libsignalSessionImage.data.length := by
    have h1 := congrArg List.length CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.rodata_0x45416_eq
    rw [List.length_take, List.length_drop, KeyDeriveCallees.utf8_decrypt_len] at h1
    omega
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (secOff := num% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>" + 2456))) (secLen := 7) (dataOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    hdlen (by rfl_kernel) hro hP
  rwa [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.rodata_0x45416_eq] at h

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.onPanic_of_formatInner {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((formatInnerSpec A).onPanic ret sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  dsimp only [formatInnerSpec, CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨⟨hpan, hpref⟩, hmem⟩
  rw [← sepConj_assoc] at hmem
  rw [allocFailedIn, htrace, ← allocFailedIn] at hpan
  rw [htrace] at hpref
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨Or.inr (Or.inr hpan), hpref⟩, ?_⟩
  exact Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hmem

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.onPanic_of_formatInner_fn {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (h : sf.mem ⊨ (((formatInnerSpec A).inImage img).onPanic ret sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  dsimp only [formatInnerSpec, CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨⟨hpan, hpref⟩, hmem⟩
  rw [← sepConj_assoc] at hmem
  rw [allocFailedIn, htrace, ← allocFailedIn] at hpan
  rw [htrace] at hpref
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨Or.inr (Or.inr hpan), hpref⟩, ?_⟩
  exact Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hmem

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.adrp_decryptStr {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64) (he : entry = b + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")) :
    (((entry + bv% (2452)) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>" + 2456)) - page% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>" + 2452))) + bv% ((ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>" + 2456)) % 4096) =
      b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>" + 2452) (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>" + 2456)) := by
  subst he; revert hb; bv_kernel

end CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive
