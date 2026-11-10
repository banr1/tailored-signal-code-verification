/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegMidBase
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegMidBase
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplay
import ProofLib.SepLogic.Entry
public meta import Lean -- shake: keep

/-!
# Trap-at-RNG Middle-Segment Base Helpers

Fetch macro, callee/hook wrappers, and shared separation-logic helpers for Segments S4–S6 on
`trTrapProgAt`.
-/

@[expose] public section

private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegC

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.DecryptPq

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc

attribute [local wp_norm] BitVec.add_assoc

namespace BS8

@[irreducible] noncomputable def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) : BitVec 64 :=
  (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_trap b C abs := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_trap
  rfl

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fetch_tryDecrypt_at_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {entry : BitVec 64}
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_trap b C abs = entry)
    {k off_k : Nat} {inst : Instr}
    (hadd : (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") + k = off_k)
    (htext : Nat.ble off_k (num% (ls_field% textEnd - 1)) = true)
    (h : CryptoVerification.libsignalSessionCode_tree.fetchDecodeAt off_k = some inst) :
    (trTrapProgAt b C abs).fetch (entry + BitVec.ofNat 64 k) = some inst := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq_trap]
  subst hadd
  have hlt : (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") + k < num% (ls_field% textEnd) :=
    Nat.lt_succ_of_le (Nat.le_of_ble_eq_true htext)
  exact CryptoVerification.libsignalSessionCode_fetch_fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt hlt h (lt_two_pow_64_of_lt_text hlt)

open Lean Elab Tactic in
elab "decrypt_fetches_at_cli_trap " hentry:ident k0:num len:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let off := (num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
  let k0 := k0.getNat
  let len := len.getNat
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let off_k := off + k
    let hex := String.ofList (Nat.toDigits 16 off_k)
    let dec := mkIdent (portCliPickCli portEnv portOpts portNs portOd ((`libsignalTripleRatchetBinCli).appendAfter s!"_decode_0x{hex}"))
    let kq := Syntax.mkNumLit (toString k)
    let offkq := Syntax.mkNumLit (toString off_k)
    evalTactic (← `(tactic|
      have := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fetch_tryDecrypt_at_trap $hentry (k := $kq) (off_k := $offkq) rfl rfl $dec))

end BS8

namespace BS8

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.spqrRecv_ok_at_entry_trap {Q : List (BitVec 8) → Prop} {A : RustAlloc} {S : SpqrModel}
    {C : Crypto}
    {abs : String → Option (State → State)} {img : Obj.Image} {entry : BitVec 64}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hrecv : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQ_trap Q C A S abs img)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_trap img.base C abs = entry) :
    subroutine_ok (trTrapProgAt img.base C abs)
      (entry + bv% ((2^64 + ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))
      ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes)) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq_trap, ← fnAddr_callee_of_fnOff CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt
    fnOff_spqrRecv (k := (num% ((2^64 + ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))) rfl]
  have h := hrecv
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQ_trap at h
  rwa [tripleRatchetProg_eq_tripleRatchetProgAt_trap hloads,
    entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs) hloads] at h

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.spqrRecv_ok_at_entryQF_trap {Q : List (BitVec 8) → Prop} {Pstk : Nat → Prop} {F : SepProp}
    {A : RustAlloc} {S : SpqrModel} {C : Crypto}
    {abs : String → Option (State → State)} {img : Obj.Image} {entry : BitVec 64}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hrecv : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQF_trap Q Pstk F C A S abs img)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_trap img.base C abs = entry) :
    subroutine_ok (trTrapProgAt img.base C abs)
      (entry + bv% ((2^64 + ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))
      (spqrRecvSpecQF Q Pstk F A S img) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq_trap, ← fnAddr_callee_of_fnOff CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt
    fnOff_spqrRecv (k := (num% ((2^64 + ls_off% "spqr::recv" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))) rfl]
  have h := hrecv
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQF_trap at h
  rwa [tripleRatchetProg_eq_tripleRatchetProgAt_trap hloads,
    entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs) hloads] at h

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.formatInner_ok_at_entry_trap {A : RustAlloc} {S : SpqrModel} {b : BitVec 64} {C : Crypto}
 {abs : String → Option (State → State)} {entry : BitVec 64}
    (hS : TripleRatchetHooks C A S abs)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_trap b C abs = entry) :
    subroutine_ok (trTrapProgAt b C abs)
      (entry + bv% ((2^64 + ls_off% "alloc::fmt::format::format_inner" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64))
      (formatInnerSpec A) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq_trap]
  exact format_inner_ok_at_trap b C A abs hS.formatInner CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    (num% (ls_off% "alloc::fmt::format::format_inner" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.hk_formatInner

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.dealloc_ok_at_entry_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {entry : BitVec 64}
    (halloc : AllocHooks A abs)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_trap b C abs = entry) :
    subroutine_ok (trTrapProgAt b C abs)
      (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64)) (rustDeallocSpec A) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq_trap]
  exact dealloc_ok_at_trap b C A abs halloc CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    (num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.hk_dealloc

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.addrDisplay_ok_at_entry_trap {A : RustAlloc} {S : SpqrModel} {b : BitVec 64} {C : Crypto}
 {abs : String → Option (State → State)} {entry : BitVec 64}
    (hS : TripleRatchetHooks C A S abs)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_trap b C abs = entry) :
    subroutine_ok (trTrapProgAt b C abs)
      (entry + bv% ((2^64 + ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64)) (addrDisplaySpec A) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq_trap, ← fnAddr_callee_of_fnOff CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt
    fnOff_addrDisplay (k := (num% ((2^64 + ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))) rfl]
  exact addrDisplay_ok_of_contract b A (Rust.withPanics (trTrapExterns C abs))
    (fmt_write_ok_at_trap b C A abs hS.fmtWrite addrDisplayName (num% (ls_off% "core::fmt::write" - ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt")) (by simp only [arm64_norm]))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.entry_eq_base_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {entry : BitVec 64}
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_trap b C abs = entry) :
    entry = b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq_trap, Program.fnAddr_rebase, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt]

end BS8

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegC
