/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
import all Init.Data.String.Defs
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBase
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Contract-Backed Middle-Segment Base (`ExtSegMidBase`)

Fetch macro, callee/hook wrappers, and shared separation-logic helpers for Segments S4–S6 of
`try_decrypt_with_state::<signal_session_handshake::Coins>` on `tripleRatchetProgAtExt`.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (libsignalSessionImage)
open CryptoVerification.RustHeap (RustAlloc allocFailedIn)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser signalMessageAt utf8)
open CryptoVerification.LibsignalTripleRatchet (AllocContractsX SpqrModel Stage2ContractsX
  TryDecryptGhost VecArg addrDisplayName addrDisplaySpec addr_display_ok_at_ext_x extHookStack
  formatInnerName formatInnerSpec rustDeallocExternSpecWithStack spqrRecvName spqrRecvSpec
  sub_ok_at_of_fnAddr tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (CmkOkX cmkSpecX spqrRecvSpecQF)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees
  (fnOff_addrDisplay fnOff_formatInner fnOff_spqrRecv lt_two_pow_64_of_lt_text utf8_decrypt_len)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegMidBase

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc
attribute [local wp_norm] BitVec.add_assoc

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt_ext :
    CryptoVerification.libsignalSessionCode.fnOff
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName =
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" :=
  ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.hk_formatInner_ext :
    CryptoVerification.libsignalSessionCode.fnOff
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
      num% (ls_off% "alloc::fmt::format::format_inner" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") =
      CryptoVerification.libsignalSessionCode.fnOff formatInnerName := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt_ext, fnOff_formatInner]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.hk_dealloc_ext :
    CryptoVerification.libsignalSessionCode.fnOff
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
      num% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") =
      CryptoVerification.libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt_ext,
    ls_stub% "__rustc::__rust_dealloc"]

noncomputable def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_ext
    (b : BitVec 64) (ext : String → Option (State → State)) : BitVec 64 :=
  (tripleRatchetProgAtExt b ext).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq_ext
    (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName =
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_ext b ext := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_ext
  rfl

attribute [local irreducible]
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_ext

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.tryDecrypt_add_spqrRecv_eq_fnAddr
    (b : BitVec 64) (H : String → Option (State → State)) :
    (CryptoVerification.libsignalSessionCode.rebase b H).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
      bv% ((2^64 + ls_off% "spqr::recv" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64) =
      (CryptoVerification.libsignalSessionCode.rebase b H).fnAddr spqrRecvName + BitVec.ofNat 64 0 := by
  change (b + BitVec.ofNat 64 (CryptoVerification.libsignalSessionCode.fnOff
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)) +
    bv% ((2^64 + ls_off% "spqr::recv" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64) =
    (b + BitVec.ofNat 64 (CryptoVerification.libsignalSessionCode.fnOff spqrRecvName)) + BitVec.ofNat 64 0
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt_ext, fnOff_spqrRecv]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.tryDecrypt_add_addrDisplay_eq_fnAddr
    (b : BitVec 64) (H : String → Option (State → State)) :
    (CryptoVerification.libsignalSessionCode.rebase b H).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
      bv% ((2^64 + ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64) =
      (CryptoVerification.libsignalSessionCode.rebase b H).fnAddr addrDisplayName + BitVec.ofNat 64 0 := by
  change (b + BitVec.ofNat 64 (CryptoVerification.libsignalSessionCode.fnOff
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)) +
    bv% ((2^64 + ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64) =
    (b + BitVec.ofNat 64 (CryptoVerification.libsignalSessionCode.fnOff addrDisplayName)) + BitVec.ofNat 64 0
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt_ext, fnOff_addrDisplay]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fetch_tryDecrypt_at_ext
    {b : BitVec 64} {ext : String → Option (State → State)} {entry : BitVec 64}
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_ext b ext = entry)
    {k off_k : Nat} {inst : Instr}
    (hadd : (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") + k = off_k)
    (htext : Nat.ble off_k (num% (ls_field% textEnd - 1)) = true)
    (h : CryptoVerification.libsignalSessionCode_tree.fetchDecodeAt off_k = some inst) :
    (tripleRatchetProgAtExt b ext).fetch (entry + BitVec.ofNat 64 k) = some inst := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq_ext]
  subst hadd
  have hlt : (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") + k <
      num% (ls_field% textEnd) :=
    Nat.lt_succ_of_le (Nat.le_of_ble_eq_true htext)
  exact CryptoVerification.libsignalSessionCode_fetch_fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt_ext
    hlt h (lt_two_pow_64_of_lt_text hlt)

open Lean Elab Tactic in
elab "decrypt_fetches_at_cli_ext " hentry:ident k0:num len:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let off := num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  let k0 := k0.getNat
  let len := len.getNat
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let off_k := off + k
    let hex := String.ofList (Nat.toDigits 16 off_k)
    let cand := (`CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli).appendAfter s!"_decode_0x{hex}"
    let decName :=
      if (Lean.ResolveName.resolveGlobalName portEnv portOpts portNs portOd cand).any (fun r => r.2.isEmpty) then
        cand
      else
        (`CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin).appendAfter s!"_decode_0x{hex}"
    let dec := mkIdent decName
    let kq := Syntax.mkNumLit (toString k)
    let offkq := Syntax.mkNumLit (toString off_k)
    evalTactic (← `(tactic|
      have := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fetch_tryDecrypt_at_ext
        $hentry (k := $kq) (off_k := $offkq) rfl rfl $dec))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.spqrRecv_ok_at_entry_ext
    {Q : List (BitVec 8) → Prop} {A : RustAlloc} {S : SpqrModel}
    {ext : String → Option (State → State)} {img : Obj.Image} {entry : BitVec 64}
    (hrecv : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
      ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes)))
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (entry + bv% ((2^64 + ls_off% "spqr::recv" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))
      ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes)) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq_ext]
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.tryDecrypt_add_spqrRecv_eq_fnAddr]
  exact sub_ok_at_of_fnAddr hrecv spqrRecvName 0 (Nat.add_zero _)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.spqrRecv_ok_at_entryQF_ext
    {Q : List (BitVec 8) → Prop} {Pstk : Nat → Prop} {F : SepProp}
    {A : RustAlloc} {S : SpqrModel}
    {ext : String → Option (State → State)} {img : Obj.Image} {entry : BitVec 64}
    (hrecv : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
      (spqrRecvSpecQF Q Pstk F A S img))
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (entry + bv% ((2^64 + ls_off% "spqr::recv" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))
      (spqrRecvSpecQF Q Pstk F A S img) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq_ext]
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.tryDecrypt_add_spqrRecv_eq_fnAddr]
  exact sub_ok_at_of_fnAddr hrecv spqrRecvName 0 (Nat.add_zero _)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.formatInner_ok_at_entry_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (entry + bv% ((2^64 + ls_off% "alloc::fmt::format::format_inner" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))
      ((formatInnerSpec A).inImage img) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq_ext]
  exact hC.format_inner_ok_at
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    (num% (ls_off% "alloc::fmt::format::format_inner" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.hk_formatInner_ext

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.dealloc_ok_at_entry_ext
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (halloc : AllocContractsX img A ext)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq_ext]
  exact halloc.dealloc_ok_at
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.hk_dealloc_ext

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.addrDisplay_ok_at_entry_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (entry + bv% ((2^64 + ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))
      ((addrDisplaySpec A).inImage img) := by
  rw [← hentry, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq_ext]
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.tryDecrypt_add_addrDisplay_eq_fnAddr]
  exact addr_display_ok_at_ext_x img C A ext hC addrDisplayName 0 (Nat.add_zero _)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.cmk_ok_at_entry_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)} {entry : BitVec 64}
    (hcmk : CmkOkX img C A ext)
    (heq : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_ext img.base ext = entry) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (entry + bv% ((2^64 + ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64))
      (cmkSpecX C.F A img) := by
  have hfn :
      (tripleRatchetProgAtExt img.base ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        bv% ((2^64 + ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64) =
      (tripleRatchetProgAtExt img.base ext).fnAddr
          "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt_ext,
      (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"),
      BitVec.add_assoc]
    rfl
  rw [← heq, ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq_ext, hfn]
  exact hcmk

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.entry_eq_base_ext
    {b : BitVec 64} {ext : String → Option (State → State)} {entry : BitVec 64}
    (hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_ext b ext = entry) :
    entry = b + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") := by
  rw [← hentry,
    ← CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnAddr_tryDecrypt_eq_ext,
    Program.fnAddr_rebase,
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.BS8.fnOff_tryDecrypt_ext]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.onPanic_drop_frame_ext
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {F R : SepProp} {s0 s' : State}
    (h : s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ (F ∗ R)) :
    s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  rcases h with ⟨hcond, hmem⟩
  rw [← sepConj_assoc] at hmem
  exact ⟨hcond, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmem⟩

set_option maxRecDepth 2000000 in
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.rodata_decryptStr_eq_ext :
    (libsignalSessionImage.data.drop
      (num% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2452)
        (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2456)) -
        num% (ls_xref% 0x2440 0x2444))).take 7 =
      utf8 "decrypt" := by
  rfl_kernel

set_option maxRecDepth 2000000 in
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.rodata_decrypt_intro_ext
    {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref%
      (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2452)
      (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2456))) ↦ᵣ utf8 "decrypt") ∗ P := by
  have hdlen : num% (ls_xref%
      (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2452)
      (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2456)) -
      num% (ls_xref% 0x2440 0x2444) + 7 ≤
      libsignalSessionImage.data.length := by
    have h1 := congrArg List.length
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.rodata_decryptStr_eq_ext
    rw [List.length_take, List.length_drop, utf8_decrypt_len] at h1
    omega
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (secOff := num% (ls_xref%
      (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2452)
      (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2456)))
    (secLen := 7)
    (dataOff := num% (ls_xref% 0x2440 0x2444))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    hdlen (by rfl_kernel) hro hP
  rwa [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.rodata_decryptStr_eq_ext] at h

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.adrp_decryptStr_ext
    {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (he : entry = b + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) :
    (((entry + 2452#64) &&& 18446744073709547520#64) +
      bv% (page% (ls_xref%
        (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2452)
        (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2456)) -
        page% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2452))) +
      bv% ((ls_xref%
        (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2452)
        (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2456)) % 4096) =
      b + bv% (ls_xref%
        (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2452)
        (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" + 2456)) := by
  rw [he, BitVec.add_assoc b, ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc b,
      BitVec.add_assoc b]
  rfl

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.onPanic_of_formatInner_ext
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (h : sf.mem ⊨ (((formatInnerSpec A).inImage img).onPanic ret sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 sf ∗ R := by
  dsimp only [formatInnerSpec, CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨⟨hpan, hpref⟩, hmem⟩
  rw [← sepConj_assoc] at hmem
  rw [allocFailedIn, htrace, ← allocFailedIn] at hpan
  rw [htrace] at hpref
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨Or.inr (Or.inr hpan), hpref⟩, ?_⟩
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmem

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.onPanic_of_spqrRecv_ext
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {st msg : VecArg} {ret : BitVec 64}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (hst : st.bytes = x.st.pqRatchetState)
    (hmsg : msg.bytes = x.msg.pqRatchet)
    (h : sf.mem ⊨ ((spqrRecvSpec A S img).onPanic (st, msg, ret) sm sf ∗ F) ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 sf ∗ R := by
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
  · exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmem

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.msg_pqRatchet_lt_of_commonHeap_ext
    {A : RustAlloc} {ctl : BitVec 64} {img : Obj.Image}
    {x : TryDecryptGhost} {draws : Nat} {s0 : State} {m : Memory} {P Q : SepProp}
    (h : m ⊨ P ∗ CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ Q) :
    x.msg.pqRatchet.length < 2 ^ 40 := by
  rw [sepConj_left_comm] at h
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap signalMessageAt at h
  simp only [sepConj_assoc] at h
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, satisfies_pure_sepConj] at h
  exact h.1.2.2.2.1

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegMidBase
