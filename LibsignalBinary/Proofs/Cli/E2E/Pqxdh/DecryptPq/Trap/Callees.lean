/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
public import LibsignalBinary.Proofs.TripleRatchet.Statements
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.ChainKeyToPb
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExt
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Ext
import LibsignalBinary.Proofs.TripleRatchet.Getters.Identity
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeys
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Main

/-!
# Trap-at-RNG Callee Contracts for Handshake `try_decrypt_with_state::<Coins>`

Discharges the 16 fields of `TryDecryptCallees_trap` on `trTrapProgAt img.base C abs` from
`TripleRatchetHooks C A S abs` and `Obj.Loads libsignalSessionImage img`.
-/

@[expose] public section

set_option autoImplicit false

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

namespace CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPqAssembly

theorem sessionExterns_le_trTrap (C : Crypto) (abs : String → Option (State → State)) :
    ∀ n f,
      Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns C.F abs) n = some f →
      Rust.withPanics (trTrapExterns C abs) n = some f := by
  apply ConsumeMessageKeyTransfer.withPanics_mono
  intro n f h
  by_cases hr : n = rngFillName
  · subst hr
    have hn : ¬(rngFillName = "__rustc::__rust_alloc" ∨ rngFillName = "__rustc::__rust_dealloc" ∨
        rngFillName = "__rustc::__rust_realloc") := by decide
    have e := ConsumeMessageKeyTransfer.sessionExterns_not_alloc
      (F := C.F) (a1 := abs) (a2 := fun _ => none) hn
    have hnone : CryptoVerification.LibsignalSession.sessionExterns C.F (fun _ => none) rngFillName = none := rfl
    rw [e, hnone] at h
    nomatch h
  · rw [trTrapExterns_eq_tripleRatchetExterns C 0#64 abs hr]
    by_cases hn : n = "__rustc::__rust_alloc" ∨ n = "__rustc::__rust_dealloc" ∨
        n = "__rustc::__rust_realloc"
    · have h1 := ConsumeMessageKeyTransfer.sessionExterns_alloc C.F abs
      have h2 := ConsumeMessageKeyTransfer.tripleRatchetExterns_alloc C 0#64 abs
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at h1 h2
      rcases hn with rfl | rfl | rfl
      · rw [h1.1] at h; rw [h2.1]; exact h
      · rw [h1.2.1] at h; rw [h2.2.1]; exact h
      · rw [h1.2.2.1] at h; rw [h2.2.2.1]; exact h
    · have e := ConsumeMessageKeyTransfer.sessionExterns_not_alloc
        (F := C.F) (a1 := abs) (a2 := fun _ => none) hn
      unfold tripleRatchetExterns
      rw [← e, h]

theorem withPanics_trTrap_blackBox (C : Crypto) (abs : String → Option (State → State)) :
    Rust.withPanics (trTrapExterns C abs) "subtle::black_box::<u8>" =
      some CryptoVerification.LibsignalSession.blackBoxHook :=
  (withPanics_trTrap_ne C abs (by decide)).trans
    (ConsumeMessageKeyTransfer.tripleRatchetProgAt_blackBox C 0#64 abs)

theorem tryDecryptPqCallees_trap (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hH : TripleRatchetHooks C A S abs) (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees_trap
      img C A uuidTryParse abs := by
  let ext := trTrapExterns C abs
  have hS2 : Stage2Contracts_trap img.base C A uuidTryParse S ext :=
    Stage2Contracts_trap.of_tripleRatchetProgAt_trap img.base C A S abs hH
  have hA : AllocContracts img.base A ext := hS2.toAllocContracts
  have hle := sessionExterns_le_trTrap C abs
  have h_bb := withPanics_trTrap_blackBox C abs
  have : HkdfHooks C.F ext := HkdfHooks.of_le_sessionExterns hle
  have hnew := ConsumeMessageKeyTransfer.new_from_slice_ok_ext img C.F himg hle
  refine
    { localIk := Getters.local_identity_key_ok_ext img A ext (pkTryFrom_ok_ext img ext himg)
      remoteIk := Glue.remoteIdentityKeyOk_ext img A ext himg
      sameAcc := Glue.is_same_account_ok_ext img.base h_bb
      clearUpk := Getters.clear_unacknowledged_pre_key_message_ok_ext img.base A ext hA
      dropChain := CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain2_ok_trap hH.alloc
      chainKeyToPb := chain_key_to_pb_ok_ext hA
      derivePk := derive_public_key_bytes_ok_of_contract
        (subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
          hS2.pub_from_secret.mono_outcome (x.secret, x.sec, x.out) R s0 hpc hrun hpre hsp
            fun _ hout => hout)
      trFrom := ReceiveRatchetFrom.trFrom_ok_ext himg hA (Glue.deserializeOk_ext img.base ext)
        (Glue.remoteIdentityKeyOk_ext img A ext himg) (Glue.dropSpeOk_ext himg hA)
        (Getters.drop_vec_chain_ok_ext hA)
      trApply := ReceiveRatchetApply.trApply_ok_ext hA (Glue.publicKeySerializeOk_ext hA)
        (Getters.drop_vec_message_key_ok_ext hA) (Getters.drop_vec_chain_ok_ext hA)
      findReceiverChainKey := Glue.findReceiverChainKeyOk_ext hle himg
      createChain := Keys.createChain_ok_of_contracts himg
        (Keys.calculateAgreement_ok_of_contracts himg hS2.dh hS2.shared_drop
          (ConsumeMessageKeyTransfer.ctEqRO_ok_ext img.base h_bb) hA.shim hA.alloc hS2.static_drop)
        (extract_ok_ext img C ext hnew)
        (expand_multi_info_ok_ext img.base C ext)
        (hA.dealloc_ok_at createChainName
          (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain"))
          (by rw [(ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::RootKey>::create_chain"),
                (ls_stub% "__rustc::__rust_dealloc")]))
      genKeys := Keys.generateKeys_ok_ext himg (extract_ok_ext img C ext hnew)
        (expand_multi_info_ok_ext img.base C ext) hA
      pkSer := Glue.publicKeySerializeOk_ext hA
      verifyMac := verifyMacWithAddresses_subroutine_ok_of_contracts img himg C A ext hA
        hS2.compress256 hS2.black_box hS2.uuid_try_parse hnew (Glue.publicKeySerializeOk_ext hA)
      cmk := ConsumeMessageKeyTransfer.cmk_ok_ext himg hH.alloc hle
      growOne := ConsumeMessageKeyTransfer.growOneChain_ok_ext himg hH.alloc hle }

/-! ## Stacked 32-bit `CliExt.blackBoxSpec` & `AllocContractsX` Callee Discharges -/

section Ext32Callees

theorem isSameAccount_ok_ext32 (b : BitVec 64) {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>"
      CryptoVerification.SignalSession.CliExt.blackBoxSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr Getters.isSameAccountName)
      Getters.isSameAccountSpecExt :=
  Glue.is_same_account_ok_ext32 b h_bb

theorem publicKeyEq_ok_ext32 (b : BitVec 64) {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>"
      CryptoVerification.SignalSession.CliExt.blackBoxSpec) :
    Getters.PublicKeyEqOkExt32 b ext :=
  Glue.publicKeyEq_ok_ext32 b h_bb

theorem ctEqRO_ok_ext32 (b : BitVec 64) {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>"
      CryptoVerification.SignalSession.CliExt.blackBoxSpec) :
    ConsumeMessageKeyTransfer.CtEqROOkExt32 b ext :=
  ConsumeMessageKeyTransfer.ctEqRO_ok_ext32 b h_bb

theorem findIndex_ok_ext32 {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>"
      CryptoVerification.SignalSession.CliExt.blackBoxSpec) :
    Proofs.libsignal.Stage1X.FindIndexOkX img A ext :=
  ConsumeMessageKeyTransfer.findIndex_ok_ext32 himg h_bb

theorem verifyMacWithAddresses_ok_ext32
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (h_bb : HookSat ext blackBoxName CryptoVerification.SignalSession.CliExt.blackBoxSpec)
    (h_comp : HookSat ext compress256Name (withStack (compress256Spec C.F) extHookStack))
    (hnew : NewFromSliceOkExt img C ext) :
    VerifyMacWithAddressesOkX img C A uuidTryParse ext :=
  CryptoVerification.LibsignalTripleRatchet.Statements.verifyMacWithAddresses_subroutine_ok_ext32
    img himg C A ext hA h_bb h_comp hnew

theorem verifyMacWithAddresses_ok_stacked_ext32
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (h_bb : HookSat ext blackBoxName CryptoVerification.SignalSession.CliExt.blackBoxSpec)
    (h_comp : HookSat ext compress256Name (withStack (compress256Spec C.F) extHookStack))
    (hnew_x : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr newFromSliceName)
      ((newFromSlicePkStackSpecAt C.F
        CryptoVerification.LibsignalTripleRatchet.Statements.computeMacPkStackExt32).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
      ((Mac.VerifyMacWithAddresses.verifyMacWithAddressesSpecWithStack img C.F A uuidTryParse
        CryptoVerification.LibsignalTripleRatchet.Statements.computeMacStackExt32).inImage img) :=
  CryptoVerification.LibsignalTripleRatchet.Statements.verifyMacWithAddresses_subroutine_ok_stacked_ext32
    img himg C A ext hA h_bb h_comp hnew_x

theorem trApply_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    TrApplyOkX img A ext :=
  ReceiveRatchetApply.trApply_ok_x hA
    (Glue.publicKeySerializeOk_ext_x hA)
    (Glue.drop_vec_message_key_ok_ext_x hA)
    (Glue.drop_vec_chain_ok_ext_x hA)

end Ext32Callees

end CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPqAssembly
