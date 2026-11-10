/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityVtables
public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Session
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.RoDataReloc

/-!
# `SessionFiles` Vtables

Establishes `MessageDecrypt.SessionOnlyVtablesOk` for any `SessionStoreSpec` with CLI
`SessionFiles` offsets (`CliSessKitOffsets`), reading `.data.rel.ro` relocations for
`dyn SessionStore` (`+0x18` `load_session`, `+0x20` `store_session`) and the 24-byte and
32-byte boxed futures sharing the no-op `cliIdFutDropName` drop glue.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Offsets -/

/-- `dyn SessionStore` vtable offset for `SessionFiles`, keyed via `load_session` (`+0x18`). -/
abbrev cliSessVtOff : BitVec 64 :=
  bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session") - 24)

/-- Code offset of `<SessionFiles as SessionStore>::load_session`. -/
abbrev cliSessLoadShimOff : BitVec 64 := bv% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session")

/-- Code offset of `<SessionFiles as SessionStore>::store_session`. -/
abbrev cliSessStoreShimOff : BitVec 64 := bv% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session")

/-- Code offset of `<SessionFiles as SessionStore>::load_session::{closure#0}`. -/
abbrev cliSessLoadPollOff : BitVec 64 := bv% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}")

/-- Code offset of `<SessionFiles as SessionStore>::store_session::{closure#0}`. -/
abbrev cliSessStorePollOff : BitVec 64 := bv% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}")

/-- Future vtable offset for `load_session::{closure#0}`, keyed via its `+0x18` poll slot. -/
abbrev cliSessLoadFutVtOff : BitVec 64 :=
  bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 24)

/-- Future vtable offset for `store_session::{closure#0}`, keyed via its `+0x18` poll slot. -/
abbrev cliSessStoreFutVtOff : BitVec 64 :=
  bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") - 24)

theorem cliSessLoadFutVtOff_eq : sessLoadFutVtOff = cliSessLoadFutVtOff := by rfl

theorem cliSessStoreFutVtOff_eq : sessStoreFutVtOff = cliSessStoreFutVtOff := by rfl

/-- A `SessionStoreSpec` at `img.base` whose session vtable, shim, poll and drop offsets and box
sizes are the CLI's. -/
structure CliSessKitOffsets {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) : Prop where
  ssVt : kit.ss_vt = img.base + cliSessVtOff
  loadShim : kit.loadShimOff = cliSessLoadShimOff
  storeShim : kit.storeShimOff = cliSessStoreShimOff
  loadFutVt : kit.loadFutVtOff = cliSessLoadFutVtOff
  storeFutVt : kit.storeFutVtOff = cliSessStoreFutVtOff
  loadPoll : kit.loadPollOff = cliSessLoadPollOff
  storePoll : kit.storePollOff = cliSessStorePollOff
  loadFutDrop : kit.loadFutDropOff = cliIdFutDropOff
  storeFutDrop : kit.storeFutDropOff = cliIdFutDropOff
  loadBoxSize : kit.loadBoxSize = 24
  storeBoxSize : kit.storeBoxSize = 32

/-! ## `.data.rel.ro` box size and alignment words -/

set_option maxRecDepth 2000000 in
theorem rodata_cliSessLoadFutSize_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 16) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 24#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
theorem rodata_cliSessLoadFutAlign_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 8) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 8#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
theorem rodata_cliSessStoreFutSize_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") - 16) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 32#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
theorem rodata_cliSessStoreFutAlign_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") - 8) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 8#64 := by rfl_kernel

/-! ## Vtable validity -/

/-- Every `SessionStoreSpec` satisfying `CliSessKitOffsets` satisfies `SessionOnlyVtablesOk`. -/
theorem cliSessionOnlyVtablesOk {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base}
    (himg : Obj.Loads libsignalSessionImage img) (h : CliSessKitOffsets img kit) :
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.SessionOnlyVtablesOk img kit where
  loadSlot hF hP := by
    rw [h.ssVt, h.loadShim]
    dsimp only [cliSessVtOff, cliSessLoadShimOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session") - 24) + 0x18#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session")) by bv_omega]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session"))) (target := num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP
  storeSlot hF hP := by
    rw [h.ssVt, h.storeShim]
    dsimp only [cliSessVtOff, cliSessStoreShimOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session") - 24) + 0x20#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session") + 8) by bv_omega]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session") + 8)) (target := num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP
  loadFutDrop hF hP := by
    rw [h.loadFutVt, h.loadFutDrop]
    dsimp only [cliSessLoadFutVtOff, cliIdFutDropOff]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 24)) (target := num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP
  loadFutSize hF hP := by
    rw [h.loadFutVt, h.loadBoxSize]
    dsimp only [cliSessLoadFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 24) + 8#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 16) by bv_omega]
    have hh := loads_rodata_holdsBytes himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 16)) (n := 8) (bs := unpack64 24#64)
      (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
      (unpack64_length _) rodata_cliSessLoadFutSize_eq
    obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
    rw [unpack64_length] at hRO hread
    exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP
  loadFutAlign hF hP := by
    rw [h.loadFutVt]
    dsimp only [cliSessLoadFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 24) + 0x10#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 8) by bv_omega]
    have hh := loads_rodata_holdsBytes himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 8)) (n := 8) (bs := unpack64 8#64)
      (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
      (unpack64_length _) rodata_cliSessLoadFutAlign_eq
    obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
    rw [unpack64_length] at hRO hread
    exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP
  loadFutPoll hF hP := by
    rw [h.loadFutVt, h.loadPoll]
    dsimp only [cliSessLoadFutVtOff, cliSessLoadPollOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 24) + 0x18#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}")) by bv_omega]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"))) (target := num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP
  storeFutDrop hF hP := by
    rw [h.storeFutVt, h.storeFutDrop]
    dsimp only [cliSessStoreFutVtOff, cliIdFutDropOff]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") - 24)) (target := num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP
  storeFutSize hF hP := by
    rw [h.storeFutVt, h.storeBoxSize]
    dsimp only [cliSessStoreFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") - 24) + 8#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") - 16) by bv_omega]
    have hh := loads_rodata_holdsBytes himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") - 16)) (n := 8) (bs := unpack64 32#64)
      (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
      (unpack64_length _) rodata_cliSessStoreFutSize_eq
    obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
    rw [unpack64_length] at hRO hread
    exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP
  storeFutAlign hF hP := by
    rw [h.storeFutVt]
    dsimp only [cliSessStoreFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") - 24) + 0x10#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") - 8) by bv_omega]
    have hh := loads_rodata_holdsBytes himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") - 8)) (n := 8) (bs := unpack64 8#64)
      (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
      (unpack64_length _) rodata_cliSessStoreFutAlign_eq
    obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
    rw [unpack64_length] at hRO hread
    exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP
  storeFutPoll hF hP := by
    rw [h.storeFutVt, h.storePoll]
    dsimp only [cliSessStoreFutVtOff, cliSessStorePollOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") - 24) + 0x18#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}")) by bv_omega]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"))) (target := num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP

end CryptoVerification.SignalSession.Cli.KitInst
