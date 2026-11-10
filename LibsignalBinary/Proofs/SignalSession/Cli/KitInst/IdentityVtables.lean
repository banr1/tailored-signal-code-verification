/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Identity
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.RoDataReloc
import ProofLib.SepLogic.WPp

/-!
# `IdentityFiles` Vtables and Future Drop

Establishes `IdentityVtablesOk` for any `IdentityStoreSpec` with CLI `IdentityFiles` offsets
(`CliIdKitOffsets`), reading `.data.rel.ro` relocations for `dyn IdentityKeyStore` (`+0x28`
`save_identity`, `+0x30` `is_trusted_identity`) and both 32-byte, 8-aligned boxed futures,
together with `futDropSpec` for the shared single-`ret` drop glue `cliIdFutDropName`.
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
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>")

/-! ## Offsets -/

/-- `dyn IdentityKeyStore` vtable offset for `IdentityFiles`, keyed via `save_identity` (`+0x28`). -/
abbrev cliIdVtOff : BitVec 64 :=
  bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") - 0x28)

/-- Code offset of `<IdentityFiles as IdentityKeyStore>::save_identity`. -/
abbrev cliIdSaveShimOff : BitVec 64 :=
  bv% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity")

/-- Code offset of `<IdentityFiles as IdentityKeyStore>::is_trusted_identity`. -/
abbrev cliIdTrustShimOff : BitVec 64 :=
  bv% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity")

/-- Code offset of `<IdentityFiles as IdentityKeyStore>::save_identity::{closure#0}`. -/
abbrev cliIdSavePollOff : BitVec 64 :=
  bv% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")

/-- Code offset of `<IdentityFiles as IdentityKeyStore>::is_trusted_identity::{closure#0}`. -/
abbrev cliIdTrustPollOff : BitVec 64 :=
  bv% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}")

/-- Future vtable offset for `save_identity::{closure#0}`, keyed via its `+0x18` poll slot. -/
abbrev cliIdSaveFutVtOff : BitVec 64 :=
  bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") - 0x18)

/-- Future vtable offset for `is_trusted_identity::{closure#0}`, keyed via its `+0x18` poll slot. -/
abbrev cliIdTrustFutVtOff : BitVec 64 :=
  bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") - 0x18)

/-- ICF-shared no-op `drop_glue` symbol (a single `ret`) for CLI store futures. -/
abbrev cliIdFutDropName : String :=
  "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"

abbrev cliIdFutDropOff : BitVec 64 :=
  bv% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>")

theorem cliIdFutDrop_fnOff :
    libsignalSessionCode.fnOff cliIdFutDropName =
      num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>")

theorem cliIdSaveFutVtOff_eq : idSaveFutVtOff = cliIdSaveFutVtOff := by rfl

theorem cliIdTrustFutVtOff_eq : idTrustFutVtOff = cliIdTrustFutVtOff := by rfl

/-- Predicate asserting that an `IdentityStoreSpec` at `img.base` has the CLI `IdentityFiles`
vtable, shim, poll, drop, and box-size parameters. -/
structure CliIdKitOffsets {A : RustAlloc} (img : Obj.Image)
    (ikit : IdentityStoreSpec A img.base) : Prop where
  idVt : ikit.id_vt = img.base + cliIdVtOff
  saveShim : ikit.saveShimOff = cliIdSaveShimOff
  trustShim : ikit.trustShimOff = cliIdTrustShimOff
  saveFutVt : ikit.saveFutVtOff = cliIdSaveFutVtOff
  trustFutVt : ikit.trustFutVtOff = cliIdTrustFutVtOff
  savePoll : ikit.savePollOff = cliIdSavePollOff
  trustPoll : ikit.trustPollOff = cliIdTrustPollOff
  saveFutDrop : ikit.saveFutDropOff = cliIdFutDropOff
  trustFutDrop : ikit.trustFutDropOff = cliIdFutDropOff
  saveBoxSize : ikit.saveBoxSize = 32
  trustBoxSize : ikit.trustBoxSize = 32

/-! ## `.data.rel.ro` box size and alignment words -/

set_option maxRecDepth 2000000 in
theorem rodata_cliIdSaveFutSize_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") - 16) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 32#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
theorem rodata_cliIdSaveFutAlign_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") - 8) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 8#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
theorem rodata_cliIdTrustFutSize_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") - 16) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 32#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
theorem rodata_cliIdTrustFutAlign_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") - 8) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 8#64 := by rfl_kernel

/-! ## Vtable validity -/

/-- Every `IdentityStoreSpec` satisfying `CliIdKitOffsets` satisfies `IdentityVtablesOk`. -/
theorem cliIdentityVtablesOk {A : RustAlloc} {img : Obj.Image}
    {ikit : IdentityStoreSpec A img.base}
    (himg : Obj.Loads libsignalSessionImage img) (h : CliIdKitOffsets img ikit) :
    IdentityVtablesOk img ikit where
  saveSlot hF hP := by
    rw [h.idVt, h.saveShim]
    dsimp only [cliIdVtOff, cliIdSaveShimOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") - 0x28) + 0x28#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity")) by bv_omega]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity"))) (target := num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP
  trustSlot hF hP := by
    rw [h.idVt, h.trustShim]
    dsimp only [cliIdVtOff, cliIdTrustShimOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") - 0x28) + 0x30#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") + 8) by bv_omega]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") + 8)) (target := num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP
  saveFutDrop hF hP := by
    rw [h.saveFutVt, h.saveFutDrop]
    dsimp only [cliIdSaveFutVtOff, cliIdFutDropOff]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") - 0x18)) (target := num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP
  saveFutSize hF hP := by
    rw [h.saveFutVt, h.saveBoxSize]
    dsimp only [cliIdSaveFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") - 0x18) + 8#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") - 16) by bv_omega]
    have hh := loads_rodata_holdsBytes himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") - 16)) (n := 8) (bs := unpack64 32#64)
      (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
      (unpack64_length _) rodata_cliIdSaveFutSize_eq
    obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
    rw [unpack64_length] at hRO hread
    exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP
  saveFutAlign hF hP := by
    rw [h.saveFutVt]
    dsimp only [cliIdSaveFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") - 0x18) + 0x10#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") - 8) by bv_omega]
    have hh := loads_rodata_holdsBytes himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") - 8)) (n := 8) (bs := unpack64 8#64)
      (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
      (unpack64_length _) rodata_cliIdSaveFutAlign_eq
    obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
    rw [unpack64_length] at hRO hread
    exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP
  saveFutPoll hF hP := by
    rw [h.saveFutVt, h.savePoll]
    dsimp only [cliIdSaveFutVtOff, cliIdSavePollOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") - 0x18) + 0x18#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")) by bv_omega]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) (target := num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP
  trustFutDrop hF hP := by
    rw [h.trustFutVt, h.trustFutDrop]
    dsimp only [cliIdTrustFutVtOff, cliIdFutDropOff]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") - 0x18)) (target := num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP
  trustFutSize hF hP := by
    rw [h.trustFutVt, h.trustBoxSize]
    dsimp only [cliIdTrustFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") - 0x18) + 8#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") - 16) by bv_omega]
    have hh := loads_rodata_holdsBytes himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") - 16)) (n := 8) (bs := unpack64 32#64)
      (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
      (unpack64_length _) rodata_cliIdTrustFutSize_eq
    obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
    rw [unpack64_length] at hRO hread
    exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP
  trustFutAlign hF hP := by
    rw [h.trustFutVt]
    dsimp only [cliIdTrustFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") - 0x18) + 0x10#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") - 8) by bv_omega]
    have hh := loads_rodata_holdsBytes himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") - 8)) (n := 8) (bs := unpack64 8#64)
      (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
      (unpack64_length _) rodata_cliIdTrustFutAlign_eq
    obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
    rw [unpack64_length] at hRO hread
    exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP
  trustFutPoll hF hP := by
    rw [h.trustFutVt, h.trustPoll]
    dsimp only [cliIdTrustFutVtOff, cliIdTrustPollOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") - 0x18) + 0x18#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}")) by bv_omega]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"))) (target := num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP

/-! ## Future drop -/

gen_decodes CryptoVerification.libsignalSessionCode_tree cliIdFutDropBin
  [(ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>") →
   (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>" + 4)]

set_option maxHeartbeats 1600000 in
/-- `cliIdFutDropName` (a single `ret`) satisfies `futDropSpec` at its `fnAddr`. -/
theorem cliIdFutDrop_fnAddr_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr cliIdFutDropName) futDropSpec := by
  simp only [futDropSpec]
  have hfn : libsignalSessionCode.fnOff cliIdFutDropName = num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>") :=
    cliIdFutDrop_fnOff
  code_fetches CryptoVerification.libsignalSessionCode cliIdFutDropBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>")) 4
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- `cliIdFutDropOff` satisfies `futDropSpec` on `tripleRatchetProgAt`. -/
theorem cliIdFutDrop_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + cliIdFutDropOff) futDropSpec := by
  have h := cliIdFutDrop_fnAddr_ok (b := b) (C := C) (ctl := ctl) (abs := abs)
  have hfn : libsignalSessionCode.fnOff cliIdFutDropName = num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>") :=
    cliIdFutDrop_fnOff
  rwa [show (tripleRatchetProgAt b C ctl abs).fnAddr cliIdFutDropName = b + cliIdFutDropOff by
    simp only [tripleRatchetProgAt, Program.fnAddr_rebase, hfn, cliIdFutDropOff]] at h

end CryptoVerification.SignalSession.Cli.KitInst
