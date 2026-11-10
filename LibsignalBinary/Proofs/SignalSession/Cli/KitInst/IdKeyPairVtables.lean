/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees
import LibsignalBinary.Proofs.RoDataReloc

/-!
# `IdentityFiles::get_identity_key_pair` Vtable Slots

`.data.rel.ro` vtable layout and entry-address rewrites for
`<IdentityFiles as IdentityKeyStore>::get_identity_key_pair` and its boxed `Future`
closure (16-byte, 8-aligned box sharing the ICF-merged no-op `cliIdFutDropOff` drop glue),
matching the key-pair fields of `IdentitySelfVtablesOk`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

set_option maxRecDepth 200000

/-! ## Offsets -/

/-- Code offset of `<IdentityFiles as IdentityKeyStore>::get_identity_key_pair`. -/
abbrev cliIdKpShimOff : BitVec 64 :=
  bv% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair")

/-- Code offset of `<IdentityFiles as IdentityKeyStore>::get_identity_key_pair::{closure#0}`. -/
abbrev cliIdKpPollOff : BitVec 64 :=
  bv% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}")

/-! ## `.data.rel.ro` words (size, align) -/

set_option maxRecDepth 2000000 in
theorem rodata_cliIdKpFutSize_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 16) -
        libsignalSessionImage.dataOff)).take 8 =
      unpack64 16#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
theorem rodata_cliIdKpFutAlign_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 8) -
        libsignalSessionImage.dataOff)).take 8 =
      unpack64 8#64 := by rfl_kernel

/-! ## Vtable slot lemmas -/

/-- Trait vtable slot `cliIdVtOff + 0x18` relocates to `get_identity_key_pair` (`cliIdKpShimOff`). -/
theorem cliIdKpSlot_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + cliIdVtOff + 0x18#64) ↦₆₄ᵣ (img.base + cliIdKpShimOff)) ∗ P := by
  dsimp only [cliIdVtOff, cliIdKpShimOff]
  rw [show img.base +
      bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") - 0x28) +
      0x18#64 =
      img.base +
      bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") - 0x10) by
    bv_omega]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") - 0x10))
    (target := num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hP

/-- Future vtable slot `idKeyPairFutVtOff + 0x00` relocates to `cliIdFutDropOff` (`cliIdFutDropName`). -/
theorem cliIdKpFutDrop_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + idKeyPairFutVtOff) ↦₆₄ᵣ (img.base + cliIdFutDropOff)) ∗ P := by
  dsimp only [idKeyPairFutVtOff, cliIdFutDropOff]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 0x18))
    (target := num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hP

/-- Future vtable slot `idKeyPairFutVtOff + 0x08` holds `16#64`. -/
theorem cliIdKpFutSize_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + idKeyPairFutVtOff + 8#64) ↦₆₄ᵣ 16#64) ∗ P := by
  dsimp only [idKeyPairFutVtOff]
  rw [show img.base +
      bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 0x18) +
      8#64 =
      img.base +
      bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 16) by
    bv_omega]
  have hh := loads_rodata_holdsBytes himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 16))
    (n := 8) (bs := unpack64 16#64)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
    (unpack64_length _) rodata_cliIdKpFutSize_eq
  obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
  rw [unpack64_length] at hRO hread
  exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP

/-- Future vtable slot `idKeyPairFutVtOff + 0x10` holds `8#64`. -/
theorem cliIdKpFutAlign_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + idKeyPairFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P := by
  dsimp only [idKeyPairFutVtOff]
  rw [show img.base +
      bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 0x18) +
      0x10#64 =
      img.base +
      bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 8) by
    bv_omega]
  have hh := loads_rodata_holdsBytes himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 8))
    (n := 8) (bs := unpack64 8#64)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
    (unpack64_length _) rodata_cliIdKpFutAlign_eq
  obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
  rw [unpack64_length] at hRO hread
  exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP

/-- Future vtable slot `idKeyPairFutVtOff + 0x18` relocates to `get_identity_key_pair::{closure#0}`
(`cliIdKpPollOff`). -/
theorem cliIdKpFutPoll_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + idKeyPairFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + cliIdKpPollOff)) ∗ P := by
  dsimp only [idKeyPairFutVtOff, cliIdKpPollOff]
  rw [show img.base +
      bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 0x18) +
      0x18#64 =
      img.base +
      bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}")) by
    bv_omega]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}")))
    (target := num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hP

/-! ## Entry-address equalities -/

theorem cliIdKpShimOff_eq {b : BitVec 64} {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr idKeyPairShimName = b + cliIdKpShimOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, idKeyPairShim_fnOff, cliIdKpShimOff]

theorem cliIdKpPollOff_eq {b : BitVec 64} {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr idKeyPairPollName = b + cliIdKpPollOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, idKeyPairPoll_fnOff, cliIdKpPollOff]

end CryptoVerification.SignalSession.Cli.KitInst
