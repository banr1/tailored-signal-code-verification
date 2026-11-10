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
# `IdentityFiles::get_local_registration_id` Vtable Slots

`.data.rel.ro` vtable layout and entry-address rewrites for
`<IdentityFiles as IdentityKeyStore>::get_local_registration_id` and its boxed `Future`
closure (16-byte, 8-aligned box sharing the ICF-merged no-op `cliIdFutDropOff` drop glue),
matching the registration-ID fields of `IdentitySelfVtablesOk`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

/-- Code offset of `<IdentityFiles as IdentityKeyStore>::get_local_registration_id`. -/
abbrev cliIdRegIdShimOff : BitVec 64 :=
  bv% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id")

/-- Code offset of `<IdentityFiles as IdentityKeyStore>::get_local_registration_id::{closure#0}`. -/
abbrev cliIdRegIdPollOff : BitVec 64 :=
  bv% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}")

set_option maxRecDepth 2000000 in
theorem rodata_cliIdRegIdFutSize_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") - 16) -
        libsignalSessionImage.dataOff)).take 8 =
      unpack64 16#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
theorem rodata_cliIdRegIdFutAlign_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") - 8) -
        libsignalSessionImage.dataOff)).take 8 =
      unpack64 8#64 := by rfl_kernel

/-- Slot `+0x20` of `IdentityFiles`' `IdentityKeyStore` vtable points to `cliIdRegIdShimOff`. -/
theorem cliIdRegIdSlot_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + cliIdVtOff + 0x20#64) ↦₆₄ᵣ (img.base + cliIdRegIdShimOff)) ∗ P := by
  dsimp only [cliIdVtOff, cliIdRegIdShimOff]
  rw [show img.base +
      bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") - 0x28) +
      0x20#64 =
      img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"))
      by bv_omega]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id")))
    (target := num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hP

/-- Slot `+0x00` of the `get_local_registration_id` future vtable points to `cliIdFutDropOff`. -/
theorem cliIdRegIdFutDrop_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + idRegIdFutVtOff) ↦₆₄ᵣ (img.base + cliIdFutDropOff)) ∗ P := by
  dsimp only [idRegIdFutVtOff, cliIdFutDropOff]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") - 0x18))
    (target := num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hP

/-- Slot `+0x08` of the `get_local_registration_id` future vtable holds `16#64`. -/
theorem cliIdRegIdFutSize_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + idRegIdFutVtOff + 8#64) ↦₆₄ᵣ 16#64) ∗ P := by
  dsimp only [idRegIdFutVtOff]
  rw [show img.base +
      bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") - 0x18) +
      8#64 =
      img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") - 16)
      by bv_omega]
  have hh := loads_rodata_holdsBytes himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") - 16))
    (n := 8) (bs := unpack64 16#64)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
    (unpack64_length _) rodata_cliIdRegIdFutSize_eq
  obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
  rw [unpack64_length] at hRO hread
  exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP

/-- Slot `+0x10` of the `get_local_registration_id` future vtable holds `8#64`. -/
theorem cliIdRegIdFutAlign_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + idRegIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P := by
  dsimp only [idRegIdFutVtOff]
  rw [show img.base +
      bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") - 0x18) +
      0x10#64 =
      img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") - 8)
      by bv_omega]
  have hh := loads_rodata_holdsBytes himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") - 8))
    (n := 8) (bs := unpack64 8#64)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
    (unpack64_length _) rodata_cliIdRegIdFutAlign_eq
  obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
  rw [unpack64_length] at hRO hread
  exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP

/-- Slot `+0x18` of the `get_local_registration_id` future vtable points to `cliIdRegIdPollOff`. -/
theorem cliIdRegIdFutPoll_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + idRegIdFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + cliIdRegIdPollOff)) ∗ P := by
  dsimp only [idRegIdFutVtOff, cliIdRegIdPollOff]
  rw [show img.base +
      bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") - 0x18) +
      0x18#64 =
      img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"))
      by bv_omega]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}")))
    (target := num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hP

theorem cliIdRegIdShimOff_eq {b : BitVec 64} {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr idRegIdShimName = b + cliIdRegIdShimOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, idRegIdShim_fnOff, cliIdRegIdShimOff]

theorem cliIdRegIdPollOff_eq {b : BitVec 64} {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr idRegIdPollName = b + cliIdRegIdPollOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, idRegIdPoll_fnOff, cliIdRegIdPollOff]

end CryptoVerification.SignalSession.Cli.KitInst
