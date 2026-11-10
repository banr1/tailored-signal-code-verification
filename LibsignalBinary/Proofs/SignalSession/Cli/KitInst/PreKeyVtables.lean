/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityVtables
public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.PreKey
import LibsignalBinary.Proofs.RoDataReloc
import ProofLib.SepLogic.WPp

/-!
# Pre-Key Store Vtables

`.data.rel.ro` trait-object slot lemmas and `dyn Future` vtable witnesses (`CliFutVtOk`) for
`SignedPreKeyFiles`, `OneTimePreKeyFiles`, and `KyberPreKeyFiles`, keyed via unique shim and
poll relocations and sharing the no-op `cliIdFutDropName` drop glue.
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

/-- A `dyn Future` vtable at `img.base + vt`: drop ↦ `img.base + dropOff`, size `boxSize`, align `8`,
poll ↦ `img.base + pollOff` (read-only, under `img.FrozenLoaded`). -/
structure CliFutVtOk (img : Obj.Image) (vt dropOff : BitVec 64) (boxSize : Nat)
    (pollOff : BitVec 64) : Prop where
  drop : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + vt) ↦₆₄ᵣ (img.base + dropOff)) ∗ P
  size : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + vt + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 boxSize) ∗ P
  align : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + vt + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  poll : ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((img.base + vt + 0x18#64) ↦₆₄ᵣ (img.base + pollOff)) ∗ P

/-! ## Offsets -/

/-- `dyn SignedPreKeyStore` vtable offset for `SignedPreKeyFiles`. -/
abbrev cliSpkVtOff : BitVec 64 := bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key") - 24)

/-- `dyn PreKeyStore` vtable offset for `OneTimePreKeyFiles`. -/
abbrev cliPkVtOff : BitVec 64 := bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key") - 24)

/-- `dyn KyberPreKeyStore` vtable offset for `KyberPreKeyFiles`. -/
abbrev cliKpkVtOff : BitVec 64 := bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key") - 24)

/-- Future vtable offset for `get_signed_pre_key::{closure#0}`, keyed via its `+0x18` poll slot. -/
abbrev cliSpkGetFutVtOff : BitVec 64 :=
  bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}") - 24)

theorem cliSpkGetFutVtOff_eq : spkGetFutVtOff = cliSpkGetFutVtOff := by rfl

/-- Future vtable offset for `get_pre_key::{closure#0}`, keyed via its `+0x18` poll slot. -/
abbrev cliPkGetFutVtOff : BitVec 64 :=
  bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") - 24)

theorem cliPkGetFutVtOff_eq : pkGetFutVtOff = cliPkGetFutVtOff := by rfl

/-- Future vtable offset for `remove_pre_key::{closure#0}`, keyed via its `+0x18` poll slot. -/
abbrev cliPkRemoveFutVtOff : BitVec 64 :=
  bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") - 24)

theorem cliPkRemoveFutVtOff_eq : pkRemoveFutVtOff = cliPkRemoveFutVtOff := by rfl

/-- Future vtable offset for `get_kyber_pre_key::{closure#0}`, keyed via its `+0x18` poll slot. -/
abbrev cliKpkGetFutVtOff : BitVec 64 :=
  bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}") - 24)

theorem cliKpkGetFutVtOff_eq : kpkGetFutVtOff = cliKpkGetFutVtOff := by rfl

/-- Future vtable offset for `mark_kyber_pre_key_used::{closure#0}`, keyed via its `+0x18` poll slot. -/
abbrev cliKpkMarkFutVtOff : BitVec 64 :=
  bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") - 24)

theorem cliKpkMarkFutVtOff_eq : kpkMarkFutVtOff = cliKpkMarkFutVtOff := by rfl

/-! ## `.data.rel.ro` box size and alignment words -/

set_option maxRecDepth 2000000 in
theorem rodata_cliSpkGetFutSize_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}") - 16) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 16#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
theorem rodata_cliSpkGetFutAlign_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}") - 8) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 8#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
theorem rodata_cliPkGetFutSize_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") - 16) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 16#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
theorem rodata_cliPkGetFutAlign_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") - 8) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 8#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
theorem rodata_cliPkRemoveFutSize_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") - 16) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 16#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
theorem rodata_cliPkRemoveFutAlign_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") - 8) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 8#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
theorem rodata_cliKpkGetFutSize_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}") - 16) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 16#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
theorem rodata_cliKpkGetFutAlign_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}") - 8) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 8#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
theorem rodata_cliKpkMarkFutSize_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") - 16) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 32#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
theorem rodata_cliKpkMarkFutAlign_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") - 8) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 8#64 := by rfl_kernel

/-! ## Future vtables -/

theorem cliSpkGetFutVt_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img) :
    CliFutVtOk img cliSpkGetFutVtOff cliIdFutDropOff 16 (bv% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}")) where
  drop hF hP := by
    dsimp only [cliSpkGetFutVtOff, cliIdFutDropOff]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}") - 24)) (target := num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP
  size hF hP := by
    dsimp only [cliSpkGetFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}") - 24) + 8#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}") - 16) by bv_omega]
    have hh := loads_rodata_holdsBytes himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}") - 16)) (n := 8) (bs := unpack64 16#64)
      (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
      (unpack64_length _) rodata_cliSpkGetFutSize_eq
    obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
    rw [unpack64_length] at hRO hread
    exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP
  align hF hP := by
    dsimp only [cliSpkGetFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}") - 24) + 0x10#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}") - 8) by bv_omega]
    have hh := loads_rodata_holdsBytes himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}") - 8)) (n := 8) (bs := unpack64 8#64)
      (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
      (unpack64_length _) rodata_cliSpkGetFutAlign_eq
    obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
    rw [unpack64_length] at hRO hread
    exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP
  poll hF hP := by
    dsimp only [cliSpkGetFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}") - 24) + 0x18#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}")) by bv_omega]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}"))) (target := num% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP

theorem cliPkGetFutVt_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img) :
    CliFutVtOk img cliPkGetFutVtOff cliIdFutDropOff 16 (bv% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}")) where
  drop hF hP := by
    dsimp only [cliPkGetFutVtOff, cliIdFutDropOff]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") - 24)) (target := num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP
  size hF hP := by
    dsimp only [cliPkGetFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") - 24) + 8#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") - 16) by bv_omega]
    have hh := loads_rodata_holdsBytes himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") - 16)) (n := 8) (bs := unpack64 16#64)
      (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
      (unpack64_length _) rodata_cliPkGetFutSize_eq
    obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
    rw [unpack64_length] at hRO hread
    exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP
  align hF hP := by
    dsimp only [cliPkGetFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") - 24) + 0x10#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") - 8) by bv_omega]
    have hh := loads_rodata_holdsBytes himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") - 8)) (n := 8) (bs := unpack64 8#64)
      (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
      (unpack64_length _) rodata_cliPkGetFutAlign_eq
    obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
    rw [unpack64_length] at hRO hread
    exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP
  poll hF hP := by
    dsimp only [cliPkGetFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") - 24) + 0x18#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}")) by bv_omega]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"))) (target := num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP

theorem cliPkRemoveFutVt_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img) :
    CliFutVtOk img cliPkRemoveFutVtOff cliIdFutDropOff 16 (bv% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}")) where
  drop hF hP := by
    dsimp only [cliPkRemoveFutVtOff, cliIdFutDropOff]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") - 24)) (target := num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP
  size hF hP := by
    dsimp only [cliPkRemoveFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") - 24) + 8#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") - 16) by bv_omega]
    have hh := loads_rodata_holdsBytes himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") - 16)) (n := 8) (bs := unpack64 16#64)
      (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
      (unpack64_length _) rodata_cliPkRemoveFutSize_eq
    obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
    rw [unpack64_length] at hRO hread
    exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP
  align hF hP := by
    dsimp only [cliPkRemoveFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") - 24) + 0x10#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") - 8) by bv_omega]
    have hh := loads_rodata_holdsBytes himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") - 8)) (n := 8) (bs := unpack64 8#64)
      (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
      (unpack64_length _) rodata_cliPkRemoveFutAlign_eq
    obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
    rw [unpack64_length] at hRO hread
    exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP
  poll hF hP := by
    dsimp only [cliPkRemoveFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") - 24) + 0x18#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}")) by bv_omega]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"))) (target := num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP

theorem cliKpkGetFutVt_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img) :
    CliFutVtOk img cliKpkGetFutVtOff cliIdFutDropOff 16 (bv% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}")) where
  drop hF hP := by
    dsimp only [cliKpkGetFutVtOff, cliIdFutDropOff]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}") - 24)) (target := num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP
  size hF hP := by
    dsimp only [cliKpkGetFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}") - 24) + 8#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}") - 16) by bv_omega]
    have hh := loads_rodata_holdsBytes himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}") - 16)) (n := 8) (bs := unpack64 16#64)
      (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
      (unpack64_length _) rodata_cliKpkGetFutSize_eq
    obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
    rw [unpack64_length] at hRO hread
    exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP
  align hF hP := by
    dsimp only [cliKpkGetFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}") - 24) + 0x10#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}") - 8) by bv_omega]
    have hh := loads_rodata_holdsBytes himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}") - 8)) (n := 8) (bs := unpack64 8#64)
      (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
      (unpack64_length _) rodata_cliKpkGetFutAlign_eq
    obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
    rw [unpack64_length] at hRO hread
    exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP
  poll hF hP := by
    dsimp only [cliKpkGetFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}") - 24) + 0x18#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}")) by bv_omega]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}"))) (target := num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP

theorem cliKpkMarkFutVt_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img) :
    CliFutVtOk img cliKpkMarkFutVtOff cliIdFutDropOff 32 (bv% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}")) where
  drop hF hP := by
    dsimp only [cliKpkMarkFutVtOff, cliIdFutDropOff]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") - 24)) (target := num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP
  size hF hP := by
    dsimp only [cliKpkMarkFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") - 24) + 8#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") - 16) by bv_omega]
    have hh := loads_rodata_holdsBytes himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") - 16)) (n := 8) (bs := unpack64 32#64)
      (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
      (unpack64_length _) rodata_cliKpkMarkFutSize_eq
    obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
    rw [unpack64_length] at hRO hread
    exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP
  align hF hP := by
    dsimp only [cliKpkMarkFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") - 24) + 0x10#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") - 8) by bv_omega]
    have hh := loads_rodata_holdsBytes himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") - 8)) (n := 8) (bs := unpack64 8#64)
      (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
      (unpack64_length _) rodata_cliKpkMarkFutAlign_eq
    obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
    rw [unpack64_length] at hRO hread
    exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP
  poll hF hP := by
    dsimp only [cliKpkMarkFutVtOff]
    rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") - 24) + 0x18#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}")) by bv_omega]
    exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"))) (target := num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"))
      (by decide) (by rfl_kernel) (by rfl_kernel) hP

/-! ## Trait-object slots -/

/-- `dyn SignedPreKeyStore` slot `+0x18` relocates to `get_signed_pre_key`. -/
theorem cliSpkGetSlot_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + cliSpkVtOff + 0x18#64) ↦₆₄ᵣ (img.base + bv% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key"))) ∗ P := by
  dsimp only [cliSpkVtOff]
  rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key") - 24) + 0x18#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key")) by bv_omega]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key"))) (target := num% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hP

/-- `dyn PreKeyStore` slot `+0x18` relocates to `get_pre_key`. -/
theorem cliPkGetSlot_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + cliPkVtOff + 0x18#64) ↦₆₄ᵣ (img.base + bv% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key"))) ∗ P := by
  dsimp only [cliPkVtOff]
  rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key") - 24) + 0x18#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key")) by bv_omega]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key"))) (target := num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hP

/-- `dyn PreKeyStore` slot `+0x28` relocates to `remove_pre_key`. -/
theorem cliPkRemoveSlot_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + cliPkVtOff + 0x28#64) ↦₆₄ᵣ (img.base + bv% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key"))) ∗ P := by
  dsimp only [cliPkVtOff]
  rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key") - 24) + 0x28#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key") + 16) by bv_omega]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key") + 16)) (target := num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hP

/-- `dyn KyberPreKeyStore` slot `+0x18` relocates to `get_kyber_pre_key`. -/
theorem cliKpkGetSlot_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + cliKpkVtOff + 0x18#64) ↦₆₄ᵣ (img.base + bv% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key"))) ∗ P := by
  dsimp only [cliKpkVtOff]
  rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key") - 24) + 0x18#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key")) by bv_omega]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key"))) (target := num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hP

/-- `dyn KyberPreKeyStore` slot `+0x28` relocates to `mark_kyber_pre_key_used`. -/
theorem cliKpkMarkSlot_ok {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + cliKpkVtOff + 0x28#64) ↦₆₄ᵣ (img.base + bv% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used"))) ∗ P := by
  dsimp only [cliKpkVtOff]
  rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key") - 24) + 0x28#64 = img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key") + 16) by bv_omega]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key") + 16)) (target := num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hP

end CryptoVerification.SignalSession.Cli.KitInst
