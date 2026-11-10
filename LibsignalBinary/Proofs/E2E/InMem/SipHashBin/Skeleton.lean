/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Specs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.HashOne
import ProofLib.Hoare.Hooks
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.RehashClosures -- shake: keep

/-!
# SipHash-1-3 Framing and Call-Site Corollaries

Symbol-offset guards, framing from `addrBorrowAt` to full `protocolAddressAt`
(`hashOneAddr36_ok`), and call-site `subroutine_ok` corollaries for all callers of
`RandomState::hash_one::<&ProtocolAddress>`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.SipHashBin

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.InMem.SipHashModel

/-! ## Symbol Offset Guards -/

theorem sipWrite_fnOff : libsignalSessionCode.fnOff sipWriteName = num% (ls_off% "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write") :=
  (ls_lemma% fnOff "<core::hash::sip::Hasher<core::hash::sip::Sip13Rounds> as core::hash::Hasher>::write")

theorem hashOneAddr_fnOff : libsignalSessionCode.fnOff hashOneAddrName = num% (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>") :=
  (ls_lemma% fnOff "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>")

theorem rehashIdClosure_fnOff : libsignalSessionCode.fnOff rehashIdClosureName = num% (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>::{closure#0}") :=
  (ls_lemma% fnOff "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>::{closure#0}")

theorem rehashSessionClosure_fnOff : libsignalSessionCode.fnOff rehashSessionClosureName = num% (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>::{closure#0}") :=
  (ls_lemma% fnOff "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>::{closure#0}")

theorem getIdentityClosure_fnOff : libsignalSessionCode.fnOff getIdentityClosureName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}") :=
  (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}")

theorem saveIdentityClosure_fnOff : libsignalSessionCode.fnOff saveIdentityClosureName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") :=
  (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")

theorem isTrustedIdentityClosure_fnOff : libsignalSessionCode.fnOff isTrustedIdentityClosureName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") :=
  (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}")

theorem loadSessionClosure_fnOff : libsignalSessionCode.fnOff loadSessionClosureName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") :=
  (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}")

theorem storeSessionClosure_fnOff : libsignalSessionCode.fnOff storeSessionClosureName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") :=
  (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}")

theorem hashMapIdInsert_fnOff : libsignalSessionCode.fnOff hashMapIdInsertName = num% (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert") :=
  (ls_lemma% fnOff "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert")

theorem reserveRehashId_fnOff : libsignalSessionCode.fnOff reserveRehashIdName = num% (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>") :=
  (ls_lemma% fnOff "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>")

theorem reserveRehashSession_fnOff : libsignalSessionCode.fnOff reserveRehashSessionName = num% (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>") :=
  (ls_lemma% fnOff "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>")

/-! ## Relative Call-Address Transport -/

/-- Transport `subroutine_ok` to `fnAddr caller + k` when `callerOff + k = calleeOff`. -/
theorem inImage_ok_at {α : Type} {b : BitVec 64} {ext : HookMap} {spec : Spec α}
    {caller callee : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff caller + k = libsignalSessionCode.fnOff callee)
    (h : subroutine_ok (RebasedProg b ext) ((RebasedProg b ext).fnAddr callee) spec) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr caller + BitVec.ofNat 64 k) spec := by
  rwa [← Program.fnAddr_rel rfl rfl hk]

/-- Transport `subroutine_ok` to `fnAddr caller - d` when `calleeOff + d = callerOff`. -/
theorem inImage_ok_back {α : Type} {b : BitVec 64} {ext : HookMap} {spec : Spec α}
    {caller callee : String} {callerOff calleeOff d : Nat}
    (hcaller : libsignalSessionCode.fnOff caller = callerOff)
    (hcallee : libsignalSessionCode.fnOff callee = calleeOff)
    (hd : calleeOff + d = callerOff)
    (h : subroutine_ok (RebasedProg b ext) ((RebasedProg b ext).fnAddr callee) spec) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr caller - BitVec.ofNat 64 d) spec := by
  rwa [← Program.fnAddr_back hcaller hcallee hd]

/-! ## Framing `addrBorrowAt` to `protocolAddressAt` -/

private theorem protocolAddressAt_eq_addrBorrowAt (A : RustAlloc) (g : AddrGhost) (addr : BitVec 64)
    (hpos : 0 < g.name.bytes.length) :
    protocolAddressAt A g addr =
      ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
      addrBorrowAt addr g.name.ptr g.name.bytes g.device ∗
      (addr ↦₆₄ g.name.cap) ∗
      A.live g.name.ptr g.name.cap.toNat 1 ∗
      memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
        (g.name.cap.toNat - g.name.bytes.length) ∗
      memRegion (addr + 25#64) 7 := by
  have hvec :
      vecGhostAt A g.name addr =
        ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
        (addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
        ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
        (g.name.ptr ↦ₛ g.name.bytes) ∗
        A.live g.name.ptr g.name.cap.toNat 1 ∗
        memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
          (g.name.cap.toNat - g.name.bytes.length) := by
    unfold vecGhostAt vecU8At vecHeader
    have h1 :
        ((addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
            (addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
          ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          if g.name.cap = 0 then emp
          else A.live g.name.ptr g.name.cap.toNat 1 ∗ g.name.ptr ↦ₛ g.name.bytes ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length)) ⊢
        (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
          (addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length ∗
          g.name.ptr ↦ₛ g.name.bytes ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
          memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
            (g.name.cap.toNat - g.name.bytes.length)) := by
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
      have hne : g.name.cap ≠ 0 := by
        intro h0; rw [h0] at hlen; change g.name.bytes.length ≤ 0 at hlen; omega
      simp only [hne, ↓reduceIte]
      apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
      have hcomm :
          (((addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
              ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length)) ∗
            (A.live g.name.ptr g.name.cap.toNat 1 ∗ (g.name.ptr ↦ₛ g.name.bytes) ∗
              memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
                (g.name.cap.toNat - g.name.bytes.length))) =
          ((addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
            ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
            (g.name.ptr ↦ₛ g.name.bytes) ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length)) := by ac_rfl
      rw [hcomm]; exact Entails.refl _
    have h2 :
        (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
          (addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length ∗
          g.name.ptr ↦ₛ g.name.bytes ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
          memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
            (g.name.cap.toNat - g.name.bytes.length)) ⊢
        ((addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
            (addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
          ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          if g.name.cap = 0 then emp
          else A.live g.name.ptr g.name.cap.toNat 1 ∗ g.name.ptr ↦ₛ g.name.bytes ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length)) := by
      apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
      have hne : g.name.cap ≠ 0 := by
        intro h0; rw [h0] at hlen; change g.name.bytes.length ≤ 0 at hlen; omega
      rw [sepConj_pure_left_comm]
      apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
      simp only [hne, ↓reduceIte]
      have hcomm :
          ((addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
            ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
            (g.name.ptr ↦ₛ g.name.bytes) ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length)) =
          (((addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
              ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length)) ∗
            (A.live g.name.ptr g.name.cap.toNat 1 ∗ (g.name.ptr ↦ₛ g.name.bytes) ∗
              memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
                (g.name.cap.toNat - g.name.bytes.length))) := by ac_rfl
      rw [hcomm]; exact Entails.refl _
    exact sepProp_eq_of_entails h1 h2
  unfold protocolAddressAt addrBorrowAt
  rw [hvec]
  change (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
      (addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
      ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
      (g.name.ptr ↦ₛ g.name.bytes) ∗
      A.live g.name.ptr g.name.cap.toNat 1 ∗
      memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
        (g.name.cap.toNat - g.name.bytes.length)) ∗
      ((addr + 24#64) ↦₈ g.device) ∗ memRegion (addr + 25#64) 7 = _
  ac_rfl

/-- Full `protocolAddressAt` specification for `RandomState::hash_one::<&ProtocolAddress>`. -/
theorem hashOneAddr36_ok (b : BitVec 64) (ext : HookMap) (A : RustAlloc) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr hashOneAddrName)
      (hashOneAddr36Spec A) := by
  refine subroutine_ok_map (hashOneAddrBorrow36_ok b ext) ?_
  rintro ⟨k0, k1, addr, g⟩ R s0 hpre
  simp only [hashOneAddr36Spec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen36⟩, hmem⟩
  have hpos : 0 < g.name.bytes.length := by omega
  rw [protocolAddressAt_eq_addrBorrowAt A g addr hpos] at hmem
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hmem
  rcases hmem with ⟨hvec_pure, hmem⟩
  refine ⟨⟨k0, k1, addr, g.name.ptr, g.name.bytes, g.device⟩,
    (addr ↦₆₄ g.name.cap) ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
      memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
        (g.name.cap.toNat - g.name.bytes.length) ∗
      memRegion (addr + 25#64) 7 ∗ R, ?_, fun sf hpost => ?_⟩
  · simp only [hashOneAddrBorrow36Spec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen36⟩, ?_⟩
    convert hmem using 1; ac_rfl
  · simp only [hashOneAddrBorrow36Spec, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hret, htr⟩, hpost⟩
    simp only [hashOneAddr36Spec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hret, htr⟩, ?_⟩
    rw [protocolAddressAt_eq_addrBorrowAt A g addr hpos]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hvec_pure, ?_⟩
    convert hpost using 1; ac_rfl

/-! ## Call-Site Corollaries (`addrBorrowAt`) -/

theorem hashOneAddrBorrow36_ok_at_reserveRehashId
    (b : BitVec 64) (ext : HookMap) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr reserveRehashIdName + bv% (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>" - ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>"))
      hashOneAddrBorrow36Spec :=
  inImage_ok_at (k := num% (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>" - ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>"))
    (by rw [reserveRehashId_fnOff, hashOneAddr_fnOff])
    (hashOneAddrBorrow36_ok b ext)

theorem hashOneAddrBorrow36_ok_at_reserveRehashSession
    (b : BitVec 64) (ext : HookMap) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr reserveRehashSessionName + bv% (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>" - ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>"))
      hashOneAddrBorrow36Spec :=
  inImage_ok_at (k := num% (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>" - ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>"))
    (by rw [reserveRehashSession_fnOff, hashOneAddr_fnOff])
    (hashOneAddrBorrow36_ok b ext)

theorem hashOneAddrBorrow36_ok_at_getIdentityClosure
    (b : BitVec 64) (ext : HookMap) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr getIdentityClosureName - 0x08b0#64)
      hashOneAddrBorrow36Spec :=
  inImage_ok_back getIdentityClosure_fnOff hashOneAddr_fnOff (d := 0x08b0) (by decide)
    (hashOneAddrBorrow36_ok b ext)

theorem hashOneAddrBorrow36_ok_at_saveIdentityClosure
    (b : BitVec 64) (ext : HookMap) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr saveIdentityClosureName - 0x0a24#64)
      hashOneAddrBorrow36Spec :=
  inImage_ok_back saveIdentityClosure_fnOff hashOneAddr_fnOff (d := 0x0a24) (by decide)
    (hashOneAddrBorrow36_ok b ext)

theorem hashOneAddrBorrow36_ok_at_isTrustedIdentityClosure
    (b : BitVec 64) (ext : HookMap) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr isTrustedIdentityClosureName - 0x0c1c#64)
      hashOneAddrBorrow36Spec :=
  inImage_ok_back isTrustedIdentityClosure_fnOff hashOneAddr_fnOff (d := 0x0c1c) (by decide)
    (hashOneAddrBorrow36_ok b ext)

theorem hashOneAddrBorrow36_ok_at_loadSessionClosure
    (b : BitVec 64) (ext : HookMap) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr loadSessionClosureName - 0x1f3c#64)
      hashOneAddrBorrow36Spec :=
  inImage_ok_back loadSessionClosure_fnOff hashOneAddr_fnOff (d := 0x1f3c) (by decide)
    (hashOneAddrBorrow36_ok b ext)

theorem hashOneAddrBorrow36_ok_at_storeSessionClosure
    (b : BitVec 64) (ext : HookMap) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr storeSessionClosureName - 0x213c#64)
      hashOneAddrBorrow36Spec :=
  inImage_ok_back storeSessionClosure_fnOff hashOneAddr_fnOff (d := 0x213c) (by decide)
    (hashOneAddrBorrow36_ok b ext)

theorem hashOneAddrBorrow36_ok_at_hashMapIdInsert
    (b : BitVec 64) (ext : HookMap) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr hashMapIdInsertName - bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 608))
      hashOneAddrBorrow36Spec :=
  inImage_ok_back hashMapIdInsert_fnOff hashOneAddr_fnOff (d := num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 608)) (by decide)
    (hashOneAddrBorrow36_ok b ext)

/-! ## Call-Site Corollaries (`protocolAddressAt`) -/

theorem hashOneAddr36_ok_at_reserveRehashId
    (b : BitVec 64) (ext : HookMap) (A : RustAlloc) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr reserveRehashIdName + bv% (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>" - ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>"))
      (hashOneAddr36Spec A) :=
  inImage_ok_at (k := num% (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>" - ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>"))
    (by rw [reserveRehashId_fnOff, hashOneAddr_fnOff])
    (hashOneAddr36_ok b ext A)

theorem hashOneAddr36_ok_at_reserveRehashSession
    (b : BitVec 64) (ext : HookMap) (A : RustAlloc) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr reserveRehashSessionName + bv% (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>" - ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>"))
      (hashOneAddr36Spec A) :=
  inImage_ok_at (k := num% (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>" - ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>"))
    (by rw [reserveRehashSession_fnOff, hashOneAddr_fnOff])
    (hashOneAddr36_ok b ext A)

theorem hashOneAddr36_ok_at_getIdentityClosure
    (b : BitVec 64) (ext : HookMap) (A : RustAlloc) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr getIdentityClosureName - 0x08b0#64)
      (hashOneAddr36Spec A) :=
  inImage_ok_back getIdentityClosure_fnOff hashOneAddr_fnOff (d := 0x08b0) (by decide)
    (hashOneAddr36_ok b ext A)

theorem hashOneAddr36_ok_at_saveIdentityClosure
    (b : BitVec 64) (ext : HookMap) (A : RustAlloc) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr saveIdentityClosureName - 0x0a24#64)
      (hashOneAddr36Spec A) :=
  inImage_ok_back saveIdentityClosure_fnOff hashOneAddr_fnOff (d := 0x0a24) (by decide)
    (hashOneAddr36_ok b ext A)

theorem hashOneAddr36_ok_at_isTrustedIdentityClosure
    (b : BitVec 64) (ext : HookMap) (A : RustAlloc) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr isTrustedIdentityClosureName - 0x0c1c#64)
      (hashOneAddr36Spec A) :=
  inImage_ok_back isTrustedIdentityClosure_fnOff hashOneAddr_fnOff (d := 0x0c1c) (by decide)
    (hashOneAddr36_ok b ext A)

theorem hashOneAddr36_ok_at_loadSessionClosure
    (b : BitVec 64) (ext : HookMap) (A : RustAlloc) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr loadSessionClosureName - 0x1f3c#64)
      (hashOneAddr36Spec A) :=
  inImage_ok_back loadSessionClosure_fnOff hashOneAddr_fnOff (d := 0x1f3c) (by decide)
    (hashOneAddr36_ok b ext A)

theorem hashOneAddr36_ok_at_storeSessionClosure
    (b : BitVec 64) (ext : HookMap) (A : RustAlloc) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr storeSessionClosureName - 0x213c#64)
      (hashOneAddr36Spec A) :=
  inImage_ok_back storeSessionClosure_fnOff hashOneAddr_fnOff (d := 0x213c) (by decide)
    (hashOneAddr36_ok b ext A)

theorem hashOneAddr36_ok_at_hashMapIdInsert
    (b : BitVec 64) (ext : HookMap) (A : RustAlloc) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr hashMapIdInsertName - bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 608))
      (hashOneAddr36Spec A) :=
  inImage_ok_back hashMapIdInsert_fnOff hashOneAddr_fnOff (d := num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 608)) (by decide)
    (hashOneAddr36_ok b ext A)

end CryptoVerification.E2E.InMem.SipHashBin
