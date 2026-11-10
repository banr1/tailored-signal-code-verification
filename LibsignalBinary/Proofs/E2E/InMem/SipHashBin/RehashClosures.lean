/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Specs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Decodes
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.HashOne
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Correctness of `RawTable::reserve_rehash` Hasher Closures

Proves `rehashIdClosure36_ok` and `rehashSessionClosure36_ok`: the inner hasher closures of
`RawTable::reserve_rehash` for `(ProtocolAddress, IdentityKey)` and
`(ProtocolAddress, SessionRecord)` dereference `RandomState`, compute the downward bucket
pointer, and tail-call `RandomState::hash_one::<&ProtocolAddress>`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.SipHashBin

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.InMem.SipHashModel

section RehashClosures

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Call-Site Transport of `hashOneAddrBorrow36_ok` -/

theorem hashOneAddrBorrow36_ok_at_rehashIdClosure (b : BitVec 64) (ext : HookMap) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr rehashIdClosureName + 0xfffffffffffff9d0#64)
      hashOneAddrBorrow36Spec := by
  have hcaller : libsignalSessionCode.fnOff rehashIdClosureName = num% (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>::{closure#0}") :=
    (ls_lemma% fnOff "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>::{closure#0}")
  have hcallee : libsignalSessionCode.fnOff hashOneAddrName = num% (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>") :=
    (ls_lemma% fnOff "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>")
  have hsub :
      (RebasedProg b ext).fnAddr rehashIdClosureName + 0xfffffffffffff9d0#64 =
      (RebasedProg b ext).fnAddr rehashIdClosureName - 0x0630#64 := by
    rw [BitVec.sub_eq_add_neg]; rfl
  rw [hsub, ← Program.fnAddr_back hcaller hcallee (d := 0x0630) (by decide)]
  exact hashOneAddrBorrow36_ok b ext

theorem hashOneAddrBorrow36_ok_at_rehashSessionClosure (b : BitVec 64) (ext : HookMap) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr rehashSessionClosureName + 0xfffffffffffff9b4#64)
      hashOneAddrBorrow36Spec := by
  have hcaller : libsignalSessionCode.fnOff rehashSessionClosureName = num% (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>::{closure#0}") :=
    (ls_lemma% fnOff "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>::{closure#0}")
  have hcallee : libsignalSessionCode.fnOff hashOneAddrName = num% (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>") :=
    (ls_lemma% fnOff "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>")
  have hsub :
      (RebasedProg b ext).fnAddr rehashSessionClosureName + 0xfffffffffffff9b4#64 =
      (RebasedProg b ext).fnAddr rehashSessionClosureName - 0x064c#64 := by
    rw [BitVec.sub_eq_add_neg]; rfl
  rw [hsub, ← Program.fnAddr_back hcaller hcallee (d := 0x064c) (by decide)]
  exact hashOneAddrBorrow36_ok b ext

/-- The `RawTable<(ProtocolAddress, IdentityKey)>::reserve_rehash` hasher closure
satisfies `rehashIdClosure36Spec`. -/
theorem rehashIdClosure36_ok (b : BitVec 64) (ext : HookMap) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr rehashIdClosureName)
      rehashIdClosure36Spec := by
  have h_hash := hashOneAddrBorrow36_ok_at_rehashIdClosure b ext
  simp only [rehashIdClosure36Spec]
  have hfn : libsignalSessionCode.fnOff rehashIdClosureName = num% (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>::{closure#0}") :=
    (ls_lemma% fnOff "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>::{closure#0}")
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b ext hfn (num% (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>::{closure#0}")) 28
  clear hfn
  dsimp only [RebasedProg, rehashIdClosureName, BitVec.ofNat_eq_ofNat] at h_hash ⊢
  generalize_entry (libsignalSessionCode.rebase b ext).fnAddr
    "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>::{closure#0}" = entry
  generalize_entry (libsignalSessionCode.rebase b ext) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  wp_init x s0
  examples_hide_fetches
  obtain ⟨closurePtr, outerClosurePtr, rsPtr, tablePtr, dataEnd, idx, k0, k1, ptr, name, dev⟩ := x
  dsimp only [randomStateAt, idBucketAddr, rehashIdClosureStack] at *
  wp_steps 7
  wp_apply
  wp_done

/-- The `RawTable<(ProtocolAddress, SessionRecord)>::reserve_rehash` hasher closure
satisfies `rehashSessionClosure36Spec`. -/
theorem rehashSessionClosure36_ok (b : BitVec 64) (ext : HookMap) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr rehashSessionClosureName)
      rehashSessionClosure36Spec := by
  have h_hash := hashOneAddrBorrow36_ok_at_rehashSessionClosure b ext
  simp only [rehashSessionClosure36Spec]
  have hfn : libsignalSessionCode.fnOff rehashSessionClosureName = num% (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>::{closure#0}") :=
    (ls_lemma% fnOff "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>::{closure#0}")
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b ext hfn (num% (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>::{closure#0}")) 36
  clear hfn
  dsimp only [RebasedProg, rehashSessionClosureName, BitVec.ofNat_eq_ofNat] at h_hash ⊢
  generalize_entry (libsignalSessionCode.rebase b ext).fnAddr
    "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::state::session::SessionRecord, std::hash::random::RandomState>::{closure#0}>::{closure#0}" = entry
  generalize_entry (libsignalSessionCode.rebase b ext) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  wp_init x s0
  examples_hide_fetches
  obtain ⟨closurePtr, outerClosurePtr, rsPtr, tablePtr, dataEnd, idx, k0, k1, ptr, name, dev⟩ := x
  dsimp only [randomStateAt, sessionBucketAddr, rehashSessionClosureStack] at *
  wp_steps 9
  wp_apply
  wp_done

end RehashClosures

end CryptoVerification.E2E.InMem.SipHashBin
