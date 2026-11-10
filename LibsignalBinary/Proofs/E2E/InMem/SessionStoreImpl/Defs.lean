/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Specs
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Specifications.LibsignalPublicApi

/-!
# In-Memory Session Store Definitions

Symbol names, `.data.rel.ro` future vtable and relocation guards, boxed-future layouts
(`inMemLoadBoxAt`, `inMemStoreBoxAt`), and heap representation predicates (`InMemSessState`,
`singleSessionStoreAt`) for `InMemSessionStore`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.InMem.SessionStoreImpl

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.InMem.HashbrownBin
open CryptoVerification.E2E.Record.Serialization (CanonSession CanonRecord)

/-! ## Symbol Names and Offset Guards -/

abbrev inMemLoadShimName : String :=
  "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session"

abbrev inMemStoreShimName : String :=
  "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session"

abbrev inMemLoadPollName : String :=
  "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"

abbrev inMemStorePollName : String :=
  "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"

/-- Shared ICF-folded no-op future `drop_glue` symbol. -/
abbrev inMemFutDropName : String :=
  "core::ptr::drop_glue::<<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"

abbrev inMemSessDropName : String :=
  "core::ptr::drop_glue::<libsignal_protocol::storage::inmem::InMemSessionStore> [local#1]"

abbrev noAllocShimName : String :=
  "__rustc::__rust_no_alloc_shim_is_unstable_v2"

abbrev rustAllocName : String := "__rustc::__rust_alloc"

abbrev rustDeallocName : String := "__rustc::__rust_dealloc"

abbrev handleAllocErrorName : String :=
  "alloc::alloc::handle_alloc_error"

theorem inMemLoadShim_fnOff :
    libsignalSessionCode.fnOff inMemLoadShimName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session") :=
  (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session")

theorem inMemStoreShim_fnOff :
    libsignalSessionCode.fnOff inMemStoreShimName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session") :=
  (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session")

theorem inMemLoadPoll_fnOff :
    libsignalSessionCode.fnOff inMemLoadPollName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") :=
  loadSessionClosure_fnOff

theorem inMemStorePoll_fnOff :
    libsignalSessionCode.fnOff inMemStorePollName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") :=
  storeSessionClosure_fnOff

theorem inMemFutDrop_fnOff :
    libsignalSessionCode.fnOff inMemFutDropName = num% (ls_off% "core::ptr::drop_glue::<<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>") :=
  (ls_lemma% fnOff "core::ptr::drop_glue::<<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>")

set_option maxRecDepth 2000000 in
theorem noAllocShim_fnOff :
    libsignalSessionCode.fnOff noAllocShimName = num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2") := by
  exact (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")

set_option maxRecDepth 2000000 in
theorem rustAlloc_fnOff :
    libsignalSessionCode.fnOff rustAllocName = num% (ls_off% "__rustc::__rust_alloc") := by
  exact (ls_stub% "__rustc::__rust_alloc")

set_option maxRecDepth 2000000 in
theorem rustDealloc_fnOff :
    libsignalSessionCode.fnOff rustDeallocName = num% (ls_off% "__rustc::__rust_dealloc") := by
  exact (ls_stub% "__rustc::__rust_dealloc")

set_option maxRecDepth 2000000 in
theorem handleAllocError_fnOff :
    libsignalSessionCode.fnOff handleAllocErrorName = num% (ls_off% "alloc::alloc::handle_alloc_error") := by
  exact (ls_stub% "alloc::alloc::handle_alloc_error")

/-! ## Vtable Offsets, Code Offsets, and Stack Budgets -/

/-- `.data.rel.ro` `dyn Future` vtable offset for `load_session::{closure#0}`. -/
abbrev inMemLoadFutVtOff : BitVec 64 := bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 24)

/-- `.data.rel.ro` `dyn Future` vtable offset for `store_session::{closure#0}`. -/
abbrev inMemStoreFutVtOff : BitVec 64 := bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") - 24)

abbrev inMemLoadShimOff : BitVec 64 := bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session")

abbrev inMemStoreShimOff : BitVec 64 := bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session")

abbrev inMemLoadPollOff : BitVec 64 := bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}")

abbrev inMemStorePollOff : BitVec 64 := bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}")

abbrev inMemFutDropOff : BitVec 64 := bv% (ls_off% "core::ptr::drop_glue::<<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>")

abbrev inMemLoadShimStack : Nat := allocHookStack + 32

abbrev inMemStoreShimStack : Nat := allocHookStack + 48

abbrev inMemLoadPollStack : Nat := loadSessionClosureStack

abbrev inMemStorePollStack : Nat := storeSessionClosureStack

theorem inMemLoadShimStack_le_extHookStack :
    inMemLoadShimStack ≤ LibsignalTripleRatchet.extHookStack := by decide
theorem inMemStoreShimStack_le_extHookStack :
    inMemStoreShimStack ≤ LibsignalTripleRatchet.extHookStack := by decide

abbrev inMemLoadBoxSize : Nat := 24

abbrev inMemStoreBoxSize : Nat := 32

/-! ## `.data.rel.ro` Vtable Byte and Relocation Guards -/

set_option maxRecDepth 2000000 in
/-- Size field (24 B) in the `load_session` future vtable. -/
theorem rodata_0x4deb0_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 16) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 24#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
/-- Alignment field (8 B) in the `load_session` future vtable. -/
theorem rodata_0x4deb8_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 8) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 8#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
/-- Size field (32 B) in the `store_session` future vtable. -/
theorem rodata_0x4ded0_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") - 16) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 32#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
/-- Alignment field (8 B) in the `store_session` future vtable. -/
theorem rodata_0x4ded8_eq :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") - 8) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 8#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
/-- Drop-glue relocation in the `load_session` future vtable. -/
theorem reloc_0x4dea8_eq :
    libsignalSessionImage.relocs.any
      (fun r => r.off == num% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 24) - libsignalSessionImage.dataOff && r.width == 8 && r.target == num% (ls_off% "core::ptr::drop_glue::<<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>")) = true := by
  rfl_kernel

set_option maxRecDepth 2000000 in
/-- Poll-function relocation in the `load_session` future vtable. -/
theorem reloc_0x4dec0_eq :
    libsignalSessionImage.relocs.any
      (fun r => r.off == num% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}")) - libsignalSessionImage.dataOff && r.width == 8 && r.target == num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}")) = true := by
  rfl_kernel

set_option maxRecDepth 2000000 in
/-- Drop-glue relocation in the `store_session` future vtable. -/
theorem reloc_0x4dec8_eq :
    libsignalSessionImage.relocs.any
      (fun r => r.off == num% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") - 24) - libsignalSessionImage.dataOff && r.width == 8 && r.target == num% (ls_off% "core::ptr::drop_glue::<<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>")) = true := by
  rfl_kernel

set_option maxRecDepth 2000000 in
/-- Poll-function relocation in the `store_session` future vtable. -/
theorem reloc_0x4dee0_eq :
    libsignalSessionImage.relocs.any
      (fun r => r.off == num% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}")) - libsignalSessionImage.dataOff && r.width == 8 && r.target == num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}")) = true := by
  rfl_kernel

/-! ## Boxed Future Layouts -/

/-- Heap layout of the 24-byte `load_session` boxed future at `box`:
`[self, addrA, state : u8, 7 padding bytes]`. -/
def inMemLoadBoxAt (box self addrA : BitVec 64) (st : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₈ st) ∗
    memRegion (box + 0x11#64) 7

/-- Heap layout of the 32-byte `store_session` boxed future at `box`:
`[self, addrA, recA, state : u8, 7 padding bytes]`. -/
def inMemStoreBoxAt (box self addrA recA : BitVec 64) (st : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₆₄ addrA) ∗ ((box + 0x10#64) ↦₆₄ recA) ∗
    ((box + 0x18#64) ↦₈ st) ∗ memRegion (box + 0x19#64) 7

theorem inMemLoadBoxAt_memRegion (box self addrA : BitVec 64) (st : BitVec 8) :
    inMemLoadBoxAt box self addrA st ⊢ memRegion box inMemLoadBoxSize := by
  unfold inMemLoadBoxAt inMemLoadBoxSize
  rw [show (24 : Nat) = 8 + (8 + (1 + 7)) from rfl,
    memRegion_split box 8 16 (by decide),
    memRegion_split (box + 8#64) 8 8 (by decide),
    memRegion_split (box + 8#64 + 8#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo8_entails_memRegion _ _)))

theorem inMemStoreBoxAt_memRegion (box self addrA recA : BitVec 64) (st : BitVec 8) :
    inMemStoreBoxAt box self addrA recA st ⊢ memRegion box inMemStoreBoxSize := by
  unfold inMemStoreBoxAt inMemStoreBoxSize
  rw [show (32 : Nat) = 8 + (8 + (8 + (1 + 7))) from rfl,
    memRegion_split box 8 24 (by decide),
    memRegion_split (box + 8#64) 8 16 (by decide),
    memRegion_split (box + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (box + 8#64 + 8#64 + 8#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (pointsTo8_entails_memRegion _ _))))

theorem inMemLoadPollOff_eq_loadSessionClosure_fnOff :
    inMemLoadPollOff = BitVec.ofNat 64 (libsignalSessionCode.fnOff loadSessionClosureName) := by
  rw [loadSessionClosure_fnOff]

theorem inMemStorePollOff_eq_storeSessionClosure_fnOff :
    inMemStorePollOff = BitVec.ofNat 64 (libsignalSessionCode.fnOff storeSessionClosureName) := by
  rw [storeSessionClosure_fnOff]

/-! ## Store State and Representation Predicate -/

/-- Bucket entry predicate for `RawTable<(ProtocolAddress, SessionRecord)>` at `a`, pairing
`protocolAddressAt` at `a` with a canonical in-scope `sessionRecordAt` at `a + 0x20`. -/
def sessionRecordBucketEntryAt (A : RustAlloc) (g : AddrGhost)
    (r : SessionRecord (List (BitVec 8))) (a : BitVec 64) : SepProp :=
  ∃∗ G : SessionGhost, ∃∗ ss : Session (List (BitVec 8)),
    ⌜r = ⟨some ss⟩ ∧ RecordInScope r ∧ CanonSession G ss⌝ ∗
    protocolAddressAt A g a ∗
    sessionRecordAt A (a + 0x20#64) ⟨0#64, 8#64, some G⟩ ⟨some ss⟩

/-- Logical state of a single-entry `InMemSessionStore`: SipHash-1-3 keys `(k0, k1)`,
occupied bucket index `k < 4`, peer address ghost `peerG`, and stored `SessionRecord`. -/
structure InMemSessState where
  k0 : BitVec 64
  k1 : BitVec 64
  k : Nat
  peerG : AddrGhost
  record : SessionRecord (List (BitVec 8))

/-- Remote-address precondition requiring `rem` to match the store's peer `peer`. -/
def inMemAddrOk (peer : AddrGhost) (rem : AddrVal) : Prop :=
  rem.name = peer.name.bytes ∧ rem.device = peer.device

/-- Separation-logic representation of a single-entry `InMemSessionStore` at `self`
for peer `peer` under record invariant `StoreScope`. -/
def singleSessionStoreAt (A : RustAlloc) (peer : AddrGhost)
    (StoreScope : SessionRecord (List (BitVec 8)) → Prop) (self : BitVec 64)
    (st : InMemSessState) : SepProp :=
  ∃∗ g : AddrGhost,
    ⌜st.peerG = peer ∧ peer.name.bytes.length = 36 ∧ st.k < 4 ∧
      g.name.bytes = peer.name.bytes ∧ g.device = peer.device ∧
      StoreScope st.record ∧ RecordInScope st.record⌝ ∗
    table4SingleAt A sessionBucketStride self st.k0 st.k1 st.k
      peer.name.bytes peer.device
      (sessionRecordBucketEntryAt A g st.record)

/-! ## Instruction Decode Lemmas -/

gen_decodes libsignalSessionCode_tree sessionStoreBin [(ls_off% "core::ptr::drop_glue::<<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>")]

/-! ### `InMemSessionStore::load_session` -/

gen_decodes libsignalSessionCode_tree sessionStoreBin [(ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session") → (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session" + 76)]

/-! ### `InMemSessionStore::store_session` -/

gen_decodes libsignalSessionCode_tree sessionStoreBin [(ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session") → (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session" + 92)]

end CryptoVerification.E2E.InMem.SessionStoreImpl
