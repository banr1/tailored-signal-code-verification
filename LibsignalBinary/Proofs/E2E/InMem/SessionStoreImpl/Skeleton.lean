/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.SessionStoreImpl.Specs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKit
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base

/-!
# In-Memory Session Store Poll Bridge Interface and Future-Drop Proofs

Eliminates unreachable `.error ()` poll branches under `inMemLoadRel` and `inMemStoreRel`,
defines the `SessionRecord`-level poll specifications (`HashbrownBinSessionBridge`), and
proves the shared no-op future `drop_glue` contracts.
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
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.InMem.HashbrownBin
open CryptoVerification.E2E.Record.Serialization (CanonSession CanonRecord)

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "core::ptr::drop_glue::<<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>")
  (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session")
  (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "alloc::alloc::handle_alloc_error")

/-! ## Poll Output Simplification -/

/-- Under `inMemLoadRel`, `ans = .ok (some st0.record)`, eliminating the `.error ()` branch of `loadPollOutAtS`. -/
theorem loadPollOutAtS_of_inMemLoadRel
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {A : RustAlloc} {b out : BitVec 64} {st0 : InMemSessState} {rem : AddrVal}
    {ans : Except Unit (Option (SessionRecord (List (BitVec 8))))}
    (hrel : inMemLoadRel st0 rem ans)
    (hScope : Scope st0.record) :
    (∃∗ g : RecordGhost, sessionRecordAt A out g st0.record) ⊢
      loadPollOutAtS Scope A b out ans := by
  rw [hrel]
  dsimp only [loadPollOutAtS]
  exact Entails.pure_right hScope (Entails.refl _)

/-- Under `inMemStoreRel`, `ans = .ok ()`, reducing `storePollOutAt` to its success layout. -/
theorem storePollOutAt_of_inMemStoreRel
    {b out : BitVec 64} {st0 : InMemSessState} {rem : AddrVal}
    {r' : SessionRecord (List (BitVec 8))} {ans : Except Unit Unit}
    (hrel : inMemStoreRel st0 rem r' ans) :
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (out + 8#64) 40 ⊢
      storePollOutAt b out ans := by
  rw [hrel]
  exact Entails.refl _

/-! ## `SessionRecord`-Level Poll Specifications -/

/-- Output layout for `Poll::Ready(Ok(Option<SessionRecord>))` (368 B) at `sret`. -/
def pollOptSessionRecordAt (A : RustAlloc) (sret : BitVec 64) :
    Option (SessionRecord (List (BitVec 8))) → SepProp
  | none =>
    (sret ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (sret + 8#64) 360
  | some r =>
    ∃∗ G' : SessionGhost, ∃∗ ss : Session (List (BitVec 8)),
      ⌜r = ⟨some ss⟩ ∧ RecordInScope r ∧ CanonSession G' ss⌝ ∗
      sessionRecordAt A sret ⟨0#64, 8#64, some G'⟩ ⟨some ss⟩

theorem pollOptSessionRecordAt_some_entails_loadPollOutAtS
    {StoreScope : SessionRecord (List (BitVec 8)) → Prop}
    {A : RustAlloc} {b out : BitVec 64} {st0 : InMemSessState} {rem : AddrVal}
    {ans : Except Unit (Option (SessionRecord (List (BitVec 8))))}
    (hrel : inMemLoadRel st0 rem ans)
    (hScope : StoreScope st0.record) :
    pollOptSessionRecordAt A out (some st0.record) ⊢
      loadPollOutAtS StoreScope A b out ans := by
  dsimp only [pollOptSessionRecordAt]
  refine Entails.trans (Entails.sepExists_elim fun G' => Entails.sepExists_elim fun ss => ?_)
    (loadPollOutAtS_of_inMemLoadRel hrel hScope)
  refine Entails.pure_left fun ⟨hr, _, _⟩ => ?_
  rw [← hr]
  exact @Entails.sepExists_intro RecordGhost
    (fun g => sessionRecordAt A out g st0.record) ⟨0#64, 8#64, some G'⟩

/-- Ghost inputs for `InMemSessionStore::load_session::{closure#0}`. -/
structure LoadSessionRecordSingleGhost where
  futPtr : BitVec 64
  sret : BitVec 64
  mp : BitVec 64
  k0 : BitVec 64
  k1 : BitVec 64
  k : Nat
  peerG : AddrGhost
  record : SessionRecord (List (BitVec 8))
  qAddrPtr : BitVec 64
  qG : AddrGhost

/-- Specification of `InMemSessionStore::load_session::{closure#0}` over `sessionRecordBucketEntryAt`. -/
def loadSessionRecordSingleSpec (A : RustAlloc) : Spec LoadSessionRecordSingleGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.futPtr ∧ s.readReg64 .x8 = x.sret ∧
      x.k < 4 ∧ x.peerG.name.bytes.length = 36 ∧ x.qG.name.bytes.length = 36 ∧
      RecordInScope x.record⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗ ((x.futPtr + 16#64) ↦₈ 0#8) ∗
      table4SingleAt A sessionBucketStride x.mp x.k0 x.k1 x.k
        x.peerG.name.bytes x.peerG.device (sessionRecordBucketEntryAt A x.peerG x.record) ∗
      protocolAddressAt A x.qG x.qAddrPtr ∗
      memRegion x.sret 368 ∗
      A.pool ∗ stackAt s.sp inMemLoadPollStack
  post := fun x s0 sf =>
    let res := if x.qG.name.bytes = x.peerG.name.bytes ∧ x.qG.device = x.peerG.device
               then some x.record else none
    ⌜sf.trace = s0.trace⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗ ((x.futPtr + 16#64) ↦₈ 1#8) ∗
      table4SingleAt A sessionBucketStride x.mp x.k0 x.k1 x.k
        x.peerG.name.bytes x.peerG.device (sessionRecordBucketEntryAt A x.peerG x.record) ∗
      protocolAddressAt A x.qG x.qAddrPtr ∗
      pollOptSessionRecordAt A x.sret res ∗
      A.pool ∗ stackAt s0.sp inMemLoadPollStack
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Ghost inputs for `InMemSessionStore::store_session::{closure#0}`. -/
structure StoreSessionRecordSingleHitGhost where
  futPtr : BitVec 64
  sret : BitVec 64
  mp : BitVec 64
  k0 : BitVec 64
  k1 : BitVec 64
  k : Nat
  peerG : AddrGhost
  oldRecord : SessionRecord (List (BitVec 8))
  qAddrPtr : BitVec 64
  qG : AddrGhost
  recPtr : BitVec 64
  newRecG : RecordGhost
  newRecord : SessionRecord (List (BitVec 8))

/-- Specification of `InMemSessionStore::store_session::{closure#0}` over `sessionRecordBucketEntryAt`. -/
def storeSessionRecordSingleHitSpec (A : RustAlloc) : Spec StoreSessionRecordSingleHitGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.futPtr ∧ s.readReg64 .x8 = x.sret ∧
      x.k < 4 ∧ x.peerG.name.bytes.length = 36 ∧
      x.qG.name.bytes = x.peerG.name.bytes ∧ x.qG.device = x.peerG.device ∧
      RecordInScope x.oldRecord ∧ RecordInScope x.newRecord ∧ x.newRecord.currentSession.isSome⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗
      ((x.futPtr + 16#64) ↦₆₄ x.recPtr) ∗ ((x.futPtr + 24#64) ↦₈ 0#8) ∗
      table4SingleAt A sessionBucketStride x.mp x.k0 x.k1 x.k
        x.peerG.name.bytes x.peerG.device (sessionRecordBucketEntryAt A x.peerG x.oldRecord) ∗
      protocolAddressAt A x.qG x.qAddrPtr ∗
      sessionRecordAt A x.recPtr x.newRecG x.newRecord ∗
      memRegion x.sret 48 ∗
      A.pool ∗ stackAt s.sp inMemStorePollStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.futPtr ↦₆₄ x.mp) ∗ ((x.futPtr + 8#64) ↦₆₄ x.qAddrPtr) ∗
      ((x.futPtr + 16#64) ↦₆₄ x.recPtr) ∗ ((x.futPtr + 24#64) ↦₈ 1#8) ∗
      (∃∗ clonedG : AddrGhost,
        ⌜clonedG.name.bytes = x.peerG.name.bytes ∧ clonedG.device = x.peerG.device⌝ ∗
        table4SingleAt A sessionBucketStride x.mp x.k0 x.k1 x.k
          x.peerG.name.bytes x.peerG.device (sessionRecordBucketEntryAt A clonedG x.newRecord)) ∗
      protocolAddressAt A x.qG x.qAddrPtr ∗
      sessionRecordAt A x.recPtr x.newRecG x.newRecord ∗
      pollUnitResultAt x.sret ∗
      A.pool ∗ stackAt s0.sp inMemStorePollStack
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Interface bundling `load_session` and `store_session` poll closure correctness. -/
structure HashbrownBinSessionBridge (A : RustAlloc) (b : BitVec 64)
    (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop where
  loadSingle_ok :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + inMemLoadPollOff) (loadSessionRecordSingleSpec A)
  storeSingleHit_ok :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + inMemStorePollOff) (storeSessionRecordSingleHitSpec A)

/-! ## Trivial Future Drop Proofs -/

private theorem fnAddr_tripleRatchetProgAt_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {off : Nat}
    (h : libsignalSessionCode.fnOff name = off) :
    (trTrapProgAt b C abs).fnAddr name = b + BitVec.ofNat 64 off := by
  simp only [trTrapProgAt, Program.fnAddr_rebase, h]

private theorem fnAddr_tripleRatchetProgAt {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {off : Nat}
    (h : libsignalSessionCode.fnOff name = off) :
    (tripleRatchetProgAt b C ctl abs).fnAddr name = b + BitVec.ofNat 64 off := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, h]

private theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private theorem stackAt_loadShim (sp : BitVec 64) :
    stackAt sp inMemLoadShimStack =
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp allocHookStack 4 (by decide)

private theorem stackAt_storeShim (sp : BitVec 64) :
    stackAt sp inMemStoreShimStack =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp allocHookStack 6 (by decide)

private theorem memRegion_24_box (p : BitVec 64) :
    memRegion p 24 =
      (∃∗ b0 : BitVec 8, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₈ b0) ∗
        memRegion (p + 17#64) 7) := by
  rw [memRegion_split p 8 16 (by decide),
    memRegion_split (p + 8#64) 8 8 (by decide),
    memRegion_split (p + 8#64 + 8#64) 1 7 (by decide),
    memRegion_one, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_32_box (p : BitVec 64) :
    memRegion p 32 =
      (∃∗ b0 : BitVec 8, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₆₄ u2) ∗ ((p + 24#64) ↦₈ b0) ∗
        memRegion (p + 25#64) 7) := by
  rw [memRegion_split p 8 24 (by decide),
    memRegion_split (p + 8#64) 8 16 (by decide),
    memRegion_split (p + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64) 1 7 (by decide),
    memRegion_one, ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem load_shim_adrp {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr inMemLoadShimName + 40#64) &&&
      0xfffffffffffff000#64) = b + bv% (page% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore as libsignal_protocol::storage::traits::SignedPreKeyStore>::save_signed_pre_key" + 28)) := by
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session"), BitVec.add_assoc,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

private theorem store_shim_adrp {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr inMemStoreShimName + 52#64) &&&
      0xfffffffffffff000#64) = b + bv% (page% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore as libsignal_protocol::storage::traits::SignedPreKeyStore>::save_signed_pre_key" + 28)) := by
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session"), BitVec.add_assoc,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

set_option maxRecDepth 2000000 in
theorem inMemFutDrop_fnAddr_ok_trap {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr inMemFutDropName)
      futDropSpec := by
  simp only [futDropSpec]
  have hfn : libsignalSessionCode.fnOff inMemFutDropName = num% (ls_off% "core::ptr::drop_glue::<<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>") := inMemFutDrop_fnOff
  code_fetches CryptoVerification.libsignalSessionCode sessionStoreBin b
    (Rust.withPanics (trTrapExterns C abs)) hfn (num% (ls_off% "core::ptr::drop_glue::<<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>")) 4
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

set_option maxRecDepth 2000000 in
/-- No-op future `drop_glue` satisfies `futDropSpec` at its symbol address. -/
theorem inMemFutDrop_fnAddr_ok {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr inMemFutDropName)
      futDropSpec := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs inMemFutDropName]
  exact subroutine_ok_kit_of_trTrap (inMemFutDrop_fnAddr_ok_trap (b := b) (C := C) (abs := abs))

theorem futDrop_ok_trap {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      (b + inMemFutDropOff)
      futDropSpec := by
  have h := inMemFutDrop_fnAddr_ok_trap (b := b) (C := C) (abs := abs)
  have hfn : libsignalSessionCode.fnOff inMemFutDropName = num% (ls_off% "core::ptr::drop_glue::<<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>") := inMemFutDrop_fnOff
  rwa [show (trTrapProgAt b C abs).fnAddr inMemFutDropName = b + inMemFutDropOff by
    simp only [trTrapProgAt, Program.fnAddr_rebase, hfn, inMemFutDropOff]] at h

/-- No-op future `drop_glue` satisfies `futDropSpec` at `b + inMemFutDropOff`. -/
theorem futDrop_ok {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      (b + inMemFutDropOff)
      futDropSpec :=
  subroutine_ok_kit_of_trTrap (futDrop_ok_trap (b := b) (C := C) (abs := abs))

end CryptoVerification.E2E.InMem.SessionStoreImpl
