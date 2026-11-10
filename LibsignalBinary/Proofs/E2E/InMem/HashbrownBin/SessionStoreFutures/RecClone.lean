/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
public import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Specs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.Callees
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Skeleton
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionClone
import LibsignalBinary.Proofs.E2E.Record.Serialization.VecVecClone
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local1
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExt
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Ext
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.Common.StringCloneFlat

/-!
# `SessionRecord` Clone and Drop Bridges for `InMemSessionStore`
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.InMem.SipHashBin
open CryptoVerification.E2E.InMem.HashbrownBin

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem fnAddr_add_eq {b : BitVec 64} {ext : HookMap} {caller callee : String}
    {cOff tOff : Nat} {off : BitVec 64}
    (hc : libsignalSessionCode.fnOff caller = cOff)
    (ht : libsignalSessionCode.fnOff callee = tOff)
    (hoff : BitVec.ofNat 64 cOff + off = BitVec.ofNat 64 tOff) :
    (RebasedProg b ext).fnAddr caller + off = (RebasedProg b ext).fnAddr callee := by
  simp only [RebasedProg, Program.fnAddr_rebase, hc, ht, BitVec.add_assoc, hoff]

theorem sessionClone_ok_rebased (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr Serialization.sessionCloneName)
      (Serialization.sessionCloneSpec A) := by
  obtain ⟨C, ctl, abs, rfl, hAlloc⟩ := hHooks.istripleRatchetProgAt
  exact Serialization.sessionClone_ok b C A ctl abs hAlloc

theorem sessionClone_ok_at_loadSessionClosure (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr loadSessionClosureName + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"))
      (Serialization.sessionCloneSpec A) := by
  rw [fnAddr_add_eq loadSessionClosure_fnOff sessionCloneName_fnOff rfl]
  exact sessionClone_ok_rebased b hHooks

theorem sessionClone_ok_at_storeSessionClosure (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr storeSessionClosureName + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"))
      (Serialization.sessionCloneSpec A) := by
  rw [fnAddr_add_eq storeSessionClosure_fnOff sessionCloneName_fnOff rfl]
  exact sessionClone_ok_rebased b hHooks

theorem vecVecCloneEmpty_ok_rebased (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr Serialization.vecVecCloneName)
      Serialization.vecVecCloneEmptySpec := by
  obtain ⟨C, ctl, abs, rfl, _⟩ := hHooks.istripleRatchetProgAt
  exact Serialization.vecVecCloneEmpty_ok b C ctl abs

theorem vecVecCloneEmpty_ok_at_loadSessionClosure (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr loadSessionClosureName + bv% (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"))
      Serialization.vecVecCloneEmptySpec := by
  rw [fnAddr_add_eq loadSessionClosure_fnOff vecVecCloneName_fnOff rfl]
  exact vecVecCloneEmpty_ok_rebased b hHooks

theorem vecVecCloneEmpty_ok_at_storeSessionClosure (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr storeSessionClosureName + bv% (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"))
      Serialization.vecVecCloneEmptySpec := by
  rw [fnAddr_add_eq storeSessionClosure_fnOff vecVecCloneName_fnOff rfl]
  exact vecVecCloneEmpty_ok_rebased b hHooks

theorem drop_session_structure_local1_ok_rebased (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr FromRecordCallees.dropSessionStructureLocal1Name)
      (FromRecordCallees.dropSessionStructureLocal1Spec A) := by
  obtain ⟨C, ctl, abs, rfl, hAlloc⟩ := hHooks.istripleRatchetProgAt
  exact FromRecordCallees.drop_session_structure_local1_ok hAlloc
    (Getters.drop_vec_message_key_ok hAlloc)
    (Getters.drop_vec_chain_ok hAlloc)

theorem drop_session_structure_local1_ok_at_storeSessionClosure (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr storeSessionClosureName + 0xffffffffffff96d0#64)
      (FromRecordCallees.dropSessionStructureLocal1Spec A) := by
  rw [fnAddr_add_eq storeSessionClosure_fnOff dropSessionStructureLocal1Name_fnOff rfl]
  exact drop_session_structure_local1_ok_rebased b hHooks

theorem hashOneAddr36_ok_at_load (b : BitVec 64) (ext : HookMap) (A : RustAlloc) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr loadSessionClosureName + 0xffffffffffffe0c4#64)
      (hashOneAddr36Spec A) := by
  have h := hashOneAddr36_ok_at_loadSessionClosure b ext A
  have hsub :
      (RebasedProg b ext).fnAddr loadSessionClosureName + 0xffffffffffffe0c4#64 =
      (SipHashBin.RebasedProg b ext).fnAddr SipHashBin.loadSessionClosureName - 0x1f3c#64 := by
    rw [BitVec.sub_eq_add_neg]; rfl
  rwa [hsub]

theorem hashOneAddr36_ok_at_store (b : BitVec 64) (ext : HookMap) (A : RustAlloc) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr storeSessionClosureName + 0xffffffffffffdec4#64)
      (hashOneAddr36Spec A) := by
  have h := hashOneAddr36_ok_at_storeSessionClosure b ext A
  have hsub :
      (RebasedProg b ext).fnAddr storeSessionClosureName + 0xffffffffffffdec4#64 =
      (SipHashBin.RebasedProg b ext).fnAddr SipHashBin.storeSessionClosureName - 0x213c#64 := by
    rw [BitVec.sub_eq_add_neg]; rfl
  rwa [hsub]

theorem memcpy_ok_at_loadSessionClosure (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr loadSessionClosureName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"))
      (sessionMemcpySpec 4096) :=
  hook_ok_at_raw loadSessionClosure_fnOff (by decide : num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") + num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") = num% (ls_off% "memcpy"))
    (by decide) (ls_hook% "memcpy")
    ⟨hookMemcpy, hHooks.memcpy, hookMemcpy_trace_ok 4096⟩

theorem memcpy_region_ok_at_loadSessionClosure (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr loadSessionClosureName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"))
      sessionMemcpyRegionSpec :=
  hook_ok_at_raw loadSessionClosure_fnOff (by decide : num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") + num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") = num% (ls_off% "memcpy"))
    (by decide) (ls_hook% "memcpy")
    ⟨hookMemcpy, hHooks.memcpy, hookMemcpy_region_trace_ok⟩

theorem memcpy_ok_at_storeSessionClosure (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr storeSessionClosureName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"))
      (sessionMemcpySpec 4096) :=
  hook_ok_at_raw storeSessionClosure_fnOff (by decide : num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") + num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") = num% (ls_off% "memcpy"))
    (by decide) (ls_hook% "memcpy")
    ⟨hookMemcpy, hHooks.memcpy, hookMemcpy_trace_ok 4096⟩

theorem memcpy_region_ok_at_storeSessionClosure (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr storeSessionClosureName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"))
      sessionMemcpyRegionSpec :=
  hook_ok_at_raw storeSessionClosure_fnOff (by decide : num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") + num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") = num% (ls_off% "memcpy"))
    (by decide) (ls_hook% "memcpy")
    ⟨hookMemcpy, hHooks.memcpy, hookMemcpy_region_trace_ok⟩

theorem dealloc_ok_at_storeSessionClosure (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr storeSessionClosureName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}"))
      (rustDeallocSpec A) := by
  obtain ⟨C, ctl, abs, rfl, hA⟩ := hHooks.istripleRatchetProgAt
  exact Getters.DropGlueFacts.dealloc_ok_at hA storeSessionClosure_fnOff (by decide : num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") + num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") = num% (ls_off% "__rustc::__rust_dealloc"))

theorem bcmp_ok_at_loadSessionClosure (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr loadSessionClosureName + bv% (ls_off% "bcmp" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}")) e2eBcmpSpec :=
  hook_ok_at_raw loadSessionClosure_fnOff (by decide : num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") + num% (ls_off% "bcmp" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") = num% (ls_off% "bcmp"))
    (by decide) (ls_hook% "bcmp") hHooks.bcmp

theorem bcmp_ok_at_storeSessionClosure (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr storeSessionClosureName + bv% (ls_off% "bcmp" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}")) e2eBcmpSpec :=
  hook_ok_at_raw storeSessionClosure_fnOff (by decide : num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") + num% (ls_off% "bcmp" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") = num% (ls_off% "bcmp"))
    (by decide) (ls_hook% "bcmp") hHooks.bcmp

theorem stringClone_ok_at_storeSessionClosure (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr storeSessionClosureName + bv% (ls_off% "<alloc::string::String as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}")) (stringCloneSpec A) := by
  rw [fnAddr_add_eq storeSessionClosure_fnOff stringCloneName_fnOff rfl]
  exact LibsignalBinary.Proofs.Common.StringCloneFlat.stringClone_rebase_hooks_ok b A ext
    hHooks.shim hHooks.alloc_sat hHooks.memcpy hHooks.rawVecHandleError

theorem sessionAt_eq_head_tail (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (s : Session (List (BitVec 8))) :
    sessionStateReprAt A ss G s =
      ∃∗ bs336 : List (BitVec 8),
        ⌜bs336.length = 336 ∧ G.localIk.cap.toNat < 2 ^ 63 ∧
          SessionInline G s.state (unpack64 G.localIk.cap ++ bs336)⌝ ∗
        (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦ₛ bs336) ∗ sessionAtHeap A G s := by
  apply ProofLib.sepProp_eq_of_entails
  · exact sessionAt_unpack_head_tail A ss G s
  · apply Entails.sepExists_elim; intro bs336
    apply Entails.pure_left; rintro ⟨_, _, hinl⟩
    exact sessionAt_pack_head_tail A ss G s hinl

theorem vecAt_empty_prev_eq_vecHeader (A : RustAlloc) (r : BitVec 64) :
    vecAt A 24 8 (fun (_ : Unit) _ => emp) r 0#64 8#64 [] =
      vecHeader r 0#64 8#64 0#64 := by
  have hbuf : vecBuf A 24 8 (fun (_ : Unit) _ => emp) 0#64 8#64 [] = emp := by
    unfold vecBuf
    simp
  unfold vecAt
  rw [hbuf, sepConj_emp]
  rfl

end CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures
