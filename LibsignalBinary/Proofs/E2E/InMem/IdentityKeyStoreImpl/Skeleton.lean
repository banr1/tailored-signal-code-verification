/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.IdentityKeyStoreImpl.Defs
public import LibsignalBinary.Proofs.PublicApi.StoreSession.StoreCallSite
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.InMem.IdentityKeyStoreImpl.Decodes
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base

/-!
# In-Memory Identity Key Store Shared Future-Drop Proofs

Helper lemmas and `subroutine_ok` proofs (`futDrop_ok_trap`, `futDrop_ok`) for the
shared no-op future `drop_glue` used by `InMemIdentityKeyStore`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.IdentityKeyStoreImpl

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

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "core::ptr::drop_glue::<<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>")
  (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity")
  (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "alloc::alloc::handle_alloc_error")

/-! ## Program Address Helpers -/

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

private theorem stackAt_identityShim (sp : BitVec 64) :
    stackAt sp identityShimStack =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp allocHookStack 6 (by decide)

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

private theorem memRegion_32_trust_box (p : BitVec 64) :
    memRegion p 32 =
      (∃∗ b1 : BitVec 8, ∃∗ b0 : BitVec 8, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₆₄ u2) ∗ ((p + 24#64) ↦₈ b0) ∗
        ((p + 25#64) ↦₈ b1) ∗ memRegion (p + 26#64) 6) := by
  rw [memRegion_split p 8 24 (by decide),
    memRegion_split (p + 8#64) 8 16 (by decide),
    memRegion_split (p + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64) 1 7 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64 + 1#64) 1 6 (by decide),
    memRegion_one, memRegion_one, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem save_shim_adrp {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr saveIdentityShimName + 52#64) &&&
      0xfffffffffffff000#64) = b + bv% (page% (ls_off% "<libsignal_protocol::protocol::SenderKeyDistributionMessage as core::convert::TryFrom<&[u8]>>::try_from" + 476)) := by
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity"), BitVec.add_assoc,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

private theorem trust_shim_adrp {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr isTrustedIdentityShimName + 56#64) &&&
      0xfffffffffffff000#64) = b + bv% (page% (ls_off% "<libsignal_protocol::protocol::SenderKeyDistributionMessage as core::convert::TryFrom<&[u8]>>::try_from" + 476)) := by
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity"), BitVec.add_assoc,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

/-! ## Trivial Future Drop Proofs -/

/-- No-op future `drop_glue` satisfies `futDropSpec` on `trTrapProgAt`. -/
theorem futDrop_ok_trap {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      (b + inMemFutDropOff)
      futDropSpec := by
  have hfn : libsignalSessionCode.fnOff inMemFutDropName = num% (ls_off% "core::ptr::drop_glue::<<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>") := inMemFutDrop_fnOff
  change subroutine_ok (trTrapProgAt b C abs) (b + BitVec.ofNat 64 (num% (ls_off% "core::ptr::drop_glue::<<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"))) futDropSpec
  rw [← fnAddr_tripleRatchetProgAt_trap (b := b) (C := C) (abs := abs) hfn]
  simp only [futDropSpec]
  code_fetches CryptoVerification.libsignalSessionCode identityKeyStoreBin b
    (Rust.withPanics (trTrapExterns C abs)) hfn (num% (ls_off% "core::ptr::drop_glue::<<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>")) 4
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- No-op future `drop_glue` satisfies `futDropSpec` on `tripleRatchetProgAt`. -/
theorem futDrop_ok {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      (b + inMemFutDropOff)
      futDropSpec :=
  subroutine_ok_kit_of_trTrap (futDrop_ok_trap (b := b) (C := C) (abs := abs))

end CryptoVerification.E2E.InMem.IdentityKeyStoreImpl
