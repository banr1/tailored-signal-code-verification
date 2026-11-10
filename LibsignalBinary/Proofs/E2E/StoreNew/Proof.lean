/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.StoreNew.RoData
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.StoreNew.Fetch
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Proofs for `RandomState::new` and `HashMap::new` TLS lazy initialization

Proves base-rebased and image-level contracts for `<InMemSignedPreKeyStore>::new` /
`<InMemSessionStore>::new` (`0x127d8`) and `<InMemIdentityKeyStore>::new` (`0x0c238`) across both
initialized (`tag = 1`) and uninitialized (`tag ≠ 1`) TLS `KEYS` states.
-/

@[expose] public section

namespace CryptoVerification.E2E.StoreNew

open Arm64 ProofLib ProofLib.ObjectLoad
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem sessionStoreNew_fnAddr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    b + bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore>::new") = (tripleRatchetProgAt b C ctl abs).fnAddr inMemSignedPreKeyStoreNewName := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, inMemSignedPreKeyStoreNew_fnOff]

theorem identityStoreNew_fnAddr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    b + bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore>::new") = (tripleRatchetProgAt b C ctl abs).fnAddr inMemIdentityKeyStoreNewName := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, inMemIdentityKeyStoreNew_fnOff]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section PreSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

end PreSimp

/-! ## `ADRP` page-resolution and SIMD extract helpers -/

theorem adrp_got_page_session_eq (b entry : BitVec 64)
    (halign : b &&& 0xfff#64 = 0#64) (hentry : b + bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore>::new") = entry) :
    (entry + bv% (12) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_field% gotOff) - page% (ls_off% "<libsignal_protocol::state::session::SessionState>::with_receiver_chain" + 872)) = b + bv% (page% (ls_field% gotOff)) := by
  subst hentry
  rw [BitVec.add_assoc b, adrp_page_of_aligned halign, BitVec.add_assoc]
  rfl

theorem adrp_ro_page_session_eq (b entry : BitVec 64)
    (halign : b &&& 0xfff#64 = 0#64) (hentry : b + bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore>::new") = entry) :
    (entry + bv% (44) &&& bv% (2 ^ 64 - 4096)) + bv% (ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964") - page% (ls_off% "<libsignal_protocol::state::session::SessionState>::with_receiver_chain" + 872)) = b + bv% (ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964")) := by
  subst hentry
  rw [BitVec.add_assoc b, adrp_page_of_aligned halign, BitVec.add_assoc]
  rfl

theorem adrp_got_page_identity_eq (b entry : BitVec 64)
    (halign : b &&& 0xfff#64 = 0#64) (hentry : b + bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore>::new") = entry) :
    (entry + bv% (16) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_field% gotOff) - page% (ls_off% "<libsignal_protocol::sealed_sender::sealed_sender_v1::EphemeralKeys>::calculate" + 532)) = b + bv% (page% (ls_field% gotOff)) := by
  subst hentry
  rw [BitVec.add_assoc b, adrp_page_of_aligned halign, BitVec.add_assoc]
  rfl

theorem adrp_ro_page_identity_eq (b entry : BitVec 64)
    (halign : b &&& 0xfff#64 = 0#64) (hentry : b + bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore>::new") = entry) :
    (entry + bv% (60) &&& bv% (2 ^ 64 - 4096)) + bv% (ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964") - page% (ls_off% "<libsignal_protocol::sealed_sender::sealed_sender_v1::EphemeralKeys>::calculate" + 532)) = b + bv% (ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964")) := by
  subst hentry
  rw [BitVec.add_assoc b, adrp_page_of_aligned halign, BitVec.add_assoc]
  rfl

/-! ## `<InMemSignedPreKeyStore>::new` (`0x127d8`) base-level proofs -/

theorem memRegion_48_unfold (out : BitVec 64) :
    memRegion out 48 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        (out ↦₆₄ v0) ∗ ((out + 8#64) ↦₆₄ v1) ∗ ((out + 16#64) ↦₆₄ v2) ∗
        ((out + 24#64) ↦₆₄ v3) ∗ ((out + 32#64) ↦₆₄ v4) ∗ ((out + 40#64) ↦₆₄ v5) := by
  rw [memRegion_48_eq_cells]
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]

theorem emptyHashMapAt_unfold (ctrlPtr out k0 k1 : BitVec 64) :
    emptyHashMapAt ctrlPtr out k0 k1 =
      (out ↦₆₄ ctrlPtr) ∗ ((out + 8#64) ↦₆₄ 0#64) ∗
      ((out + 16#64) ↦₆₄ 0#64) ∗ ((out + 24#64) ↦₆₄ 0#64) ∗
      ((out + 32#64) ↦₆₄ k0) ∗ ((out + 40#64) ↦₆₄ k1) := by
  simp only [emptyHashMapAt, emptyRawTableAt, randomStateAt,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-- Initialized TLS path (`tag = 1#8`) for `<InMemSignedPreKeyStore>::new` (`0x127d8`): increments
`word[t + 0]` in `t = s0.tpidrEl0 + g.tpoff` and writes `emptyHashMapAt g.ctrlPtr g.out g.k0 g.k1`. -/
theorem sessionStore_new_init_base_ok (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (halign : b &&& 0xfff#64 = 0#64) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr inMemSignedPreKeyStoreNewName)
      (sessionStoreNewInitBaseSpec b) := by
  simp only [sessionStoreNewInitBaseSpec, tlsKeysInitAt, tlsKeysRawAt, storeNewRoDataAt,
    tlsKeysGotOff, emptyRawTableOff, emptyHashMapAt_unfold,
    memRegion_48_unfold, stackAt_32_eq_cells, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  cells_unfold
  have hentry : b + bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore>::new") = (tripleRatchetProgAt b C ctl abs).fnAddr inMemSignedPreKeyStoreNewName :=
    sessionStoreNew_fnAddr_eq b C ctl abs
  code_fetches CryptoVerification.libsignalSessionCode
    libsignalSessionBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) inMemSignedPreKeyStoreNew_fnOff (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore>::new")) 112
  dsimp only [tripleRatchetProgAt] at hentry ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr inMemSignedPreKeyStoreNewName = entry
  wpp_init g s0
  rcases g with ⟨out, tpoff, ctrlPtr, k0, k1⟩
  dsimp only at h hpre ⊢
  subst h
  apply SepWPp.of_sepWP_ret
  wp_steps
  rw [adrp_got_page_session_eq b entry halign hentry]
  wp_steps
  rw [adrp_ro_page_session_eq b entry halign hentry]
  wp_steps
  wp_done

theorem randomKeys_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hRk : HookSat abs randomKeysName randomKeysSpec) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff randomKeysName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) randomKeysSpec :=
  hook_ok_at (hname := randomKeysName) rfl hk (by fnoff_eq) (by fnoff_eq) (by decide +kernel)
    (by unfold HookSat at *; exact hRk)

theorem stackAt_sessionStoreNew_eq (sp : BitVec 64) :
    stackAt sp inMemSessionStoreNewStack =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - BitVec.ofNat 64 32) 4 := by
  rw [show inMemSessionStoreNewStack = extHookStack + 8 * 4 from rfl]
  exact stackAt_split_cells sp extHookStack 4 (by decide)

theorem sessionStore_new_uninit_base_ok (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (halign : b &&& 0xfff#64 = 0#64)
    (hRk : HookSat abs randomKeysName randomKeysSpec) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr inMemSignedPreKeyStoreNewName)
      (sessionStoreNewUninitBaseSpec b) := by
  simp only [sessionStoreNewUninitBaseSpec, tlsKeysInitAt, tlsKeysRawAt, storeNewRoDataAt,
    tlsKeysGotOff, emptyRawTableOff, emptyHashMapAt_unfold,
    memRegion_48_unfold, stackAt_sessionStoreNew_eq, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  cells_unfold
  have hentry : b + bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore>::new") = (tripleRatchetProgAt b C ctl abs).fnAddr inMemSignedPreKeyStoreNewName :=
    sessionStoreNew_fnAddr_eq b C ctl abs
  have hcall := randomKeys_ok_at b C ctl abs hRk inMemSignedPreKeyStoreNewName (num% (ls_off% "std::sys::random::linux::hashmap_random_keys" - ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore>::new"))
    (by rw [inMemSignedPreKeyStoreNew_fnOff, randomKeys_fnOff])
  simp only [randomKeysSpec] at hcall
  code_fetches CryptoVerification.libsignalSessionCode
    libsignalSessionBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) inMemSignedPreKeyStoreNew_fnOff (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore>::new")) 112
  dsimp only [tripleRatchetProgAt, BitVec.ofNat_eq_ofNat] at hentry hcall ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr inMemSignedPreKeyStoreNewName = entry
  wpp_init g s0
  rcases g with ⟨out, tpoff, ctrlPtr, k0Old, k1Old, tag⟩
  dsimp only at h h_1 hpre ⊢
  subst h_1
  apply SepWPp.of_sepWP_ret
  wp_steps
  rw [adrp_got_page_session_eq b entry halign hentry]
  wp_steps
  wp_apply
  wp_steps
  rw [adrp_ro_page_session_eq b entry halign hentry]
  wp_steps
  wp_done

/-! ## `<InMemIdentityKeyStore>::new` (`0x0c238`) base-level proofs -/

theorem memRegion_120_unfold (out : BitVec 64) :
    memRegion out 120 =
      ∃∗ v14 : BitVec 32,
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
      ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
      ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64,
        (out ↦₆₄ v0) ∗ ((out + 8#64) ↦₆₄ v1) ∗ ((out + 16#64) ↦₆₄ v2) ∗
        ((out + 24#64) ↦₆₄ v3) ∗ ((out + 32#64) ↦₆₄ v4) ∗ ((out + 40#64) ↦₆₄ v5) ∗
        ((out + 48#64) ↦₆₄ v6) ∗ ((out + 56#64) ↦₆₄ v7) ∗ ((out + 64#64) ↦₆₄ v8) ∗
        ((out + 72#64) ↦₆₄ v9) ∗ ((out + 80#64) ↦₆₄ v10) ∗ ((out + 88#64) ↦₆₄ v11) ∗
        ((out + 96#64) ↦₆₄ v12) ∗ ((out + 104#64) ↦₆₄ v13) ∗
        ((out + 112#64) ↦₃₂ v14) ∗ memRegion (out + 116#64) 4 := by
  rw [memRegion_120_split]
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem emptyIdentityKeyStoreAt_unfold (ctrlPtr out k0 k1 : BitVec 64)
    {kpBytes : List (BitVec 8)} (regId : BitVec 32) (hlen : kpBytes.length = 64) :
    emptyIdentityKeyStoreAt ctrlPtr out k0 k1 kpBytes regId =
      (out ↦₆₄ ctrlPtr) ∗ ((out + 8#64) ↦₆₄ 0#64) ∗
      ((out + 16#64) ↦₆₄ 0#64) ∗ ((out + 24#64) ↦₆₄ 0#64) ∗
      ((out + 32#64) ↦₆₄ k0) ∗ ((out + 40#64) ↦₆₄ k1) ∗
      ((out + 48#64) ↦₆₄ word64At kpBytes 0) ∗
      ((out + 56#64) ↦₆₄ word64At kpBytes 1) ∗
      ((out + 64#64) ↦₆₄ word64At kpBytes 2) ∗
      ((out + 72#64) ↦₆₄ word64At kpBytes 3) ∗
      ((out + 80#64) ↦₆₄ word64At kpBytes 4) ∗
      ((out + 88#64) ↦₆₄ word64At kpBytes 5) ∗
      ((out + 96#64) ↦₆₄ word64At kpBytes 6) ∗
      ((out + 104#64) ↦₆₄ word64At kpBytes 7) ∗
      ((out + 112#64) ↦₃₂ regId) ∗
      memRegion (out + 116#64) 4 := by
  simp only [emptyIdentityKeyStoreAt, emptyHashMapAt_unfold,
    pointsToBytes_64_eq_words (out + 48#64) hlen,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-- Initialized TLS path (`tag = 1#8`) for `<InMemIdentityKeyStore>::new` (`0x0c238`): increments
`word[t + 0]`, copies the 64-byte `IdentityKeyPair`, writes `regId` at `+112`, and initializes the
`identities` `HashMap` at `+0..+48`. -/
theorem identityStore_new_init_base_ok (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (halign : b &&& 0xfff#64 = 0#64) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr inMemIdentityKeyStoreNewName)
      (identityStoreNewInitBaseSpec b) := by
  simp only [identityStoreNewInitBaseSpec, tlsKeysInitAt, tlsKeysRawAt, storeNewRoDataAt,
    tlsKeysGotOff, emptyRawTableOff,
    memRegion_120_unfold, stackAt_48_eq_cells, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  cells_unfold
  have hentry : b + bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore>::new") = (tripleRatchetProgAt b C ctl abs).fnAddr inMemIdentityKeyStoreNewName :=
    identityStoreNew_fnAddr_eq b C ctl abs
  code_fetches CryptoVerification.libsignalSessionCode
    libsignalSessionBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) inMemIdentityKeyStoreNew_fnOff (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore>::new")) 164
  dsimp only [tripleRatchetProgAt] at hentry ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr inMemIdentityKeyStoreNewName = entry
  wpp_init g s0
  rcases g with ⟨out, kpPtr, kpBytes, regId, tpoff, ctrlPtr, k0, k1⟩
  dsimp only at h h_1 h_2 h_3 hpre ⊢
  rw [emptyIdentityKeyStoreAt_unfold ctrlPtr out k0 k1 regId h]
  rw [pointsToBytes_64_eq_words kpPtr h] at hpre ⊢
  simp only [sepConj_assoc] at hpre ⊢
  subst h_3 h_2 h_1
  apply SepWPp.of_sepWP_ret
  wp_steps
  rw [adrp_got_page_identity_eq b entry halign hentry]
  wp_steps
  rw [adrp_ro_page_identity_eq b entry halign hentry]
  wp_steps
  wp_done

theorem stackAt_identityStoreNew_eq (sp : BitVec 64) :
    stackAt sp inMemIdentityStoreNewStack =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - BitVec.ofNat 64 48) 6 := by
  rw [show inMemIdentityStoreNewStack = extHookStack + 8 * 6 from rfl]
  exact stackAt_split_cells sp extHookStack 6 (by decide)

/-- Uninitialized TLS path (`tag ≠ 1#8`) for `<InMemIdentityKeyStore>::new` (`0x0c238`): calls
`hashmap_random_keys`, initializes the TLS cell to `(k0 + 1#64, k1, 1#8)`, and populates
`emptyIdentityKeyStoreAt`. -/
theorem identityStore_new_uninit_base_ok (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (halign : b &&& 0xfff#64 = 0#64)
    (hRk : HookSat abs randomKeysName randomKeysSpec) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr inMemIdentityKeyStoreNewName)
      (identityStoreNewUninitBaseSpec b) := by
  simp only [identityStoreNewUninitBaseSpec, tlsKeysInitAt, tlsKeysRawAt, storeNewRoDataAt,
    tlsKeysGotOff, emptyRawTableOff,
    memRegion_120_unfold, stackAt_identityStoreNew_eq, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  cells_unfold
  have hentry : b + bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore>::new") = (tripleRatchetProgAt b C ctl abs).fnAddr inMemIdentityKeyStoreNewName :=
    identityStoreNew_fnAddr_eq b C ctl abs
  have hcall := randomKeys_ok_at b C ctl abs hRk inMemIdentityKeyStoreNewName (num% (ls_off% "std::sys::random::linux::hashmap_random_keys" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore>::new"))
    (by rw [inMemIdentityKeyStoreNew_fnOff, randomKeys_fnOff])
  simp only [randomKeysSpec] at hcall
  code_fetches CryptoVerification.libsignalSessionCode
    libsignalSessionBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) inMemIdentityKeyStoreNew_fnOff (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore>::new")) 164
  dsimp only [tripleRatchetProgAt, BitVec.ofNat_eq_ofNat] at hentry hcall ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr inMemIdentityKeyStoreNewName = entry
  wpp_init g s0
  rcases g with ⟨out, kpPtr, kpBytes, regId, tpoff, ctrlPtr, k0Old, k1Old, tag⟩
  dsimp only at h h_1 h_2 h_3 h_4 hpre ⊢
  simp only [emptyIdentityKeyStoreAt_unfold ctrlPtr out _ _ regId h_4]
  rw [pointsToBytes_64_eq_words kpPtr h_4] at hpre ⊢
  simp only [sepConj_assoc] at hpre ⊢
  subst h_3 h_2 h_1
  apply SepWPp.of_sepWP_ret
  wp_steps
  rw [adrp_got_page_identity_eq b entry halign hentry]
  wp_steps
  wp_apply
  wp_steps
  rw [adrp_ro_page_identity_eq b entry halign hentry]
  wp_steps
  wp_done

/-! ## Image-level (`tripleRatchetProg`) bridge theorems -/

theorem memRegion_sepConj_pure (a : BitVec 64) (n : Nat) (φ : Prop) (Q : SepProp) :
    memRegion a n ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ (memRegion a n ∗ Q) := by
  rw [← sepConj_assoc, sepConj_comm (memRegion a n) ⌜φ⌝, sepConj_assoc]

theorem pointsToBytes_sepConj_pure (a : BitVec 64) (bs : List (BitVec 8)) (φ : Prop) (Q : SepProp) :
    (a ↦ₛ bs) ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ ((a ↦ₛ bs) ∗ Q) := by
  rw [← sepConj_assoc, sepConj_comm (a ↦ₛ bs) ⌜φ⌝, sepConj_assoc]

theorem stackAt_add_eq (sp : BitVec 64) (n k : Nat) (h : n + k ≤ 2 ^ 64) :
    stackAt sp (k + n) =
      stackAt sp k ∗ stackAt (sp - BitVec.ofNat 64 k) n := by
  rw [Nat.add_comm k n, sepConj_comm]
  simp only [stackAt]
  rw [memRegion_split _ n k h]
  have e1 : sp - BitVec.ofNat 64 (n + k) = sp - BitVec.ofNat 64 k - BitVec.ofNat 64 n := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  have e2 : sp - BitVec.ofNat 64 (n + k) + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 k := by
    rw [e1, BitVec.sub_add_cancel]
  rw [e2, e1]

theorem stackAt_sessionStoreNew_frame_split (sp : BitVec 64) :
    stackAt sp inMemSessionStoreNewStack =
      stackAt sp inMemSessionStoreNewFrame ∗ stackAt (sp - 32#64) extHookStack :=
  stackAt_add_eq sp extHookStack inMemSessionStoreNewFrame (by decide)

theorem stackAt_identityStoreNew_frame_split (sp : BitVec 64) :
    stackAt sp inMemIdentityStoreNewStack =
      stackAt sp inMemIdentityStoreNewFrame ∗ stackAt (sp - 48#64) extHookStack :=
  stackAt_add_eq sp extHookStack inMemIdentityStoreNewFrame (by decide)

/-- Image-level initialized TLS path (`tag = 1#8`) for `<InMemSignedPreKeyStore>::new` (`0x127d8`). -/
theorem sessionStore_new_init_ok {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProg img C ctl abs)
      (entryOf img inMemSignedPreKeyStoreNewName)
      (sessionStoreNewInitSpec img) := by
  apply root_of_tripleRatchetProgAt himg
  refine subroutine_ok_refine
    (sessionStore_new_init_base_ok img.base C ctl abs (base_aligned_of_loads himg))
    fun ⟨out, k0, k1⟩ R s0 hpre => ?_
  rw [sessionStoreNewInitSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, _⟩, hpre⟩
  dsimp only at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx8, hpre⟩
  have hro := storeNewRoDataAt_intro himg hF hpre
  refine ⟨⟨out, tlsKeysTpoff, img.base + emptyCtrlOff, k0, k1⟩, ?_, fun sf hpost => ?_⟩
  · simp only [sessionStoreNewInitBaseSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx8, by simpa only [sepConj_assoc] using hro⟩
  · simp only [sessionStoreNewInitBaseSpec, sessionStoreNewInitSpec, Spec.inImage,
      sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hpure, hpost⟩
    exact ⟨hpure, Satisfies.drop_left hpost⟩

/-- Image-level uninitialized TLS path (`tag ≠ 1#8`) for `<InMemSignedPreKeyStore>::new` (`0x127d8`). -/
theorem sessionStore_new_uninit_ok {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hRk : HookSat abs randomKeysName randomKeysSpec) :
    subroutine_ok (tripleRatchetProg img C ctl abs)
      (entryOf img inMemSignedPreKeyStoreNewName)
      (sessionStoreNewUninitSpec img) := by
  apply root_of_tripleRatchetProgAt himg
  refine subroutine_ok_refine
    (sessionStore_new_uninit_base_ok img.base C ctl abs (base_aligned_of_loads himg) hRk)
    fun ⟨out, k0Old, k1Old, tag⟩ R s0 hpre => ?_
  rw [sessionStoreNewUninitSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, _⟩, hpre⟩
  dsimp only at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  have hro := storeNewRoDataAt_intro himg hF hpre
  refine ⟨⟨out, tlsKeysTpoff, img.base + emptyCtrlOff, k0Old, k1Old, tag⟩, ?_, fun sf hpost => ?_⟩
  · simp only [sessionStoreNewUninitBaseSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, by simpa only [sepConj_assoc] using hro⟩
  · simp only [sessionStoreNewUninitBaseSpec, sessionStoreNewUninitSpec, Spec.inImage,
      sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hpure', hpost⟩
    exact ⟨hpure', Satisfies.drop_left hpost⟩

/-- Unified image-level contract (`st : Option (BitVec 64 × BitVec 64)`) for
`<InMemSignedPreKeyStore>::new` / `<InMemSessionStore>::new` (`0x127d8`). -/
theorem sessionStore_new_ok {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hRk : HookSat abs randomKeysName randomKeysSpec) :
    subroutine_ok (tripleRatchetProg img C ctl abs)
      (entryOf img inMemSignedPreKeyStoreNewName)
      (sessionStoreNewSpec img) := by
  refine subroutine_ok_intro fun ⟨out, st⟩ R s0 hpc hrun hpre hsp => ?_
  cases st with
  | none =>
    simp only [sessionStoreNewSpec, Spec.inImage, tlsKeysAt, tlsKeysUninitAt,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
    rcases hpre with ⟨k0Old, k1Old, tag, hpre⟩
    refine reaches_of_ghost (sessionStore_new_uninit_ok himg hRk)
      (out, k0Old, k1Old, tag) emp hpc hrun hsp ?_ (fun sf _ hpost => ?_)
    · simp only [sessionStoreNewUninitSpec, Spec.inImage, emp_sepConj,
        sepConj_assoc, memRegion_sepConj_pure, satisfies_pure_sepConj] at hpre ⊢
      rcases hpre with ⟨himg_ok, hx8, htag, hmem⟩
      exact ⟨himg_ok, ⟨hx8, htag⟩, hmem⟩
    · simpa only [sessionStoreNewUninitSpec, sessionStoreNewSpec, Spec.inImage,
        emp_sepConj, sepConj_assoc] using hpost
  | some ks =>
    rcases ks with ⟨k0, k1⟩
    refine reaches_of_ghost (sessionStore_new_init_ok himg)
      (out, k0, k1) (stackAt (s0.sp - 32#64) extHookStack) hpc hrun hsp ?_ (fun sf _ hpost => ?_)
    · simpa only [sessionStoreNewSpec, sessionStoreNewInitSpec, Spec.inImage, tlsKeysAt,
        stackAt_sessionStoreNew_frame_split, sepConj_assoc] using hpre
    · simp only [sessionStoreNewInitSpec, sessionStoreNewSpec, Spec.inImage,
        stackAt_sessionStoreNew_frame_split, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨⟨htr, _⟩, hpost⟩
      exact ⟨htr, hpost⟩

/-- Image-level initialized TLS path (`tag = 1#8`) for `<InMemIdentityKeyStore>::new` (`0x0c238`). -/
theorem identityStore_new_init_ok {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProg img C ctl abs)
      (entryOf img inMemIdentityKeyStoreNewName)
      (identityStoreNewInitSpec img) := by
  apply root_of_tripleRatchetProgAt himg
  refine subroutine_ok_refine
    (identityStore_new_init_base_ok img.base C ctl abs (base_aligned_of_loads himg))
    fun ⟨out, kpPtr, kpBytes, regId, k0, k1⟩ R s0 hpre => ?_
  rw [identityStoreNewInitSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, _⟩, hpre⟩
  dsimp only at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  have hro := storeNewRoDataAt_intro himg hF hpre
  refine ⟨⟨out, kpPtr, kpBytes, regId, tlsKeysTpoff, img.base + emptyCtrlOff, k0, k1⟩,
    ?_, fun sf hpost => ?_⟩
  · simp only [identityStoreNewInitBaseSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, by simpa only [sepConj_assoc] using hro⟩
  · simp only [identityStoreNewInitBaseSpec, identityStoreNewInitSpec, Spec.inImage,
      sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hpure', hpost⟩
    exact ⟨hpure', Satisfies.drop_left hpost⟩

/-- Image-level uninitialized TLS path (`tag ≠ 1#8`) for `<InMemIdentityKeyStore>::new` (`0x0c238`). -/
theorem identityStore_new_uninit_ok {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hRk : HookSat abs randomKeysName randomKeysSpec) :
    subroutine_ok (tripleRatchetProg img C ctl abs)
      (entryOf img inMemIdentityKeyStoreNewName)
      (identityStoreNewUninitSpec img) := by
  apply root_of_tripleRatchetProgAt himg
  refine subroutine_ok_refine
    (identityStore_new_uninit_base_ok img.base C ctl abs (base_aligned_of_loads himg) hRk)
    fun ⟨out, kpPtr, kpBytes, regId, k0Old, k1Old, tag⟩ R s0 hpre => ?_
  rw [identityStoreNewUninitSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, _⟩, hpre⟩
  dsimp only at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  have hro := storeNewRoDataAt_intro himg hF hpre
  refine ⟨⟨out, kpPtr, kpBytes, regId, tlsKeysTpoff, img.base + emptyCtrlOff, k0Old, k1Old, tag⟩,
    ?_, fun sf hpost => ?_⟩
  · simp only [identityStoreNewUninitBaseSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, by simpa only [sepConj_assoc] using hro⟩
  · simp only [identityStoreNewUninitBaseSpec, identityStoreNewUninitSpec, Spec.inImage,
      sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hpure', hpost⟩
    exact ⟨hpure', Satisfies.drop_left hpost⟩

/-- Unified image-level contract (`st : Option (BitVec 64 × BitVec 64)`) for
`<InMemIdentityKeyStore>::new` (`0x0c238`). -/
theorem identityStore_new_ok {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hRk : HookSat abs randomKeysName randomKeysSpec) :
    subroutine_ok (tripleRatchetProg img C ctl abs)
      (entryOf img inMemIdentityKeyStoreNewName)
      (identityStoreNewSpec img) := by
  refine subroutine_ok_intro fun ⟨out, kpPtr, kpBytes, regId, st⟩ R s0 hpc hrun hpre hsp => ?_
  cases st with
  | none =>
    simp only [identityStoreNewSpec, Spec.inImage, tlsKeysAt, tlsKeysUninitAt,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
    rcases hpre with ⟨k0Old, k1Old, tag, hpre⟩
    refine reaches_of_ghost (identityStore_new_uninit_ok himg hRk)
      (out, kpPtr, kpBytes, regId, k0Old, k1Old, tag) emp hpc hrun hsp ?_ (fun sf _ hpost => ?_)
    · simp only [identityStoreNewUninitSpec, Spec.inImage, emp_sepConj,
        sepConj_assoc, pointsToBytes_sepConj_pure, memRegion_sepConj_pure,
        satisfies_pure_sepConj] at hpre ⊢
      rcases hpre with ⟨himg_ok, ⟨hx8, hx0, hx1, hlen⟩, htag, hmem⟩
      exact ⟨himg_ok, ⟨hx8, hx0, hx1, hlen, htag⟩, hmem⟩
    · simpa only [identityStoreNewUninitSpec, identityStoreNewSpec, Spec.inImage,
        emp_sepConj, sepConj_assoc] using hpost
  | some ks =>
    rcases ks with ⟨k0, k1⟩
    refine reaches_of_ghost (identityStore_new_init_ok himg)
      (out, kpPtr, kpBytes, regId, k0, k1) (stackAt (s0.sp - 48#64) extHookStack) hpc hrun hsp
      ?_ (fun sf _ hpost => ?_)
    · simpa only [identityStoreNewSpec, identityStoreNewInitSpec, Spec.inImage, tlsKeysAt,
        stackAt_identityStoreNew_frame_split, sepConj_assoc] using hpre
    · simp only [identityStoreNewInitSpec, identityStoreNewSpec, Spec.inImage,
        stackAt_identityStoreNew_frame_split, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨⟨htr, _⟩, hpost⟩
      exact ⟨htr, hpost⟩

end CryptoVerification.E2E.StoreNew



