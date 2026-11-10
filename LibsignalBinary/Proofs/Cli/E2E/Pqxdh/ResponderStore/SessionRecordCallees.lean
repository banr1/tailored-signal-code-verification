/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.SessionRecordCallees
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# CLI `SessionRecord` Callee Contracts

Subroutine contracts for `SessionRecord::archive_current_state_inner` (empty-session fast path) and
the `try_decrypt_from_record::<signal_session_handshake::Coins>::{closure#0}` log-filter check in
the CLI binary.
-/

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.ResponderStore

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000

set_option maxHeartbeats 2000000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "cells_unfold_fast" : tactic =>
  `(tactic| simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub])

/-! ## `SessionRecord::archive_current_state_inner` (empty-session fast path) -/

abbrev _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplName : String :=
  "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>"

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.drop_process_prekey_impl_state1_ok_trap {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplName)
      dropProcessPrekeyImplState1Spec := by
  unfold dropProcessPrekeyImplState1Spec
  cells_unfold
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplName = (ls_off% "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>")
  responder_fetches_from_cli b (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>") 0 368
  wp_init ptr s0
  examples_generalize_entry
  examples_hide_fetches
  subst h
  wp_steps
  wp_done

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.drop_process_prekey_impl_state1_ok {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplName)
      dropProcessPrekeyImplState1Spec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplName]
  exact subroutine_ok_kit_of_trTrap CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.drop_process_prekey_impl_state1_ok_trap

/-! ## `try_decrypt_from_record::<Coins>::{closure#0}` (log-disabled fast path) -/

abbrev _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName : String :=
  "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}"

private theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName = (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}") :=
  (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}")

private theorem stackAt_pqxdhClosure (sp : BitVec 64) :
    stackAt sp pqxdhClosureStack =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 432#64) ↦₆₄ v0) ∗ ((sp - 424#64) ↦₆₄ v1) ∗
        ((sp - 416#64) ↦₆₄ v2) ∗ ((sp - 408#64) ↦₆₄ v3)) ∗
      stackAt (sp - 96#64) 304 ∗
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
       ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗ ((sp - 80#64) ↦₆₄ w2) ∗
        ((sp - 72#64) ↦₆₄ w3) ∗ ((sp - 64#64) ↦₆₄ w4) ∗ ((sp - 56#64) ↦₆₄ w5) ∗
        ((sp - 48#64) ↦₆₄ w6) ∗ ((sp - 40#64) ↦₆₄ w7) ∗ ((sp - 32#64) ↦₆₄ w8) ∗
        ((sp - 24#64) ↦₆₄ w9) ∗ ((sp - 16#64) ↦₆₄ w10) ∗ ((sp - 8#64) ↦₆₄ w11)) := by
  have h1 := ProofLib.stackAt_split_cells sp 336 12 (by decide)
  have h2 := stackAt_split_bottom (sp - 96#64) 304 32 (by decide)
  have hsub : (sp - 96#64) - BitVec.ofNat 64 (304 + 32) = sp - 432#64 := by
    rw [BitVec.sub_sub]; rfl
  rw [hsub, show (32 : Nat) = 8 * 4 by rfl,
      ProofLib.memRegion_cells (sp - 432#64) 4 (by decide)] at h2
  change stackAt sp pqxdhClosureStack = stackAt (sp - 96#64) 336 ∗ cells (sp - 96#64) 12 at h1
  have hc4 : cells (sp - 432#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 432#64) ↦₆₄ v0) ∗ ((sp - 424#64) ↦₆₄ v1) ∗
        ((sp - 416#64) ↦₆₄ v2) ∗ ((sp - 408#64) ↦₆₄ v3)) := by
    cells_unfold
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
       ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗ ((sp - 80#64) ↦₆₄ w2) ∗
        ((sp - 72#64) ↦₆₄ w3) ∗ ((sp - 64#64) ↦₆₄ w4) ∗ ((sp - 56#64) ↦₆₄ w5) ∗
        ((sp - 48#64) ↦₆₄ w6) ∗ ((sp - 40#64) ↦₆₄ w7) ∗ ((sp - 32#64) ↦₆₄ w8) ∗
        ((sp - 24#64) ↦₆₄ w9) ∗ ((sp - 16#64) ↦₆₄ w10) ∗ ((sp - 8#64) ↦₆₄ w11)) := by
    cells_unfold
  rw [h1, h2, hc4, hc12, sepConj_assoc]

private theorem pqxdhLogClosure_adrp_addr_eq {base entry : BitVec 64}
    (hb : base &&& 0xfff#64 = 0#64) (he : entry = base + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}"))) :
    (((entry + 36#64) &&& 18446744073709547520#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - (page% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}" + 36)))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) = base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
  subst he; bv_arith

def _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.PqxdhLogClosureOk_trap
    (img : Obj.Image) (C : Crypto) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName)
    ((pqxdhLogClosureSpec img).inImage img)

def _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.PqxdhLogClosureOk (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName)
    ((pqxdhLogClosureSpec img).inImage img)

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdh_log_closure_ok_trap
    {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.PqxdhLogClosureOk_trap img C abs := by
  unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.PqxdhLogClosureOk_trap
  simp only [Spec.inImage, pqxdhLogClosureSpec, logOff, logFilterAddr, stackAt_pqxdhClosure,
    sepExists_sepConj_left, sepExists_sepConj_right]
  unfold trTrapProgAt
  have hfn := CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName_fnOff
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hentry : (libsignalSessionCode.rebase img.base
      (Rust.withPanics (trTrapExterns C abs))).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName =
      img.base + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, hfn]
  have hadrp := pqxdhLogClosure_adrp_addr_eq hb hentry
  clear hentry
  responder_fetches_from_cli img.base
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}") 0 56
  responder_fetches_from_cli img.base
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}") 784 32
  clear hfn himg
  generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (trTrapExterns C abs))).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName = entry
  wp_init x s0
  examples_hide_fetches
  wp_steps
  wp_done

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdh_log_closure_ok {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.PqxdhLogClosureOk img C ctl abs := by
  unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.PqxdhLogClosureOk
  rw [← (trapsOnly_trTrap_kit img.base C ctl abs).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName]
  exact subroutine_ok_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdh_log_closure_ok_trap himg)

end CryptoVerification.E2E.Pqxdh.ResponderStore
