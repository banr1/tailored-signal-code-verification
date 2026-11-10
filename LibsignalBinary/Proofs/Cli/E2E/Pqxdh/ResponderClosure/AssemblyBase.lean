/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP2a
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
public import ProofLib.SepLogic.WP
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP2a
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.ErrExit
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Responder Closure `.rodata`, Vtable, and Stage P2/P3 Segment Steps

`.rodata` `"decryption failed"` and `.data.rel.ro` vtable helpers, Stage P3 version-dispatch
and version-mismatch error basic-block `SepWP` lemmas, and Stage P2 zero-capacity signature
segment specializations for `message_decrypt_prekey::<Coins>::{closure#0}`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalSession

open CryptoVerification.E2E.Pqxdh.WireEntries

open CryptoVerification.E2E.Pqxdh.ResponderStore

set_option maxRecDepth 200000

set_option maxHeartbeats 1600000

set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

/-! ## 1. `.rodata` `"decryption failed"` Intro & `.data.rel.ro` Vtable Bundle -/

set_option maxRecDepth 2000000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.rodata_0x87350_eq :
    (libsignalSessionImage.data.drop (num% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964)) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 0x6974707972636564#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
open ProofLib.ObjectLoad in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.rodata_0x87350_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) ↦₆₄ᵣ 0x6974707972636564#64) ∗ P := by
  have hh := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) (n := 8) (bs := unpack64 0x6974707972636564#64)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
    (unpack64_length _) CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.rodata_0x87350_eq
  obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
  rw [unpack64_length] at hRO hread
  exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP

set_option maxRecDepth 2000000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.rodata_0x87358_eq :
    (libsignalSessionImage.data.drop (num% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 0x656c696166206e6f#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
open ProofLib.ObjectLoad in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.rodata_0x87358_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8)) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗ P := by
  have hh := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8)) (n := 8) (bs := unpack64 0x656c696166206e6f#64)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
    (unpack64_length _) CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.rodata_0x87358_eq
  obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
  rw [unpack64_length] at hRO hread
  exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP

local macro "cells_unfold_26" : tactic =>
  `(tactic| simp (config := { maxSteps := 1000000 }) (disch := decide) only [
    ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero, sepConj_emp,
    sepExists_sepConj_right] at *)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_rodata_0x1e08 {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64) (he : entry = b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"))) :
    ((entry + 7688#64 &&& 18446744073709547520#64) + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7688) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7692)) - (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7688))) = b + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7688) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7692)))) ∧
    ((((bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) + (b + 0x1e08#64)) &&& 0xfffffffffffff000#64) + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7688) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7692)) - (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7688))) = b + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7688) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7692)))) := by
  refine ⟨?_, ?_⟩
  · rw [he, BitVec.add_assoc, ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]; rfl
  · rw [← BitVec.add_assoc, BitVec.add_comm _ b, BitVec.add_assoc,
        ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]
    rfl

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_logLevel_0x3080 {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64) (he : entry = b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"))) :
    ((entry + 12416#64 &&& 18446744073709547520#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 12416))) = b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) ∧
    ((((bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) + (b + 0x3080#64)) &&& 0xfffffffffffff000#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 12416))) = b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) := by
  refine ⟨?_, ?_⟩
  · rw [he, BitVec.add_assoc, ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]; rfl
  · rw [← BitVec.add_assoc, BitVec.add_comm _ b, BitVec.add_assoc,
        ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]
    rfl

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_rodata_0x33bc {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64) (he : entry = b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"))) :
    ((entry + 13244#64 &&& 18446744073709547520#64) + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964)) - (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 13244))) = b + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964)))) ∧
    ((((bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) + (b + 0x33bc#64)) &&& 0xfffffffffffff000#64) + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964)) - (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 13244))) = b + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964)))) := by
  refine ⟨?_, ?_⟩
  · rw [he, BitVec.add_assoc, ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]; rfl
  · rw [← BitVec.add_assoc, BitVec.add_comm _ b, BitVec.add_assoc,
        ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]
    rfl

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg6_v4_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr locIdLen newLocIdPtr remIdLen newRemIdPtr newRootKeyPtr
    v08 v10 v18 v38 v40
    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    remAddrPtr locAddrPtr whisperMsgPtr
    ua90 ua98 uaa0 uaa8 uab0 uab8 uac0 uac8 uad0 uad8 uae0 uae8
    uaf0 uaf8 ub00 ub08 ub10 ub18 ub20 ub28 ub30 ub38 ub40 ub48
    ub50 ub58 ub60 ub68 ub70 ub78 ub80 ub88 ub90 ub98
    uba8 ubb8 ubc0 ubc8 : BitVec 64)
    (v24 v28 v2c f248 f24c prevCounter
    uba0 uba4 ubb0 ubd0 ubd8 ubdc ube0 ube4 : BitVec 32)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs) (b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) s
      (((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
       ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗
       ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
       ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
       ((s.sp + 0x38#64) ↦₆₄ v38) ∗ ((s.sp + 0x40#64) ↦₆₄ v40) ∗
       ((s.sp + 0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
       ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
       ((s.sp + 0x68#64) ↦₆₄ remIdLen) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
       ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
       ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗
       ((s.sp + 0xd0#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x930#64) ↦₆₄ c1) ∗ ((s.sp + 0x938#64) ↦₆₄ c2) ∗
       ((s.sp + 0x940#64) ↦₆₄ c3) ∗ ((s.sp + 0x948#64) ↦₆₄ c4) ∗
       ((s.sp + 0x950#64) ↦₆₄ c5) ∗ ((s.sp + 0x958#64) ↦₆₄ c6) ∗
       ((s.sp + 0x960#64) ↦₆₄ c7) ∗ ((s.sp + 0x968#64) ↦₆₄ c8) ∗
       ((s.sp + 0x970#64) ↦₆₄ c9) ∗ ((s.sp + 0x978#64) ↦₆₄ c10) ∗
       ((s.sp + 0x980#64) ↦₆₄ c11) ∗ ((s.sp + 0x988#64) ↦₆₄ c12) ∗
       ((s.sp + 0xa90#64) ↦₆₄ ua90) ∗ ((s.sp + 0xa98#64) ↦₆₄ ua98) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ uaa0) ∗ ((s.sp + 0xaa8#64) ↦₆₄ uaa8) ∗
       ((s.sp + 0xab0#64) ↦₆₄ uab0) ∗ ((s.sp + 0xab8#64) ↦₆₄ uab8) ∗
       ((s.sp + 0xac0#64) ↦₆₄ uac0) ∗ ((s.sp + 0xac8#64) ↦₆₄ uac8) ∗
       ((s.sp + 0xad0#64) ↦₆₄ uad0) ∗ ((s.sp + 0xad8#64) ↦₆₄ uad8) ∗
       ((s.sp + 0xae0#64) ↦₆₄ uae0) ∗ ((s.sp + 0xae8#64) ↦₆₄ uae8) ∗
       ((s.sp + 0xaf0#64) ↦₆₄ uaf0) ∗ ((s.sp + 0xaf8#64) ↦₆₄ uaf8) ∗
       ((s.sp + 0xb00#64) ↦₆₄ ub00) ∗ ((s.sp + 0xb08#64) ↦₆₄ ub08) ∗
       ((s.sp + 0xb10#64) ↦₆₄ ub10) ∗ ((s.sp + 0xb18#64) ↦₆₄ ub18) ∗
       ((s.sp + 0xb20#64) ↦₆₄ ub20) ∗ ((s.sp + 0xb28#64) ↦₆₄ ub28) ∗
       ((s.sp + 0xb30#64) ↦₆₄ ub30) ∗ ((s.sp + 0xb38#64) ↦₆₄ ub38) ∗
       ((s.sp + 0xb40#64) ↦₆₄ ub40) ∗ ((s.sp + 0xb48#64) ↦₆₄ ub48) ∗
       ((s.sp + 0xb50#64) ↦₆₄ ub50) ∗ ((s.sp + 0xb58#64) ↦₆₄ ub58) ∗
       ((s.sp + 0xb60#64) ↦₆₄ ub60) ∗ ((s.sp + 0xb68#64) ↦₆₄ ub68) ∗
       ((s.sp + 0xb70#64) ↦₆₄ ub70) ∗ ((s.sp + 0xb78#64) ↦₆₄ ub78) ∗
       ((s.sp + 0xb80#64) ↦₆₄ ub80) ∗ ((s.sp + 0xb88#64) ↦₆₄ ub88) ∗
       ((s.sp + 0xb90#64) ↦₆₄ ub90) ∗ ((s.sp + 0xb98#64) ↦₆₄ ub98) ∗
       ((s.sp + 0xba0#64) ↦₃₂ uba0) ∗ ((s.sp + 0xba4#64) ↦₃₂ uba4) ∗
       ((s.sp + 0xba8#64) ↦₆₄ uba8) ∗ ((s.sp + 0xbb0#64) ↦₃₂ ubb0) ∗
       ((s.sp + 0xbb8#64) ↦₆₄ ubb8) ∗ ((s.sp + 0xbc0#64) ↦₆₄ ubc0) ∗ ((s.sp + 0xbc8#64) ↦₆₄ ubc8) ∗
       ((s.sp + 0xbd0#64) ↦₃₂ ubd0) ∗ ((s.sp + 0xbd8#64) ↦₃₂ ubd8) ∗
       ((s.sp + 0xbdc#64) ↦₃₂ ubdc) ∗ ((s.sp + 0xbe0#64) ↦₃₂ ube0) ∗
       ((s.sp + 0xbe4#64) ↦₃₂ ube4))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
          ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗
          ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
          ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
          ((s.sp + 0x38#64) ↦₆₄ v38) ∗ ((s.sp + 0x40#64) ↦₆₄ v40) ∗
          ((s.sp + 0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
          ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
          ((s.sp + 0x68#64) ↦₆₄ remIdLen) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
          ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
          ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗
          ((s.sp + 0xd0#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x930#64) ↦₆₄ c1) ∗ ((s.sp + 0x938#64) ↦₆₄ c2) ∗
          ((s.sp + 0x940#64) ↦₆₄ c3) ∗ ((s.sp + 0x948#64) ↦₆₄ c4) ∗
          ((s.sp + 0x950#64) ↦₆₄ c5) ∗ ((s.sp + 0x958#64) ↦₆₄ c6) ∗
          ((s.sp + 0x960#64) ↦₆₄ c7) ∗ ((s.sp + 0x968#64) ↦₆₄ c8) ∗
          ((s.sp + 0x970#64) ↦₆₄ c9) ∗ ((s.sp + 0x978#64) ↦₆₄ c10) ∗
          ((s.sp + 0x980#64) ↦₆₄ c11) ∗ ((s.sp + 0x988#64) ↦₆₄ c12) ∗
          ((s.sp + 0xa90#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0xa98#64) ↦₆₄ newLocIdPtr) ∗
          ((s.sp + 0xaa0#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0xaa8#64) ↦₆₄ remIdLen) ∗
          ((s.sp + 0xab0#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0xab8#64) ↦₆₄ remIdLen) ∗
          ((s.sp + 0xac0#64) ↦₆₄ s.readReg64 .x28) ∗ ((s.sp + 0xac8#64) ↦₆₄ newRootKeyPtr) ∗
          ((s.sp + 0xad0#64) ↦₆₄ s.readReg64 .x28) ∗ ((s.sp + 0xad8#64) ↦₆₄ v40) ∗
          ((s.sp + 0xae0#64) ↦₆₄ s.readReg64 .x25) ∗ ((s.sp + 0xae8#64) ↦₆₄ v40) ∗
          ((s.sp + 0xaf0#64) ↦₆₄ s.readReg64 .x24) ∗ ((s.sp + 0xaf8#64) ↦₆₄ s.readReg64 .x23) ∗
          ((s.sp + 0xb00#64) ↦₆₄ s.readReg64 .x24) ∗ ((s.sp + 0xb08#64) ↦₆₄ s.readReg64 .x26) ∗
          ((s.sp + 0xb10#64) ↦₆₄ s.readReg64 .x21) ∗ ((s.sp + 0xb18#64) ↦₆₄ s.readReg64 .x26) ∗
          ((s.sp + 0xb20#64) ↦₆₄ c0) ∗ ((s.sp + 0xb28#64) ↦₆₄ c1) ∗
          ((s.sp + 0xb30#64) ↦₆₄ c2) ∗ ((s.sp + 0xb38#64) ↦₆₄ c3) ∗
          ((s.sp + 0xb40#64) ↦₆₄ c4) ∗ ((s.sp + 0xb48#64) ↦₆₄ c5) ∗
          ((s.sp + 0xb50#64) ↦₆₄ c6) ∗ ((s.sp + 0xb58#64) ↦₆₄ c7) ∗
          ((s.sp + 0xb60#64) ↦₆₄ c8) ∗ ((s.sp + 0xb68#64) ↦₆₄ c9) ∗
          ((s.sp + 0xb70#64) ↦₆₄ c10) ∗ ((s.sp + 0xb78#64) ↦₆₄ c11) ∗
          ((s.sp + 0xb80#64) ↦₆₄ c12) ∗ ((s.sp + 0xb88#64) ↦₆₄ s.readReg64 .x22) ∗
          ((s.sp + 0xb90#64) ↦₆₄ v18) ∗ ((s.sp + 0xb98#64) ↦₆₄ s.readReg64 .x22) ∗
          ((s.sp + 0xba0#64) ↦₃₂ v2c) ∗ ((s.sp + 0xba4#64) ↦₃₂ (s.readReg64 .x20).truncate 32) ∗
          ((s.sp + 0xba8#64) ↦₆₄ v10) ∗ ((s.sp + 0xbb0#64) ↦₃₂ v28) ∗
          ((s.sp + 0xbb8#64) ↦₆₄ v38) ∗ ((s.sp + 0xbc0#64) ↦₆₄ v08) ∗ ((s.sp + 0xbc8#64) ↦₆₄ v38) ∗
          ((s.sp + 0xbd0#64) ↦₃₂ v24) ∗ ((s.sp + 0xbd8#64) ↦₃₂ 4#32) ∗
          ((s.sp + 0xbdc#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0xbe0#64) ↦₃₂ f248) ∗
          ((s.sp + 0xbe4#64) ↦₃₂ f24c)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x270#64 ∧
        s1.readReg64 .x1 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x2 = remAddrPtr ∧
        s1.readReg64 .x3 = locAddrPtr ∧
        s1.readReg64 .x4 = whisperMsgPtr ∧
        s1.readReg64 .x5 = 3#64 ∧
        s1.readReg64 .x6 = 0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1bac 0x1cd4
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
      0x1cd4#64 + bv% ((2^64 + ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7380)) % 2^64) = b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment P3.6_v4 (`+0x1bac -> Coins>`, `0x4cc78 -> try_decrypt_with_state`): Stores the cloned `SessionState` (`344` B) into `sp + 0xa90..0xbe8`, checks
`session_version = 4 == 4 = message_version`, loads `x0 = sp + 0x270`, `x1 = sp + 0xa90`,
`x2 = [sp + 0x3a0]`, `x3 = [sp + 0xa0]`, `x4 = [sp + 0xb0]`, `x5 = 3#64`, `x6 = 0#64`,
and calls `bl -19688` (`Coins>`, `try_decrypt_with_state`) at `+0x1cd4`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg6_v4_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr locIdLen newLocIdPtr remIdLen newRemIdPtr newRootKeyPtr
    v08 v10 v18 v38 v40
    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    remAddrPtr locAddrPtr whisperMsgPtr
    ua90 ua98 uaa0 uaa8 uab0 uab8 uac0 uac8 uad0 uad8 uae0 uae8
    uaf0 uaf8 ub00 ub08 ub10 ub18 ub20 ub28 ub30 ub38 ub40 ub48
    ub50 ub58 ub60 ub68 ub70 ub78 ub80 ub88 ub90 ub98
    uba8 ubb8 ubc0 ubc8 : BitVec 64)
    (v24 v28 v2c f248 f24c prevCounter
    uba0 uba4 ubb0 ubd0 ubd8 ubdc ube0 ube4 : BitVec 32)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) (b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) s
      (((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
       ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗
       ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
       ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
       ((s.sp + 0x38#64) ↦₆₄ v38) ∗ ((s.sp + 0x40#64) ↦₆₄ v40) ∗
       ((s.sp + 0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
       ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
       ((s.sp + 0x68#64) ↦₆₄ remIdLen) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
       ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
       ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗
       ((s.sp + 0xd0#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x930#64) ↦₆₄ c1) ∗ ((s.sp + 0x938#64) ↦₆₄ c2) ∗
       ((s.sp + 0x940#64) ↦₆₄ c3) ∗ ((s.sp + 0x948#64) ↦₆₄ c4) ∗
       ((s.sp + 0x950#64) ↦₆₄ c5) ∗ ((s.sp + 0x958#64) ↦₆₄ c6) ∗
       ((s.sp + 0x960#64) ↦₆₄ c7) ∗ ((s.sp + 0x968#64) ↦₆₄ c8) ∗
       ((s.sp + 0x970#64) ↦₆₄ c9) ∗ ((s.sp + 0x978#64) ↦₆₄ c10) ∗
       ((s.sp + 0x980#64) ↦₆₄ c11) ∗ ((s.sp + 0x988#64) ↦₆₄ c12) ∗
       ((s.sp + 0xa90#64) ↦₆₄ ua90) ∗ ((s.sp + 0xa98#64) ↦₆₄ ua98) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ uaa0) ∗ ((s.sp + 0xaa8#64) ↦₆₄ uaa8) ∗
       ((s.sp + 0xab0#64) ↦₆₄ uab0) ∗ ((s.sp + 0xab8#64) ↦₆₄ uab8) ∗
       ((s.sp + 0xac0#64) ↦₆₄ uac0) ∗ ((s.sp + 0xac8#64) ↦₆₄ uac8) ∗
       ((s.sp + 0xad0#64) ↦₆₄ uad0) ∗ ((s.sp + 0xad8#64) ↦₆₄ uad8) ∗
       ((s.sp + 0xae0#64) ↦₆₄ uae0) ∗ ((s.sp + 0xae8#64) ↦₆₄ uae8) ∗
       ((s.sp + 0xaf0#64) ↦₆₄ uaf0) ∗ ((s.sp + 0xaf8#64) ↦₆₄ uaf8) ∗
       ((s.sp + 0xb00#64) ↦₆₄ ub00) ∗ ((s.sp + 0xb08#64) ↦₆₄ ub08) ∗
       ((s.sp + 0xb10#64) ↦₆₄ ub10) ∗ ((s.sp + 0xb18#64) ↦₆₄ ub18) ∗
       ((s.sp + 0xb20#64) ↦₆₄ ub20) ∗ ((s.sp + 0xb28#64) ↦₆₄ ub28) ∗
       ((s.sp + 0xb30#64) ↦₆₄ ub30) ∗ ((s.sp + 0xb38#64) ↦₆₄ ub38) ∗
       ((s.sp + 0xb40#64) ↦₆₄ ub40) ∗ ((s.sp + 0xb48#64) ↦₆₄ ub48) ∗
       ((s.sp + 0xb50#64) ↦₆₄ ub50) ∗ ((s.sp + 0xb58#64) ↦₆₄ ub58) ∗
       ((s.sp + 0xb60#64) ↦₆₄ ub60) ∗ ((s.sp + 0xb68#64) ↦₆₄ ub68) ∗
       ((s.sp + 0xb70#64) ↦₆₄ ub70) ∗ ((s.sp + 0xb78#64) ↦₆₄ ub78) ∗
       ((s.sp + 0xb80#64) ↦₆₄ ub80) ∗ ((s.sp + 0xb88#64) ↦₆₄ ub88) ∗
       ((s.sp + 0xb90#64) ↦₆₄ ub90) ∗ ((s.sp + 0xb98#64) ↦₆₄ ub98) ∗
       ((s.sp + 0xba0#64) ↦₃₂ uba0) ∗ ((s.sp + 0xba4#64) ↦₃₂ uba4) ∗
       ((s.sp + 0xba8#64) ↦₆₄ uba8) ∗ ((s.sp + 0xbb0#64) ↦₃₂ ubb0) ∗
       ((s.sp + 0xbb8#64) ↦₆₄ ubb8) ∗ ((s.sp + 0xbc0#64) ↦₆₄ ubc0) ∗ ((s.sp + 0xbc8#64) ↦₆₄ ubc8) ∗
       ((s.sp + 0xbd0#64) ↦₃₂ ubd0) ∗ ((s.sp + 0xbd8#64) ↦₃₂ ubd8) ∗
       ((s.sp + 0xbdc#64) ↦₃₂ ubdc) ∗ ((s.sp + 0xbe0#64) ↦₃₂ ube0) ∗
       ((s.sp + 0xbe4#64) ↦₃₂ ube4))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
          ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗
          ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
          ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
          ((s.sp + 0x38#64) ↦₆₄ v38) ∗ ((s.sp + 0x40#64) ↦₆₄ v40) ∗
          ((s.sp + 0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
          ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
          ((s.sp + 0x68#64) ↦₆₄ remIdLen) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
          ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
          ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗
          ((s.sp + 0xd0#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x930#64) ↦₆₄ c1) ∗ ((s.sp + 0x938#64) ↦₆₄ c2) ∗
          ((s.sp + 0x940#64) ↦₆₄ c3) ∗ ((s.sp + 0x948#64) ↦₆₄ c4) ∗
          ((s.sp + 0x950#64) ↦₆₄ c5) ∗ ((s.sp + 0x958#64) ↦₆₄ c6) ∗
          ((s.sp + 0x960#64) ↦₆₄ c7) ∗ ((s.sp + 0x968#64) ↦₆₄ c8) ∗
          ((s.sp + 0x970#64) ↦₆₄ c9) ∗ ((s.sp + 0x978#64) ↦₆₄ c10) ∗
          ((s.sp + 0x980#64) ↦₆₄ c11) ∗ ((s.sp + 0x988#64) ↦₆₄ c12) ∗
          ((s.sp + 0xa90#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0xa98#64) ↦₆₄ newLocIdPtr) ∗
          ((s.sp + 0xaa0#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0xaa8#64) ↦₆₄ remIdLen) ∗
          ((s.sp + 0xab0#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0xab8#64) ↦₆₄ remIdLen) ∗
          ((s.sp + 0xac0#64) ↦₆₄ s.readReg64 .x28) ∗ ((s.sp + 0xac8#64) ↦₆₄ newRootKeyPtr) ∗
          ((s.sp + 0xad0#64) ↦₆₄ s.readReg64 .x28) ∗ ((s.sp + 0xad8#64) ↦₆₄ v40) ∗
          ((s.sp + 0xae0#64) ↦₆₄ s.readReg64 .x25) ∗ ((s.sp + 0xae8#64) ↦₆₄ v40) ∗
          ((s.sp + 0xaf0#64) ↦₆₄ s.readReg64 .x24) ∗ ((s.sp + 0xaf8#64) ↦₆₄ s.readReg64 .x23) ∗
          ((s.sp + 0xb00#64) ↦₆₄ s.readReg64 .x24) ∗ ((s.sp + 0xb08#64) ↦₆₄ s.readReg64 .x26) ∗
          ((s.sp + 0xb10#64) ↦₆₄ s.readReg64 .x21) ∗ ((s.sp + 0xb18#64) ↦₆₄ s.readReg64 .x26) ∗
          ((s.sp + 0xb20#64) ↦₆₄ c0) ∗ ((s.sp + 0xb28#64) ↦₆₄ c1) ∗
          ((s.sp + 0xb30#64) ↦₆₄ c2) ∗ ((s.sp + 0xb38#64) ↦₆₄ c3) ∗
          ((s.sp + 0xb40#64) ↦₆₄ c4) ∗ ((s.sp + 0xb48#64) ↦₆₄ c5) ∗
          ((s.sp + 0xb50#64) ↦₆₄ c6) ∗ ((s.sp + 0xb58#64) ↦₆₄ c7) ∗
          ((s.sp + 0xb60#64) ↦₆₄ c8) ∗ ((s.sp + 0xb68#64) ↦₆₄ c9) ∗
          ((s.sp + 0xb70#64) ↦₆₄ c10) ∗ ((s.sp + 0xb78#64) ↦₆₄ c11) ∗
          ((s.sp + 0xb80#64) ↦₆₄ c12) ∗ ((s.sp + 0xb88#64) ↦₆₄ s.readReg64 .x22) ∗
          ((s.sp + 0xb90#64) ↦₆₄ v18) ∗ ((s.sp + 0xb98#64) ↦₆₄ s.readReg64 .x22) ∗
          ((s.sp + 0xba0#64) ↦₃₂ v2c) ∗ ((s.sp + 0xba4#64) ↦₃₂ (s.readReg64 .x20).truncate 32) ∗
          ((s.sp + 0xba8#64) ↦₆₄ v10) ∗ ((s.sp + 0xbb0#64) ↦₃₂ v28) ∗
          ((s.sp + 0xbb8#64) ↦₆₄ v38) ∗ ((s.sp + 0xbc0#64) ↦₆₄ v08) ∗ ((s.sp + 0xbc8#64) ↦₆₄ v38) ∗
          ((s.sp + 0xbd0#64) ↦₃₂ v24) ∗ ((s.sp + 0xbd8#64) ↦₃₂ 4#32) ∗
          ((s.sp + 0xbdc#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0xbe0#64) ↦₃₂ f248) ∗
          ((s.sp + 0xbe4#64) ↦₃₂ f24c)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x270#64 ∧
        s1.readReg64 .x1 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x2 = remAddrPtr ∧
        s1.readReg64 .x3 = locAddrPtr ∧
        s1.readReg64 .x4 = whisperMsgPtr ∧
        s1.readReg64 .x5 = 3#64 ∧
        s1.readReg64 .x6 = 0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg6_v4_wp_trap b C abs s
    coroPtr locIdLen newLocIdPtr remIdLen newRemIdPtr newRootKeyPtr
    v08 v10 v18 v38 v40 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    remAddrPtr locAddrPtr whisperMsgPtr
    ua90 ua98 uaa0 uaa8 uab0 uab8 uac0 uac8 uad0 uad8 uae0 uae8
    uaf0 uaf8 ub00 ub08 ub10 ub18 ub20 ub28 ub30 ub38 ub40 ub48
    ub50 ub58 ub60 ub68 ub70 ub78 ub80 ub88 ub90 ub98
    uba8 ubb8 ubc0 ubc8
    v24 v28 v2c f248 f24c prevCounter uba0 uba4 ubb0 ubd0 ubd8 ubdc ube0 ube4
    hpc hrun hsp_align hx19)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg6_ver_ne_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr locIdLen newLocIdPtr remIdLen newRemIdPtr newRootKeyPtr
    v08 v10 v18 v38 v40
    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    u3e0 ua90 ua98 uaa0 uaa8 uab0 uab8 uac0 uac8 uad0 uad8 uae0 uae8
    uaf0 uaf8 ub00 ub08 ub10 ub18 ub20 ub28 ub30 ub38 ub40 ub48
    ub50 ub58 ub60 ub68 ub70 ub78 ub80 ub88 ub90 ub98
    uba8 ubb8 ubc0 ubc8 : BitVec 64)
    (msgVer v24 v28 v2c f248 f24c prevCounter u3e8
    uba0 uba4 ubb0 ubd0 ubd8 ubdc ube0 ube4 : BitVec 32)
    (hb : b &&& 0xfff#64 = 0#64)
    (hver_ne : msgVer ≠ 4#32)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs) (b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}"))) s
      (((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
       ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗
       ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
       ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
       ((s.sp + 0x38#64) ↦₆₄ v38) ∗ ((s.sp + 0x40#64) ↦₆₄ v40) ∗
       ((s.sp + 0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
       ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
       ((s.sp + 0x68#64) ↦₆₄ remIdLen) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
       ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
       ((s.sp + 0xd0#64) ↦₆₄ locIdLen) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u3e0) ∗ ((s.sp + 0x3e8#64) ↦₃₂ u3e8) ∗
       ((s.sp + 0x930#64) ↦₆₄ c1) ∗ ((s.sp + 0x938#64) ↦₆₄ c2) ∗
       ((s.sp + 0x940#64) ↦₆₄ c3) ∗ ((s.sp + 0x948#64) ↦₆₄ c4) ∗
       ((s.sp + 0x950#64) ↦₆₄ c5) ∗ ((s.sp + 0x958#64) ↦₆₄ c6) ∗
       ((s.sp + 0x960#64) ↦₆₄ c7) ∗ ((s.sp + 0x968#64) ↦₆₄ c8) ∗
       ((s.sp + 0x970#64) ↦₆₄ c9) ∗ ((s.sp + 0x978#64) ↦₆₄ c10) ∗
       ((s.sp + 0x980#64) ↦₆₄ c11) ∗ ((s.sp + 0x988#64) ↦₆₄ c12) ∗
       ((s.sp + 0xa90#64) ↦₆₄ ua90) ∗ ((s.sp + 0xa98#64) ↦₆₄ ua98) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ uaa0) ∗ ((s.sp + 0xaa8#64) ↦₆₄ uaa8) ∗
       ((s.sp + 0xab0#64) ↦₆₄ uab0) ∗ ((s.sp + 0xab8#64) ↦₆₄ uab8) ∗
       ((s.sp + 0xac0#64) ↦₆₄ uac0) ∗ ((s.sp + 0xac8#64) ↦₆₄ uac8) ∗
       ((s.sp + 0xad0#64) ↦₆₄ uad0) ∗ ((s.sp + 0xad8#64) ↦₆₄ uad8) ∗
       ((s.sp + 0xae0#64) ↦₆₄ uae0) ∗ ((s.sp + 0xae8#64) ↦₆₄ uae8) ∗
       ((s.sp + 0xaf0#64) ↦₆₄ uaf0) ∗ ((s.sp + 0xaf8#64) ↦₆₄ uaf8) ∗
       ((s.sp + 0xb00#64) ↦₆₄ ub00) ∗ ((s.sp + 0xb08#64) ↦₆₄ ub08) ∗
       ((s.sp + 0xb10#64) ↦₆₄ ub10) ∗ ((s.sp + 0xb18#64) ↦₆₄ ub18) ∗
       ((s.sp + 0xb20#64) ↦₆₄ ub20) ∗ ((s.sp + 0xb28#64) ↦₆₄ ub28) ∗
       ((s.sp + 0xb30#64) ↦₆₄ ub30) ∗ ((s.sp + 0xb38#64) ↦₆₄ ub38) ∗
       ((s.sp + 0xb40#64) ↦₆₄ ub40) ∗ ((s.sp + 0xb48#64) ↦₆₄ ub48) ∗
       ((s.sp + 0xb50#64) ↦₆₄ ub50) ∗ ((s.sp + 0xb58#64) ↦₆₄ ub58) ∗
       ((s.sp + 0xb60#64) ↦₆₄ ub60) ∗ ((s.sp + 0xb68#64) ↦₆₄ ub68) ∗
       ((s.sp + 0xb70#64) ↦₆₄ ub70) ∗ ((s.sp + 0xb78#64) ↦₆₄ ub78) ∗
       ((s.sp + 0xb80#64) ↦₆₄ ub80) ∗ ((s.sp + 0xb88#64) ↦₆₄ ub88) ∗
       ((s.sp + 0xb90#64) ↦₆₄ ub90) ∗ ((s.sp + 0xb98#64) ↦₆₄ ub98) ∗
       ((s.sp + 0xba0#64) ↦₃₂ uba0) ∗ ((s.sp + 0xba4#64) ↦₃₂ uba4) ∗
       ((s.sp + 0xba8#64) ↦₆₄ uba8) ∗ ((s.sp + 0xbb0#64) ↦₃₂ ubb0) ∗
       ((s.sp + 0xbb8#64) ↦₆₄ ubb8) ∗ ((s.sp + 0xbc0#64) ↦₆₄ ubc0) ∗ ((s.sp + 0xbc8#64) ↦₆₄ ubc8) ∗
       ((s.sp + 0xbd0#64) ↦₃₂ ubd0) ∗ ((s.sp + 0xbd8#64) ↦₃₂ ubd8) ∗
       ((s.sp + 0xbdc#64) ↦₃₂ ubdc) ∗ ((s.sp + 0xbe0#64) ↦₃₂ ube0) ∗
       ((s.sp + 0xbe4#64) ↦₃₂ ube4))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
          ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗
          ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
          ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
          ((s.sp + 0x38#64) ↦₆₄ v38) ∗ ((s.sp + 0x40#64) ↦₆₄ v40) ∗
          ((s.sp + 0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
          ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
          ((s.sp + 0x68#64) ↦₆₄ remIdLen) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
          ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
          ((s.sp + 0xd0#64) ↦₆₄ locIdLen) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ 0x8000000000000006#64) ∗ ((s.sp + 0x3e8#64) ↦₃₂ msgVer) ∗
          ((s.sp + 0x930#64) ↦₆₄ c1) ∗ ((s.sp + 0x938#64) ↦₆₄ c2) ∗
          ((s.sp + 0x940#64) ↦₆₄ c3) ∗ ((s.sp + 0x948#64) ↦₆₄ c4) ∗
          ((s.sp + 0x950#64) ↦₆₄ c5) ∗ ((s.sp + 0x958#64) ↦₆₄ c6) ∗
          ((s.sp + 0x960#64) ↦₆₄ c7) ∗ ((s.sp + 0x968#64) ↦₆₄ c8) ∗
          ((s.sp + 0x970#64) ↦₆₄ c9) ∗ ((s.sp + 0x978#64) ↦₆₄ c10) ∗
          ((s.sp + 0x980#64) ↦₆₄ c11) ∗ ((s.sp + 0x988#64) ↦₆₄ c12) ∗
          ((s.sp + 0xa90#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0xa98#64) ↦₆₄ newLocIdPtr) ∗
          ((s.sp + 0xaa0#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0xaa8#64) ↦₆₄ remIdLen) ∗
          ((s.sp + 0xab0#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0xab8#64) ↦₆₄ remIdLen) ∗
          ((s.sp + 0xac0#64) ↦₆₄ s.readReg64 .x28) ∗ ((s.sp + 0xac8#64) ↦₆₄ newRootKeyPtr) ∗
          ((s.sp + 0xad0#64) ↦₆₄ s.readReg64 .x28) ∗ ((s.sp + 0xad8#64) ↦₆₄ v40) ∗
          ((s.sp + 0xae0#64) ↦₆₄ s.readReg64 .x25) ∗ ((s.sp + 0xae8#64) ↦₆₄ v40) ∗
          ((s.sp + 0xaf0#64) ↦₆₄ s.readReg64 .x24) ∗ ((s.sp + 0xaf8#64) ↦₆₄ s.readReg64 .x23) ∗
          ((s.sp + 0xb00#64) ↦₆₄ s.readReg64 .x24) ∗ ((s.sp + 0xb08#64) ↦₆₄ s.readReg64 .x26) ∗
          ((s.sp + 0xb10#64) ↦₆₄ s.readReg64 .x21) ∗ ((s.sp + 0xb18#64) ↦₆₄ s.readReg64 .x26) ∗
          ((s.sp + 0xb20#64) ↦₆₄ c0) ∗ ((s.sp + 0xb28#64) ↦₆₄ c1) ∗
          ((s.sp + 0xb30#64) ↦₆₄ c2) ∗ ((s.sp + 0xb38#64) ↦₆₄ c3) ∗
          ((s.sp + 0xb40#64) ↦₆₄ c4) ∗ ((s.sp + 0xb48#64) ↦₆₄ c5) ∗
          ((s.sp + 0xb50#64) ↦₆₄ c6) ∗ ((s.sp + 0xb58#64) ↦₆₄ c7) ∗
          ((s.sp + 0xb60#64) ↦₆₄ c8) ∗ ((s.sp + 0xb68#64) ↦₆₄ c9) ∗
          ((s.sp + 0xb70#64) ↦₆₄ c10) ∗ ((s.sp + 0xb78#64) ↦₆₄ c11) ∗
          ((s.sp + 0xb80#64) ↦₆₄ c12) ∗ ((s.sp + 0xb88#64) ↦₆₄ s.readReg64 .x22) ∗
          ((s.sp + 0xb90#64) ↦₆₄ v18) ∗ ((s.sp + 0xb98#64) ↦₆₄ s.readReg64 .x22) ∗
          ((s.sp + 0xba0#64) ↦₃₂ v2c) ∗ ((s.sp + 0xba4#64) ↦₃₂ (s.readReg64 .x20).truncate 32) ∗
          ((s.sp + 0xba8#64) ↦₆₄ v10) ∗ ((s.sp + 0xbb0#64) ↦₃₂ v28) ∗
          ((s.sp + 0xbb8#64) ↦₆₄ v38) ∗ ((s.sp + 0xbc0#64) ↦₆₄ v08) ∗ ((s.sp + 0xbc8#64) ↦₆₄ v38) ∗
          ((s.sp + 0xbd0#64) ↦₃₂ v24) ∗ ((s.sp + 0xbd8#64) ↦₃₂ 4#32) ∗
          ((s.sp + 0xbdc#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0xbe0#64) ↦₃₂ f248) ∗
          ((s.sp + 0xbe4#64) ↦₃₂ f24c)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3b0#64 ∧
        s1.readReg64 .x1 = b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7688) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7692)) ∧
        s1.readReg64 .x2 = 7#64 ∧
        s1.readReg64 .x3 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x4 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1e30#64) := by
  have hcond_ver := cond_ne_subs32_4_of_ne hver_ne
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1bac 0x1cb4
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1e04 0x1e2c
  dsimp only [trTrapProgAt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_rodata_0x1e08 hb hentry).1
  have hadrp := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_rodata_0x1e08 hb hentry).2
  have htarget : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
      0x1e2c#64 + 0x1990#64 = b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have h5ac6e : (b + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7688) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7692)))) + bv% ((ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7688) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7692)) % 4096) = b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7688) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7692)) := by bv_arith
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment P3.6_ver_ne (`+0x1bac -> {closure#0}`, `0x4cc78 -> 0x4ced0 -> logOrDrop`): When `session_version = 4#32 ≠ msgVer`, stores the cloned `SessionState` (`344` B) into
`sp + 0xa90..0xbe8`, branches at `0x4cd80` (`+0x1cb4`) to `0x4ced0` (`+0x1e04`), writes
`UnrecognizedMessageVersion` (`0x8000000000000006#64`, `msgVer`) to `sp + 0x3e0..0x3ec`,
and calls `bl {closure#0}` (`logOrDrop`) at `+0x1e2c`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg6_ver_ne_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr locIdLen newLocIdPtr remIdLen newRemIdPtr newRootKeyPtr
    v08 v10 v18 v38 v40
    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    u3e0 ua90 ua98 uaa0 uaa8 uab0 uab8 uac0 uac8 uad0 uad8 uae0 uae8
    uaf0 uaf8 ub00 ub08 ub10 ub18 ub20 ub28 ub30 ub38 ub40 ub48
    ub50 ub58 ub60 ub68 ub70 ub78 ub80 ub88 ub90 ub98
    uba8 ubb8 ubc0 ubc8 : BitVec 64)
    (msgVer v24 v28 v2c f248 f24c prevCounter u3e8
    uba0 uba4 ubb0 ubd0 ubd8 ubdc ube0 ube4 : BitVec 32)
    (hb : b &&& 0xfff#64 = 0#64)
    (hver_ne : msgVer ≠ 4#32)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) (b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}"))) s
      (((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
       ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗
       ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
       ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
       ((s.sp + 0x38#64) ↦₆₄ v38) ∗ ((s.sp + 0x40#64) ↦₆₄ v40) ∗
       ((s.sp + 0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
       ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
       ((s.sp + 0x68#64) ↦₆₄ remIdLen) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
       ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
       ((s.sp + 0xd0#64) ↦₆₄ locIdLen) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u3e0) ∗ ((s.sp + 0x3e8#64) ↦₃₂ u3e8) ∗
       ((s.sp + 0x930#64) ↦₆₄ c1) ∗ ((s.sp + 0x938#64) ↦₆₄ c2) ∗
       ((s.sp + 0x940#64) ↦₆₄ c3) ∗ ((s.sp + 0x948#64) ↦₆₄ c4) ∗
       ((s.sp + 0x950#64) ↦₆₄ c5) ∗ ((s.sp + 0x958#64) ↦₆₄ c6) ∗
       ((s.sp + 0x960#64) ↦₆₄ c7) ∗ ((s.sp + 0x968#64) ↦₆₄ c8) ∗
       ((s.sp + 0x970#64) ↦₆₄ c9) ∗ ((s.sp + 0x978#64) ↦₆₄ c10) ∗
       ((s.sp + 0x980#64) ↦₆₄ c11) ∗ ((s.sp + 0x988#64) ↦₆₄ c12) ∗
       ((s.sp + 0xa90#64) ↦₆₄ ua90) ∗ ((s.sp + 0xa98#64) ↦₆₄ ua98) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ uaa0) ∗ ((s.sp + 0xaa8#64) ↦₆₄ uaa8) ∗
       ((s.sp + 0xab0#64) ↦₆₄ uab0) ∗ ((s.sp + 0xab8#64) ↦₆₄ uab8) ∗
       ((s.sp + 0xac0#64) ↦₆₄ uac0) ∗ ((s.sp + 0xac8#64) ↦₆₄ uac8) ∗
       ((s.sp + 0xad0#64) ↦₆₄ uad0) ∗ ((s.sp + 0xad8#64) ↦₆₄ uad8) ∗
       ((s.sp + 0xae0#64) ↦₆₄ uae0) ∗ ((s.sp + 0xae8#64) ↦₆₄ uae8) ∗
       ((s.sp + 0xaf0#64) ↦₆₄ uaf0) ∗ ((s.sp + 0xaf8#64) ↦₆₄ uaf8) ∗
       ((s.sp + 0xb00#64) ↦₆₄ ub00) ∗ ((s.sp + 0xb08#64) ↦₆₄ ub08) ∗
       ((s.sp + 0xb10#64) ↦₆₄ ub10) ∗ ((s.sp + 0xb18#64) ↦₆₄ ub18) ∗
       ((s.sp + 0xb20#64) ↦₆₄ ub20) ∗ ((s.sp + 0xb28#64) ↦₆₄ ub28) ∗
       ((s.sp + 0xb30#64) ↦₆₄ ub30) ∗ ((s.sp + 0xb38#64) ↦₆₄ ub38) ∗
       ((s.sp + 0xb40#64) ↦₆₄ ub40) ∗ ((s.sp + 0xb48#64) ↦₆₄ ub48) ∗
       ((s.sp + 0xb50#64) ↦₆₄ ub50) ∗ ((s.sp + 0xb58#64) ↦₆₄ ub58) ∗
       ((s.sp + 0xb60#64) ↦₆₄ ub60) ∗ ((s.sp + 0xb68#64) ↦₆₄ ub68) ∗
       ((s.sp + 0xb70#64) ↦₆₄ ub70) ∗ ((s.sp + 0xb78#64) ↦₆₄ ub78) ∗
       ((s.sp + 0xb80#64) ↦₆₄ ub80) ∗ ((s.sp + 0xb88#64) ↦₆₄ ub88) ∗
       ((s.sp + 0xb90#64) ↦₆₄ ub90) ∗ ((s.sp + 0xb98#64) ↦₆₄ ub98) ∗
       ((s.sp + 0xba0#64) ↦₃₂ uba0) ∗ ((s.sp + 0xba4#64) ↦₃₂ uba4) ∗
       ((s.sp + 0xba8#64) ↦₆₄ uba8) ∗ ((s.sp + 0xbb0#64) ↦₃₂ ubb0) ∗
       ((s.sp + 0xbb8#64) ↦₆₄ ubb8) ∗ ((s.sp + 0xbc0#64) ↦₆₄ ubc0) ∗ ((s.sp + 0xbc8#64) ↦₆₄ ubc8) ∗
       ((s.sp + 0xbd0#64) ↦₃₂ ubd0) ∗ ((s.sp + 0xbd8#64) ↦₃₂ ubd8) ∗
       ((s.sp + 0xbdc#64) ↦₃₂ ubdc) ∗ ((s.sp + 0xbe0#64) ↦₃₂ ube0) ∗
       ((s.sp + 0xbe4#64) ↦₃₂ ube4))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
          ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗
          ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
          ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗
          ((s.sp + 0x38#64) ↦₆₄ v38) ∗ ((s.sp + 0x40#64) ↦₆₄ v40) ∗
          ((s.sp + 0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
          ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
          ((s.sp + 0x68#64) ↦₆₄ remIdLen) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
          ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
          ((s.sp + 0xd0#64) ↦₆₄ locIdLen) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ 0x8000000000000006#64) ∗ ((s.sp + 0x3e8#64) ↦₃₂ msgVer) ∗
          ((s.sp + 0x930#64) ↦₆₄ c1) ∗ ((s.sp + 0x938#64) ↦₆₄ c2) ∗
          ((s.sp + 0x940#64) ↦₆₄ c3) ∗ ((s.sp + 0x948#64) ↦₆₄ c4) ∗
          ((s.sp + 0x950#64) ↦₆₄ c5) ∗ ((s.sp + 0x958#64) ↦₆₄ c6) ∗
          ((s.sp + 0x960#64) ↦₆₄ c7) ∗ ((s.sp + 0x968#64) ↦₆₄ c8) ∗
          ((s.sp + 0x970#64) ↦₆₄ c9) ∗ ((s.sp + 0x978#64) ↦₆₄ c10) ∗
          ((s.sp + 0x980#64) ↦₆₄ c11) ∗ ((s.sp + 0x988#64) ↦₆₄ c12) ∗
          ((s.sp + 0xa90#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0xa98#64) ↦₆₄ newLocIdPtr) ∗
          ((s.sp + 0xaa0#64) ↦₆₄ locIdLen) ∗ ((s.sp + 0xaa8#64) ↦₆₄ remIdLen) ∗
          ((s.sp + 0xab0#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0xab8#64) ↦₆₄ remIdLen) ∗
          ((s.sp + 0xac0#64) ↦₆₄ s.readReg64 .x28) ∗ ((s.sp + 0xac8#64) ↦₆₄ newRootKeyPtr) ∗
          ((s.sp + 0xad0#64) ↦₆₄ s.readReg64 .x28) ∗ ((s.sp + 0xad8#64) ↦₆₄ v40) ∗
          ((s.sp + 0xae0#64) ↦₆₄ s.readReg64 .x25) ∗ ((s.sp + 0xae8#64) ↦₆₄ v40) ∗
          ((s.sp + 0xaf0#64) ↦₆₄ s.readReg64 .x24) ∗ ((s.sp + 0xaf8#64) ↦₆₄ s.readReg64 .x23) ∗
          ((s.sp + 0xb00#64) ↦₆₄ s.readReg64 .x24) ∗ ((s.sp + 0xb08#64) ↦₆₄ s.readReg64 .x26) ∗
          ((s.sp + 0xb10#64) ↦₆₄ s.readReg64 .x21) ∗ ((s.sp + 0xb18#64) ↦₆₄ s.readReg64 .x26) ∗
          ((s.sp + 0xb20#64) ↦₆₄ c0) ∗ ((s.sp + 0xb28#64) ↦₆₄ c1) ∗
          ((s.sp + 0xb30#64) ↦₆₄ c2) ∗ ((s.sp + 0xb38#64) ↦₆₄ c3) ∗
          ((s.sp + 0xb40#64) ↦₆₄ c4) ∗ ((s.sp + 0xb48#64) ↦₆₄ c5) ∗
          ((s.sp + 0xb50#64) ↦₆₄ c6) ∗ ((s.sp + 0xb58#64) ↦₆₄ c7) ∗
          ((s.sp + 0xb60#64) ↦₆₄ c8) ∗ ((s.sp + 0xb68#64) ↦₆₄ c9) ∗
          ((s.sp + 0xb70#64) ↦₆₄ c10) ∗ ((s.sp + 0xb78#64) ↦₆₄ c11) ∗
          ((s.sp + 0xb80#64) ↦₆₄ c12) ∗ ((s.sp + 0xb88#64) ↦₆₄ s.readReg64 .x22) ∗
          ((s.sp + 0xb90#64) ↦₆₄ v18) ∗ ((s.sp + 0xb98#64) ↦₆₄ s.readReg64 .x22) ∗
          ((s.sp + 0xba0#64) ↦₃₂ v2c) ∗ ((s.sp + 0xba4#64) ↦₃₂ (s.readReg64 .x20).truncate 32) ∗
          ((s.sp + 0xba8#64) ↦₆₄ v10) ∗ ((s.sp + 0xbb0#64) ↦₃₂ v28) ∗
          ((s.sp + 0xbb8#64) ↦₆₄ v38) ∗ ((s.sp + 0xbc0#64) ↦₆₄ v08) ∗ ((s.sp + 0xbc8#64) ↦₆₄ v38) ∗
          ((s.sp + 0xbd0#64) ↦₃₂ v24) ∗ ((s.sp + 0xbd8#64) ↦₃₂ 4#32) ∗
          ((s.sp + 0xbdc#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0xbe0#64) ↦₃₂ f248) ∗
          ((s.sp + 0xbe4#64) ↦₃₂ f24c)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3b0#64 ∧
        s1.readReg64 .x1 = b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7688) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7692)) ∧
        s1.readReg64 .x2 = 7#64 ∧
        s1.readReg64 .x3 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x4 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1e30#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg6_ver_ne_wp_trap b C abs s
    coroPtr locIdLen newLocIdPtr remIdLen newRemIdPtr newRootKeyPtr
    v08 v10 v18 v38 v40 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    u3e0 ua90 ua98 uaa0 uaa8 uab0 uab8 uac0 uac8 uad0 uad8 uae0 uae8
    uaf0 uaf8 ub00 ub08 ub10 ub18 ub20 ub28 ub30 ub38 ub40 ub48
    ub50 ub58 ub60 ub68 ub70 ub78 ub80 ub88 ub90 ub98
    uba8 ubb8 ubc0 ubc8
    msgVer v24 v28 v2c f248 f24c prevCounter u3e8
    uba0 uba4 ubb0 ubd0 ubd8 ubdc ube0 ube4
    hb hver_ne hpc hrun hsp_align hx19)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_b_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1e30#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs)
      (b + (bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one"))) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3c8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = 0#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1e48#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1e30 0x1e44
  dsimp only [trTrapProgAt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
      0x1e44#64 + bv% ((2^64 + ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7748)) % 2^64) =
      b + (bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment P3.ErrVerB (`+0x1e30 -> 0x15c44`, `0x4cefc -> growOneSpe`): Checks `errs.len = 0` and `errs.cap = 0` at `sp + 0x3c8..0x3d8`, sets `x0 = sp + 0x3c8`,
and calls `bl 0x15c44` (`growOneSpe`) at `+0x1e44`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_b_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1e30#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) (b + 0x15c44#64) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3c8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = 0#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1e48#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_b_wp_trap b C abs s
    coroPtr hpc hrun hsp_align hx19)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_c_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr errsPtr errTag e1 e2 e3 e4 e5
    u_c0 u_e0 u_e1 u_e2 u_e3 u_e4 u_e5 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1e48#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = 0#64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWP (trTrapProgAt b C abs) (b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]"))) s
      (((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ errTag) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ e1) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ e2) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ e3) ∗
       ((s.sp + 0x400#64) ↦₆₄ e4) ∗
       ((s.sp + 0x408#64) ↦₆₄ e5) ∗
       ((errsPtr + 0x0#64) ↦₆₄ u_e0) ∗
       ((errsPtr + 0x8#64) ↦₆₄ u_e1) ∗
       ((errsPtr + 0x10#64) ↦₆₄ u_e2) ∗
       ((errsPtr + 0x18#64) ↦₆₄ u_e3) ∗
       ((errsPtr + 0x20#64) ↦₆₄ u_e4) ∗
       ((errsPtr + 0x28#64) ↦₆₄ u_e5))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xc0#64) ↦₆₄ s.readReg64 .x27) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ errTag) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ e1) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ e2) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ e3) ∗
          ((s.sp + 0x400#64) ↦₆₄ e4) ∗
          ((s.sp + 0x408#64) ↦₆₄ e5) ∗
          ((errsPtr + 0x0#64) ↦₆₄ errTag) ∗
          ((errsPtr + 0x8#64) ↦₆₄ e1) ∗
          ((errsPtr + 0x10#64) ↦₆₄ e2) ∗
          ((errsPtr + 0x18#64) ↦₆₄ e3) ∗
          ((errsPtr + 0x20#64) ↦₆₄ e4) ∗
          ((errsPtr + 0x28#64) ↦₆₄ e5)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1e78#64) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1e48 0x1e74
  dsimp only [trTrapProgAt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
      0x1e74#64 + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7796)) % 2^64) = b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = 0#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have herr0 : 0#64 * 0x30#64 + errsPtr = errsPtr := by bv_arith
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P3.ErrVerC (`+0x1e48 -> SessionStructure> [local#5]`, `0x4cf14 -> dropSessionStructure3`): Copies `[sp + 0x3e0..0x410]` (`48` B) to `[errsPtr + 0..0x30]`, sets `[sp + 0x3d8] = 1#64`,
saves `x27` at `sp + 0xc0`, sets `x0 = sp + 0xa90`, and calls `bl SessionStructure> [local#5]` (`dropSessionStructure3`)
at `+0x1e74`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_c_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr errsPtr errTag e1 e2 e3 e4 e5
    u_c0 u_e0 u_e1 u_e2 u_e3 u_e4 u_e5 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1e48#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = 0#64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWP (tripleRatchetProgAt b C ctl abs) (b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]"))) s
      (((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ errTag) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ e1) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ e2) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ e3) ∗
       ((s.sp + 0x400#64) ↦₆₄ e4) ∗
       ((s.sp + 0x408#64) ↦₆₄ e5) ∗
       ((errsPtr + 0x0#64) ↦₆₄ u_e0) ∗
       ((errsPtr + 0x8#64) ↦₆₄ u_e1) ∗
       ((errsPtr + 0x10#64) ↦₆₄ u_e2) ∗
       ((errsPtr + 0x18#64) ↦₆₄ u_e3) ∗
       ((errsPtr + 0x20#64) ↦₆₄ u_e4) ∗
       ((errsPtr + 0x28#64) ↦₆₄ u_e5))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xc0#64) ↦₆₄ s.readReg64 .x27) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ errTag) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ e1) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ e2) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ e3) ∗
          ((s.sp + 0x400#64) ↦₆₄ e4) ∗
          ((s.sp + 0x408#64) ↦₆₄ e5) ∗
          ((errsPtr + 0x0#64) ↦₆₄ errTag) ∗
          ((errsPtr + 0x8#64) ↦₆₄ e1) ∗
          ((errsPtr + 0x10#64) ↦₆₄ e2) ∗
          ((errsPtr + 0x18#64) ↦₆₄ e3) ∗
          ((errsPtr + 0x20#64) ↦₆₄ e4) ∗
          ((errsPtr + 0x28#64) ↦₆₄ e5)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1e78#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_c_wp_trap b C abs s
    coroPtr errsPtr errTag e1 e2 e3 e4 e5
    u_c0 u_e0 u_e1 u_e2 u_e3 u_e4 u_e5
    hpc hrun hsp_align hx19 hx21 hx24)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_d_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr retPtr savedX27 ssCap u_3e0 : BitVec 64)
    (hb : b &&& 0xfff#64 = 0#64)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1e78#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x33b0#64) s
      (((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
       ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
          ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = 17#64 ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = retPtr ∧
        s1.readReg64 .x27 = savedX27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hshim := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_shim_ok_trap (b := b) (C := C)
    (abs := abs)
  have hcond_cap := cond_eq_adds64_of_ne_neg1 hcap_ne
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1e78 0x1e84
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x2cfc 0x2d14
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x307c 0x3098
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x32bc 0x32c0
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x33a4 0x33ac
  dsimp only [trTrapProgAt] at hshim hpc ⊢
  have hentry : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_logLevel_0x3080 hb hentry).1
  have hadrp := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_logLevel_0x3080 hb hentry).2
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have h5b810 : (b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by bv_arith
  wp_steps
  wp_call hshim ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P3.ErrVerD (`+0x1e78 -> +0x33b0`, `0x4cf44 -> bl __rust_alloc(17, 1)`): Checks `[coroPtr + 0xf0] = 0#64` (`previous_states.len = 0`), writes `[sp + 0x3e0] = -1`,
branches through `0x4ddc8 -> 0x4e148 -> 0x4e388 -> 0x4e470`, invokes
`__rust_no_alloc_shim_is_unstable_v2`, sets `x0 = 17, x1 = 1`, and stops at `+0x33b0`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_d_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr retPtr savedX27 ssCap u_3e0 : BitVec 64)
    (hb : b &&& 0xfff#64 = 0#64)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1e78#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x33b0#64) s
      (((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
       ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
          ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = 17#64 ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = retPtr ∧
        s1.readReg64 .x27 = savedX27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_d_wp_trap b C abs s
    coroPtr retPtr savedX27 ssCap u_3e0
    hb hcap_ne hpc hrun hsp_align hx19)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_e_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr dfPtr errsPtr ro0 ro1
    u_df0 u_df8 u_270 u_278 u_280 u_288 : BitVec 64)
    (u_df10 u_290 : BitVec 8)
    (hb : b &&& 0xfff#64 = 0#64)
    (hdf_nz : dfPtr ≠ 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x33b4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = dfPtr)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs) (b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]"))) s
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) ↦₆₄ᵣ ro0) ∗
       ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8)) ↦₆₄ᵣ ro1) ∗
       ((dfPtr + 0x0#64) ↦₆₄ u_df0) ∗
       ((dfPtr + 0x8#64) ↦₆₄ u_df8) ∗
       ((dfPtr + 0x10#64) ↦₈ u_df10) ∗
       ((s.sp + 0x270#64) ↦₆₄ u_270) ∗
       ((s.sp + 0x278#64) ↦₆₄ u_278) ∗
       ((s.sp + 0x280#64) ↦₆₄ u_280) ∗
       ((s.sp + 0x288#64) ↦₆₄ u_288) ∗
       ((s.sp + 0x290#64) ↦₈ u_290))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
          ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) ↦₆₄ᵣ ro0) ∗
          ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8)) ↦₆₄ᵣ ro1) ∗
          ((dfPtr + 0x0#64) ↦₆₄ ro0) ∗
          ((dfPtr + 0x8#64) ↦₆₄ ro1) ∗
          ((dfPtr + 0x10#64) ↦₈ 0x64#8) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗
          ((s.sp + 0x278#64) ↦₆₄ 17#64) ∗
          ((s.sp + 0x280#64) ↦₆₄ dfPtr) ∗
          ((s.sp + 0x288#64) ↦₆₄ 17#64) ∗
          ((s.sp + 0x290#64) ↦₈ 3#8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = errsPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = errsPtr ∧
        s1.readReg64 .x22 = errsPtr ∧
        s1.readReg64 .x23 = 1#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000018#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3410#64) := by
  have hdf_beq : (dfPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hdf_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x33b4 0x340c
  dsimp only [trTrapProgAt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_rodata_0x33bc hb hentry).1
  have hadrp := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_rodata_0x33bc hb hentry).2
  have htarget : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
      0x340c#64 + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 13324)) % 2^64) = b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = dfPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have h5ac90 : (b + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964)))) + bv% ((ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964)) % 4096) = b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964)) := by bv_arith
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P3.ErrVerE (`+0x33b4 -> SignalProtocolError> [local#3]`, `0x4e480 -> dropSpe2`): Checks `dfPtr ≠ 0`, copies `"decryption failed"` (`17` B from `b + 0xa6350#64`) to `dfPtr`,
writes `(0x8000000000000018#64, 17#64, dfPtr, 17#64, 3#8)` to `sp + 0x270..0x291`,
loads `x23 = [sp + 0x3d8] = 1#64` and `x22 = [sp + 0x3d0] = errsPtr`, sets `x21 = errsPtr`,
`x0 = errsPtr`, and calls `bl SignalProtocolError> [local#3]` (`dropSpe2`) at `+0x340c`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_e_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr dfPtr errsPtr ro0 ro1
    u_df0 u_df8 u_270 u_278 u_280 u_288 : BitVec 64)
    (u_df10 u_290 : BitVec 8)
    (hb : b &&& 0xfff#64 = 0#64)
    (hdf_nz : dfPtr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x33b4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = dfPtr)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) (b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]"))) s
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) ↦₆₄ᵣ ro0) ∗
       ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8)) ↦₆₄ᵣ ro1) ∗
       ((dfPtr + 0x0#64) ↦₆₄ u_df0) ∗
       ((dfPtr + 0x8#64) ↦₆₄ u_df8) ∗
       ((dfPtr + 0x10#64) ↦₈ u_df10) ∗
       ((s.sp + 0x270#64) ↦₆₄ u_270) ∗
       ((s.sp + 0x278#64) ↦₆₄ u_278) ∗
       ((s.sp + 0x280#64) ↦₆₄ u_280) ∗
       ((s.sp + 0x288#64) ↦₆₄ u_288) ∗
       ((s.sp + 0x290#64) ↦₈ u_290))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
          ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) ↦₆₄ᵣ ro0) ∗
          ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8)) ↦₆₄ᵣ ro1) ∗
          ((dfPtr + 0x0#64) ↦₆₄ ro0) ∗
          ((dfPtr + 0x8#64) ↦₆₄ ro1) ∗
          ((dfPtr + 0x10#64) ↦₈ 0x64#8) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗
          ((s.sp + 0x278#64) ↦₆₄ 17#64) ∗
          ((s.sp + 0x280#64) ↦₆₄ dfPtr) ∗
          ((s.sp + 0x288#64) ↦₆₄ 17#64) ∗
          ((s.sp + 0x290#64) ↦₈ 3#8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = errsPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = errsPtr ∧
        s1.readReg64 .x22 = errsPtr ∧
        s1.readReg64 .x23 = 1#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000018#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3410#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_e_wp_trap b C abs s
    coroPtr dfPtr errsPtr ro0 ro1
    u_df0 u_df8 u_270 u_278 u_280 u_288
    u_df10 u_290
    hb hdf_nz hpc hrun hsp_align hx0 hx19)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_f_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr errsPtr ssCap
    v_27c v_284 v_290 v_298
    u_250 u_258 u_370 u_378 u_384 u_38c : BitVec 64)
    (v_278 v_28c u_260 u_380 : BitVec 32)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3410#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = errsPtr)
    (hx22 : s.readReg64 .x22 = errsPtr)
    (hx23 : s.readReg64 .x23 = 1#64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = 0x8000000000000018#64) :
    SepWP (trTrapProgAt b C abs) (b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]"))) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       A.live errsPtr 192 8 ∗
       memRegion errsPtr 192 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
       ((s.sp + 0x250#64) ↦₆₄ u_250) ∗
       ((s.sp + 0x258#64) ↦₆₄ u_258) ∗
       ((s.sp + 0x260#64) ↦₃₂ u_260) ∗
       ((s.sp + 0x278#64) ↦₃₂ v_278) ∗
       ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗
       ((s.sp + 0x284#64) ↦₆₄ v_284) ∗
       ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗
       ((s.sp + 0x290#64) ↦₆₄ v_290) ∗
       ((s.sp + 0x298#64) ↦₆₄ v_298) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₃₂ u_380) ∗
       ((s.sp + 0x384#64) ↦₆₄ u_384) ∗
       ((s.sp + 0x38c#64) ↦₆₄ u_38c))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
          ((s.sp + 0x250#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x258#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x260#64) ↦₃₂ v_28c) ∗
          ((s.sp + 0x278#64) ↦₃₂ v_278) ∗
          ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x284#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗
          ((s.sp + 0x290#64) ↦₆₄ v_290) ∗
          ((s.sp + 0x298#64) ↦₆₄ v_298) ∗
          ((s.sp + 0x370#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x378#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x380#64) ↦₃₂ v_28c) ∗
          ((s.sp + 0x384#64) ↦₆₄ v_290) ∗
          ((s.sp + 0x38c#64) ↦₆₄ v_298)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = v_278.zeroExtend 64 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000018#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap (b := b) (C := C)
    (abs := abs) hA
  have hcond_cap := cond_eq_adds64_of_ne_neg1 hcap_ne
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x3410 0x341c
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x3500 0x3534
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x3570 0x3598
  dsimp only [trTrapProgAt] at hdealloc hpc ⊢
  have hentry : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
      0x3598#64 + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 13720)) % 2^64) = b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = errsPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = errsPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0x8000000000000018#64 := hx28
  wp_steps
  wp_call hdealloc (errsPtr, 192, 8)
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment P3.ErrVerF (`+0x3410 -> SessionStructure> [local#5]`, `0x4e4dc -> 0x4e5cc -> dropSessionStructure3`): Decrements `x23` (`1 -> 0`), branches to `0x4e5cc` (`+0x3500`), deallocates `errsPtr` (`192` B,
align `8`) via `__rust_dealloc`, copies `[sp + 0x278..0x2a0]` to `[sp + 0x370..0x394]` and `w22`,
checks `[coroPtr + 0xf8] = ssCap ≠ -1`, sets `x0 = coroPtr + 0xf8`, and calls `bl SessionStructure> [local#5]`
(`dropSessionStructure3`) at `+0x3598`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_f_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr errsPtr ssCap
    v_27c v_284 v_290 v_298
    u_250 u_258 u_370 u_378 u_384 u_38c : BitVec 64)
    (v_278 v_28c u_260 u_380 : BitVec 32)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3410#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = errsPtr)
    (hx22 : s.readReg64 .x22 = errsPtr)
    (hx23 : s.readReg64 .x23 = 1#64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = 0x8000000000000018#64) :
    SepWP (tripleRatchetProgAt b C ctl abs) (b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]"))) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       A.live errsPtr 192 8 ∗
       memRegion errsPtr 192 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
       ((s.sp + 0x250#64) ↦₆₄ u_250) ∗
       ((s.sp + 0x258#64) ↦₆₄ u_258) ∗
       ((s.sp + 0x260#64) ↦₃₂ u_260) ∗
       ((s.sp + 0x278#64) ↦₃₂ v_278) ∗
       ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗
       ((s.sp + 0x284#64) ↦₆₄ v_284) ∗
       ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗
       ((s.sp + 0x290#64) ↦₆₄ v_290) ∗
       ((s.sp + 0x298#64) ↦₆₄ v_298) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₃₂ u_380) ∗
       ((s.sp + 0x384#64) ↦₆₄ u_384) ∗
       ((s.sp + 0x38c#64) ↦₆₄ u_38c))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
          ((s.sp + 0x250#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x258#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x260#64) ↦₃₂ v_28c) ∗
          ((s.sp + 0x278#64) ↦₃₂ v_278) ∗
          ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x284#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗
          ((s.sp + 0x290#64) ↦₆₄ v_290) ∗
          ((s.sp + 0x298#64) ↦₆₄ v_298) ∗
          ((s.sp + 0x370#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x378#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x380#64) ↦₃₂ v_28c) ∗
          ((s.sp + 0x384#64) ↦₆₄ v_290) ∗
          ((s.sp + 0x38c#64) ↦₆₄ v_298)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = v_278.zeroExtend 64 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000018#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_ver_f_wp_trap b C abs hA s
    coroPtr errsPtr ssCap
    v_27c v_284 v_290 v_298
    u_250 u_258 u_370 u_378 u_384 u_38c
    v_278 v_28c u_260 u_380
    hcap_ne hpc hrun hsp_align hx19 hx21 hx22 hx23 hx24 hx25 hx28)

/-! ## 2. Stage P2 `spkSigCap = 0#64` / `kyberSigCap = 0#64` Segment Specializations -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg2d_sig0_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr spkPubPtr spkPrivPtr spkSigPtr
    kyberCtCap kyberStorePtr kyberStoreVt kyberLoadShimAddr
    v_a0 v_b0 u_3e0 : BitVec 64)
    (kyberPreKeyId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b63
     s0 s1_b s2 s3 s4 s5 s6
     c0 c1 c2 c3 c4 c5 c6 c63 b_3e8 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6
     cw0 cw1 cw2 cw3 cw4 cw5 cw6 : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xfcc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = spkSigPtr)
    (hx22 : s.readReg64 .x22 = spkPubPtr)
    (hx28 : s.readReg64 .x28 = 33#64) :
    SepWP (trTrapProgAt b C abs) kyberLoadShimAddr s
      (((s.sp + 0xa90#64) ↦₈ 0#8) ∗
       keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
       bytes7At (s.sp + 0x930#64) s0 s1_b s2 s3 s4 s5 s6 ∗
       keyPair64UnalignedAt
         (coroPtr + 0x398#64) c0 c1 c2 c3 c4 c5 c6 cw0 cw1 cw2 cw3 cw4 cw5 cw6 c63 ∗
       ((s.sp + 0x90#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ 32#64) ∗
       ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((s.sp + 0x3e8#64) ↦₈ b_3e8) ∗
       A.live spkPubPtr 33 1 ∗ memRegion spkPubPtr 33 ∗
       A.live spkPrivPtr 32 1 ∗ memRegion spkPrivPtr 32 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
       ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa90#64) ↦₈ 0#8) ∗
          keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          bytes7At (s.sp + 0x930#64) b0 b1 b2 b3 b4 b5 b6 ∗
          keyPair64UnalignedAt (coroPtr + 0x398#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          ((s.sp + 0x90#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ w6) ∗
          ((s.sp + 0x3e8#64) ↦₈ b63) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
          ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
          ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
          ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberStorePtr ∧
        s1.readReg64 .x1 = kyberPreKeyId.zeroExtend 64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = spkSigPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x22 = spkPubPtr ∧
        s1.readReg64 .x23 = v_a0 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1460#64) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap (b := b) (C := C)
    (abs := abs) hA
  have hkyber_beq : (kyberCtCap == 0#64) = false := beq_eq_false_iff_ne.mpr hkyber_nz
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xfcc 0xfd4
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x138c 0x145c
  dsimp only [trTrapProgAt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = spkSigPtr := hx20
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkPubPtr := hx22
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 33#64 := hx28
  dsimp only [keyPair64UnalignedAt, bytes7At]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_call hdealloc (spkPubPtr, 33, 1)
  wp_steps
  wp_call hdealloc (spkPrivPtr, 32, 1)
  wp_steps
  rw [hsp_sf]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

/-- Segment P2.2d (`spkSigCap = 0#64` specialization): Checks `[sp + 0xa90] = 0#8` (`Ok(spkKeyPair)`), jumps to `+0x138c`, copies the 64-byte SPK
`KeyPair` from `sp + 0xa91..0xad1` to `coroPtr + 0x398..0x3d8` (via `sp + 0x930..0x937`),
deallocates `spkPubPtr` and `spkPrivPtr`, skips `spkSigPtr` deallocation because `[sp + 0x90] =
0#64`,
checks `[msgPtr + 0x90] = kyberCtCap ≠ 0`, loads `w1 = [msgPtr + 0xa0]` (`kyberPreKeyId`),
`x0 = kyberStorePtr`, and calls `blr x8` (`kyberLoadShimAddr`) at `+0x145c`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg2d_sig0_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr spkPubPtr spkPrivPtr spkSigPtr
    kyberCtCap kyberStorePtr kyberStoreVt kyberLoadShimAddr
    v_a0 v_b0 u_3e0 : BitVec 64)
    (kyberPreKeyId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b63
     s0 s1_b s2 s3 s4 s5 s6
     c0 c1 c2 c3 c4 c5 c6 c63 b_3e8 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6
     cw0 cw1 cw2 cw3 cw4 cw5 cw6 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xfcc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = spkSigPtr)
    (hx22 : s.readReg64 .x22 = spkPubPtr)
    (hx28 : s.readReg64 .x28 = 33#64) :
    SepWP (tripleRatchetProgAt b C ctl abs) kyberLoadShimAddr s
      (((s.sp + 0xa90#64) ↦₈ 0#8) ∗
       keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
       bytes7At (s.sp + 0x930#64) s0 s1_b s2 s3 s4 s5 s6 ∗
       keyPair64UnalignedAt
         (coroPtr + 0x398#64) c0 c1 c2 c3 c4 c5 c6 cw0 cw1 cw2 cw3 cw4 cw5 cw6 c63 ∗
       ((s.sp + 0x90#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ 32#64) ∗
       ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((s.sp + 0x3e8#64) ↦₈ b_3e8) ∗
       A.live spkPubPtr 33 1 ∗ memRegion spkPubPtr 33 ∗
       A.live spkPrivPtr 32 1 ∗ memRegion spkPrivPtr 32 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
       ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa90#64) ↦₈ 0#8) ∗
          keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          bytes7At (s.sp + 0x930#64) b0 b1 b2 b3 b4 b5 b6 ∗
          keyPair64UnalignedAt (coroPtr + 0x398#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          ((s.sp + 0x90#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ w6) ∗
          ((s.sp + 0x3e8#64) ↦₈ b63) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
          ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
          ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
          ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberStorePtr ∧
        s1.readReg64 .x1 = kyberPreKeyId.zeroExtend 64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = spkSigPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x22 = spkPubPtr ∧
        s1.readReg64 .x23 = v_a0 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1460#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg2d_sig0_wp_trap b C abs hA s
    coroPtr msgPtr spkPubPtr spkPrivPtr spkSigPtr
    kyberCtCap kyberStorePtr kyberStoreVt kyberLoadShimAddr
    v_a0 v_b0 u_3e0 kyberPreKeyId
    b0 b1 b2 b3 b4 b5 b6 b63 s0 s1_b s2 s3 s4 s5 s6
    c0 c1 c2 c3 c4 c5 c6 c63 b_3e8
    w0 w1 w2 w3 w4 w5 w6 cw0 cw1 cw2 cw3 cw4 cw5 cw6
    hpc hrun hsp_align hkyber_nz hx19 hx20 hx22 hx28)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3d1_sig0_wp_trap {A : RustAlloc} (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr kyberPubPtr kyberSecPtr kyberSigPtr
    pkBuf skBuf kyberCtCap v_98 v_a0
    u_3d8 u_3e0 u_3e8 u_3f0 : BitVec 64)
    (b_4f1 : BitVec 8)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xc74#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = kyberSigPtr)
    (hx23 : s.readReg64 .x23 = kyberPubPtr)
    (hx28 : s.readReg64 .x28 = 1569#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd04#64) s
      (((s.sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((s.sp + 0xa98#64) ↦₆₄ pkBuf) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
       ((s.sp + 0xaa8#64) ↦₆₄ skBuf) ∗
       ((s.sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗
       ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗
       ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((s.sp + 0x90#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ 3169#64) ∗
       ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr) ∗
       A.live kyberPubPtr 1569 1 ∗ memRegion kyberPubPtr 1569 ∗
       A.live kyberSecPtr 3169 1 ∗ memRegion kyberSecPtr 3169 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((s.sp + 0xa98#64) ↦₆₄ pkBuf) ∗
          ((s.sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
          ((s.sp + 0xaa8#64) ↦₆₄ skBuf) ∗
          ((s.sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
          ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗
          ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗
          ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
          ((s.sp + 0x90#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ 3169#64) ∗
          ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = 21#64 ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = msgPtr + 0x90#64 ∧
        s1.readReg64 .x22 = kyberCtCap ∧
        s1.readReg64 .x23 = v_a0 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  have hdealloc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_dealloc_ok_trap (b := b) (C := C)
    (abs := abs) hA
  have hshim := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_shim_ok_trap (b := b) (C := C)
    (abs := abs)
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0xc74 0xd00
  dsimp only [trTrapProgAt] at hdealloc hshim hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = kyberSigPtr := hx20
  have hx23' : s.readReg64 (Reg.gpr 23#5) = kyberPubPtr := hx23
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 1569#64 := hx28
  wp_steps
  wp_call hdealloc (kyberPubPtr, 1569, 1)
  wp_steps
  wp_call hdealloc (kyberSecPtr, 3169, 1)
  wp_steps
  wp_call hshim ()
  wp_steps
  have hsp_sf1 : sf.sp = s.sp := by simp_all [arm64_norm]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by rw [hsp_sf1]; ac_rfl), by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment P2.3d1 (`kyberSigCap = 0#64` specialization): Reads `Ok(kyberKeyPair)` (`tag = -2`, `pkBuf, 0x620, skBuf, 0xc60`) from `sp + 0xa90..0xab8`,
stores `(pkBuf, 0x620, skBuf, 0xc60)` at `coroPtr + 0x3d8..0x3f8` and `1#8` at `[coroPtr + 0x4f1]`,
deallocates `kyberPubPtr` and `kyberSecPtr`, skips `kyberSigPtr` deallocation because `[sp +
0x90] = 0#64`,
invokes `__rust_no_alloc_shim_is_unstable_v2`, sets `x0 = 21, x1 = 1`, and stops at `+0x0d04`
(`bl __rust_alloc`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3d1_sig0_wp {A : RustAlloc} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s : State) (coroPtr msgPtr kyberPubPtr kyberSecPtr kyberSigPtr
    pkBuf skBuf kyberCtCap v_98 v_a0
    u_3d8 u_3e0 u_3e8 u_3f0 : BitVec 64)
    (b_4f1 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xc74#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = kyberSigPtr)
    (hx23 : s.readReg64 .x23 = kyberPubPtr)
    (hx28 : s.readReg64 .x28 = 1569#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xd04#64) s
      (((s.sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((s.sp + 0xa98#64) ↦₆₄ pkBuf) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
       ((s.sp + 0xaa8#64) ↦₆₄ skBuf) ∗
       ((s.sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗
       ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗
       ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((s.sp + 0x90#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ 3169#64) ∗
       ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr) ∗
       A.live kyberPubPtr 1569 1 ∗ memRegion kyberPubPtr 1569 ∗
       A.live kyberSecPtr 3169 1 ∗ memRegion kyberSecPtr 3169 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((s.sp + 0xa98#64) ↦₆₄ pkBuf) ∗
          ((s.sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
          ((s.sp + 0xaa8#64) ↦₆₄ skBuf) ∗
          ((s.sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
          ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗
          ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗
          ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
          ((s.sp + 0x90#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ 3169#64) ∗
          ((s.sp + 0xd0#64) ↦₆₄ kyberSecPtr) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = 21#64 ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = msgPtr + 0x90#64 ∧
        s1.readReg64 .x22 = kyberCtCap ∧
        s1.readReg64 .x23 = v_a0 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p2_seg3d1_sig0_wp_trap b C abs hA s
    coroPtr msgPtr kyberPubPtr kyberSecPtr kyberSigPtr
    pkBuf skBuf kyberCtCap v_98 v_a0
    u_3d8 u_3e0 u_3e8 u_3f0 b_4f1
    hpc hrun hsp_align hx19 hx20 hx23 hx28)

end CryptoVerification.E2E.Pqxdh.ResponderClosure
