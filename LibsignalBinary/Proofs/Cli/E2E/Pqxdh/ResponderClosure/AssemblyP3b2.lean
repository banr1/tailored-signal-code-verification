/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSpe2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.ErrExit
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.SessionRecordCallees
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local1
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpe
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.SetState
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExt
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Ext
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

/-!
# Responder Closure Stage P3 Post-`tryDecrypt` `Ok` & `Err` Dispatch

Proves the Stage P3 `Ok` path (`stageP3_sub5_ok`, `+0x1cd8 → +0x34dc`), duplicate and
non-duplicate error funnels (`stageP3_sub5_err_dup_ok`, `stageP3_sub5_err_nondup_ok`,
`stageP3_sub5_err_ok`), and unified post-`tryDecrypt` dispatch (`stageP3_sub5_dispatch_ok`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open CryptoVerification.LibsignalTripleRatchet.RawByteMove

open CryptoVerification.LibsignalTripleRatchet.Record

open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps

open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts

open CryptoVerification.LibsignalPublicApiRepr

open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux

open CryptoVerification.LibsignalSession

open CryptoVerification.E2E.Pqxdh.WireEntries

open CryptoVerification.E2E.Pqxdh.ResponderStore

set_option maxRecDepth 200000

set_option maxHeartbeats 1600000

set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace P3P4

abbrev _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3b2_rodata_0x87350_intro := @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.rodata_0x87350_intro

abbrev _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3b2_rodata_0x87358_intro := @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.rodata_0x87358_intro

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.SepWPp.intro_rodata_5ac90_5ac98 {img : Obj.Image} {b : BitVec 64}
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s)
    (h : SepWPp prog ret s
      (((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) ↦₆₄ᵣ 0x6974707972636564#64) ∗
       ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8)) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  subst hb
  intro R hm hL
  have hm1 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3b2_rodata_0x87358_intro himg hF hm
  have hm2 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3b2_rodata_0x87350_intro himg hF hm1
  have hm3 : s.mem ⊨
      (((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) ↦₆₄ᵣ 0x6974707972636564#64) ∗
       ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8)) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗ P) ∗ R := by
    simpa only [sepConj_assoc] using hm2
  exact h R hm3 hL

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_seg7a_x24_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr retPtr : BitVec 64)
    (ssBytes : List (BitVec 8))
    (hb : b &&& 0xfff#64 = 0#64)
    (hss_len : ssBytes.length = 344)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs) (b + 0x174d4#64) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0xa90#64) ↦ₛ ssBytes) ∗ memRegion (s.sp + 0x3e0#64) 344)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0xa90#64) ↦ₛ ssBytes) ∗ ((s.sp + 0x3e0#64) ↦ₛ ssBytes)) ∧ s1.sp = s.sp ∧
        s1.trace = s.trace ∧ s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = s.sp + 0x3e0#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = retPtr ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1dfc#64) := by
  have hmemcpy := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_memcpy_ok_trap (b := b) (C := C)
    (abs := abs)
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1cd8 0x1cf8
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1de0 0x1df8
  dsimp only [trTrapProgAt] at hmemcpy hpc ⊢
  have hentry : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_logMaxLevel_0x1cec hb hentry).1
  have hadrp := (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.adrp_logMaxLevel_0x1cec hb hentry).2
  have htarget : (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
      0x1df8#64 + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7672)) % 2^64) = b + 0x174d4#64 := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have h5b810 : (b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by bv_arith
  wp_steps
  wp_call hmemcpy (s.sp + 0x3e0#64, s.sp + 0xa90#64, ssBytes)
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- `p3_seg7a_wp` with `x24` preservation explicitly tracked. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_seg7a_x24_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr retPtr : BitVec 64)
    (ssBytes : List (BitVec 8))
    (hb : b &&& 0xfff#64 = 0#64)
    (hss_len : ssBytes.length = 344)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs) (b + 0x174d4#64) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0xa90#64) ↦ₛ ssBytes) ∗ memRegion (s.sp + 0x3e0#64) 344)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0xa90#64) ↦ₛ ssBytes) ∗ ((s.sp + 0x3e0#64) ↦ₛ ssBytes)) ∧ s1.sp = s.sp ∧
        s1.trace = s.trace ∧ s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = s.sp + 0x3e0#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = retPtr ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1dfc#64) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_seg7a_x24_wp_trap b C abs s
      coroPtr retPtr ssBytes hb hss_len hpc hrun hsp_align hx19)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_seg7b_x24_wp_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1dfc#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64) s
      emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧ s1.sp = s.sp ∧
        s1.trace = s.trace ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29) := by
  closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1dfc 0x1e00
  dsimp only [trTrapProgAt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- `p3_seg7b_wp` with `x24` preservation explicitly tracked. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_seg7b_x24_wp (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1dfc#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64) s
      emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧ s1.sp = s.sp ∧
        s1.trace = s.trace ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_seg7b_x24_wp_trap b C abs s
      coroPtr hpc hrun hx19)

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_ok_trap {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr retPtr : BitVec 64)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hb : b &&& 0xfff#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ A.pool ∗ stackAt s.sp setSessionStateStack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          sessionStateAt A (coroPtr + 0xf8#64) G₂ st₂ ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          memRegion (s.sp + 0xa90#64) 344 ∗ A.pool ∗ stackAt s.sp setSessionStateStack) ∧
        sf.sp = s.sp ∧ sf.trace = s0.trace ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        sf.readReg64 .x19 = coroPtr ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.sp + 0x210#64 ∧ sf.readReg64 .x26 = retPtr ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29)
      (PanicOomProp s0) := by
  have hset := FromRecordCallees.set_session_state_ok_trap
    (FromRecordCallees.drop_session_structure_local1_ok_trap (b := b) (C := C)
      (abs := abs) hA
      (Getters.drop_vec_message_key_ok_trap hA) (Getters.drop_vec_chain_ok_trap hA))
  rw [sessionStateAt_eq_inline_sep_heap A (s.sp + 0xa90#64) G₂ st₂]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun bs => ?_
  refine SepWPp.weaken_frame
    (P₁ := ⌜bs.length = 344 ∧ SessionInline G₂ st₂ bs⌝)
    (P₂ := ⌜bs.length = 344 ∧ SessionInline G₂ st₂ bs⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨hbs_len, hinl⟩ => ?_
  have hstep1 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_seg7a_x24_wp_trap b C abs s coroPtr retPtr bs hb hbs_len
    hpc hrun hsp_align hx19
  refine SepWPp.bind_sepWP_frame hF hsym hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx1_1, hx19_1, hx24_1, hx25_1, hx26_1, hx27_1, hx29_1,
    hx30_1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hpc1_set : s1.pc = (trTrapProgAt b C abs).fnAddr setSessionStateName := by
    rw [hpc1, trTrapProgAt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x174d4]
  refine SepWPp.call_frame_frozen_nopanic
    (x := (⟨coroPtr + 0xe0#64, s.sp + 0x3e0#64, some (recG, recSt), bs⟩ : SetSessionStateGhost))
    (T := sessionStateAt A (coroPtr + 0xe0#64 + 0x18#64) recG recSt ∗
          ((s.sp + 0x3e0#64) ↦ₛ bs) ∗ A.pool ∗ stackAt s.sp setSessionStateStack)
    hF1 hsym1 hset hpc1_set hrun1 hsp1_al hx30_1
    (by dsimp only [setSessionStateSpec]; rw [hsp1_s])
    (And.intro hx0_1 (And.intro hx1_1 hbs_len))
    (by
      have h18 : coroPtr + 0xe0#64 + 0x18#64 = coroPtr + 0xf8#64 := by bv_omega
      rw [h18]; sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 hsp2_al hcs2 hF2 hsym2 => ?_)
  dsimp only [setSessionStateSpec]
  rw [hsp1_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have h18 : coroPtr + 0xe0#64 + 0x18#64 = coroPtr + 0xf8#64 := by bv_omega
  rw [h18]
  have hmove := RawByteMove.sessionStateAt_move_bytes_twice A
    (s.sp + 0xa90#64) (s.sp + 0x3e0#64) (coroPtr + 0xf8#64) G₂ st₂ hinl
  refine SepWPp.weaken_frame hmove (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, hx27_cs2, _, hx29_cs2, _⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hstep3 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_seg7b_x24_wp_trap b C abs s2 coroPtr hpc2 hrun2 hx19_2
  refine SepWPp.ret_sepWP_frame hF2 hsym2 hstep3 (by sep_focus)
    fun sf hpcf hrunf hFf hsymf hregsf => ?_
  rcases hregsf with ⟨hspf_2, htrf_2, hx19_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f⟩
  refine ⟨Entails.of_eq (eq_of_sep_emp (by sep_focus)),
    hspf_2.trans hsp2_s,
    htrf_2.trans (htr2_1.trans (htr1_s.trans htr)),
    hFf, hsymf, hx19_f,
    hx24_f.trans (hx24_cs2.trans hx24_1),
    hx25_f.trans (hx25_cs2.trans hx25_1),
    hx26_f.trans (hx26_cs2.trans hx26_1),
    hx27_f.trans (hx27_cs2.trans hx27_1),
    hx28_f, hx29_f.trans (hx29_cs2.trans hx29_1)⟩

set_option maxHeartbeats 4000000 in
/-- Substage P3.5 / P3.7 (`stageP3_sub5_ok`, `+0x1cd8#64 -> +0x34dc#64` on `Ok`): Composes `p3_seg7a_x24_wp` (`+0x1cd8#64 -> b + 0x174d4#64`),
  `FromRecordCallees.set_session_state_ok`
(`b + 0x174d4#64 -> +0x1dfc#64` with `RawByteMove.sessionStateAt_move_bytes_twice`), and
`p3_seg7b_x24_wp` (`+0x1dfc#64 -> +0x34dc#64`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto) (ctl : BitVec
  64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr retPtr : BitVec 64)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hb : b &&& 0xfff#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ A.pool ∗ stackAt s.sp setSessionStateStack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          sessionStateAt A (coroPtr + 0xf8#64) G₂ st₂ ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          memRegion (s.sp + 0xa90#64) 344 ∗ A.pool ∗ stackAt s.sp setSessionStateStack) ∧
        sf.sp = s.sp ∧ sf.trace = s0.trace ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        sf.readReg64 .x19 = coroPtr ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.sp + 0x210#64 ∧ sf.readReg64 .x26 = retPtr ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_ok_trap img b C abs hA s0
      s coroPtr retPtr G₂ recG st₂ recSt hb hF hsym hpc hrun hsp_align htr hx19)

abbrev _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub7_ok_trap := @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_ok_trap

abbrev _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub7_ok := @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_ok

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_decResult_ok_trap {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr retPtr : BitVec 64)
    (pt : List (BitVec 8)) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hb : b &&& 0xfff#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       vecResultAt A (s.sp + 0x270#64) (.ok pt) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ A.pool ∗ stackAt s.sp setSessionStateStack)
      (fun sf P_f =>
        ∃ ptCap ptPtr : BitVec 64,
          pt.length ≤ ptCap.toNat ∧ ptCap.toNat < 2 ^ 63 ∧ ptPtr ≠ 0#64 ∧
          (P_f ⊢
            ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
            ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
            ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
            memRegion (s.sp + 0x290#64) 16 ∗ (ptPtr ↦ₛ pt) ∗
            (if ptCap = 0#64 then emp
             else A.live ptPtr ptCap.toNat 1 ∗
               memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
            ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ sessionStateAt A (coroPtr + 0xf8#64) G₂ st₂ ∗
            memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0xa90#64) 344 ∗
            A.pool ∗ stackAt s.sp setSessionStateStack) ∧ sf.sp = s.sp ∧
          sf.trace = s0.trace ∧ img.FrozenLoaded sf ∧
          sf.symtab = img.symtab ∧ sf.readReg64 .x19 = coroPtr ∧
          sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = s.sp + 0x210#64 ∧
          sf.readReg64 .x26 = retPtr ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
          sf.readReg64 .x28 = 0xfffffffffffffffe#64 ∧ sf.readReg64 .x29 = s.readReg64 .x29)
      (PanicOomProp s0) := by
  refine SepWPp.weaken_frame (decResultAt_ok_unpack A (s.sp + 0x270#64) pt) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ptCap => SepWPp.exists_elim fun ptPtr => ?_
  refine SepWPp.weaken_frame
    (P₁ := ⌜pt.length ≤ ptCap.toNat ∧ ptCap.toNat < 2 ^ 63 ∧ ptPtr ≠ 0#64⌝)
    (P₂ := ⌜pt.length ≤ ptCap.toNat ∧ ptCap.toNat < 2 ^ 63 ∧ ptPtr ≠ 0#64⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨hpt_le, hpt_lt, hpt_ne⟩ => ?_
  have hsub := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_ok_trap img b C abs hA s0 s coroPtr retPtr G₂ recG st₂ recSt
    hb hF hsym hpc hrun hsp_align htr hx19
  refine SepWPp.ret_sepWPp_frame hsub (by sep_focus)
    fun sf _ _ ⟨hspf, htrf, hFf, hsymf, hx19f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f⟩ => ?_
  refine ⟨ptCap, ptPtr, hpt_le, hpt_lt, hpt_ne, ?_,
    hspf, htrf, hFf, hsymf, hx19f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f⟩
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

/-- Wrapper around `stageP3_sub5_ok` starting from `vecResultAt A (s.sp + 0x270#64) (.ok pt)`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_decResult_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
  (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr retPtr : BitVec 64)
    (pt : List (BitVec 8)) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hb : b &&& 0xfff#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       vecResultAt A (s.sp + 0x270#64) (.ok pt) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ A.pool ∗ stackAt s.sp setSessionStateStack)
      (fun sf P_f =>
        ∃ ptCap ptPtr : BitVec 64,
          pt.length ≤ ptCap.toNat ∧ ptCap.toNat < 2 ^ 63 ∧ ptPtr ≠ 0#64 ∧
          (P_f ⊢
            ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
            ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
            ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
            memRegion (s.sp + 0x290#64) 16 ∗ (ptPtr ↦ₛ pt) ∗
            (if ptCap = 0#64 then emp
             else A.live ptPtr ptCap.toNat 1 ∗
               memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
            ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ sessionStateAt A (coroPtr + 0xf8#64) G₂ st₂ ∗
            memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0xa90#64) 344 ∗
            A.pool ∗ stackAt s.sp setSessionStateStack) ∧ sf.sp = s.sp ∧
          sf.trace = s0.trace ∧ img.FrozenLoaded sf ∧
          sf.symtab = img.symtab ∧ sf.readReg64 .x19 = coroPtr ∧
          sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = s.sp + 0x210#64 ∧
          sf.readReg64 .x26 = retPtr ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
          sf.readReg64 .x28 = 0xfffffffffffffffe#64 ∧ sf.readReg64 .x29 = s.readReg64 .x29)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_decResult_ok_trap img b C
      abs hA s0 s coroPtr retPtr pt G₂ recG st₂ recSt hb hF hsym hpc hrun hsp_align htr hx19)

/-! ## 1. Common Error Epilogue & Duplicate-Message Error Path -/

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_err_tail_common_ok_trap {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr outPtr errTag prevStatesPtr
    w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")))
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = coroPtr + 0xf8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hx30 : s.readReg64 .x30 =
      (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64) :
    SepWPp (trTrapProgAt b C abs) (s0.readReg64 .x30) s
      (sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       ((s.sp + 0x370#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
       ((s.sp + 0x378#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
       ((s.sp + 0x380#64) ↦₃₂ w2.extractLsb' 32 32) ∗ ((s.sp + 0x384#64) ↦₆₄ w3) ∗
       ((s.sp + 0x38c#64) ↦₆₄ w4) ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢
          memRegion (coroPtr + 0xf8#64) 344 ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ words6At outPtr errTag w0 w1 w2 w3 w4 ∗
          memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗ stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hdropSs3 := CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.drop_session_structure3_ok_trap
    (b := b) (C := C) (abs := abs) hA
  have hpc_drop : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name := by
    rw [hpc, trTrapProgAt, Program.fnAddr_rebase, (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")]
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned] using hsp_align
  refine SepWPp.call_frame_frozen_nopanic
    (x := (⟨coroPtr + 0xf8#64, recG, recSt⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ A.pool ∗
          stackAt s.sp dropSessionStructure2Stack)
    hF hsym hdropSs3 hpc_drop hrun hsp_al hx30
    (by dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec])
    hx0 (by sep_focus)
    (hnext := fun s1 hpc1 hrun1 hsp1_s hsp1_al hcs1 hF1 hsym1 => ?_)
  dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1_s => ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1_s]; exact hsp_align
  rcases hcs1 with ⟨hx19_cs1, _, _, hx22_cs1, _, _, hx25_cs1, hx26_cs1, _, hx28_cs1, _, _⟩
  have hx19_1 : s1.readReg64 .x19 = coroPtr := hx19_cs1.trans hx19
  have hx22_1 : s1.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64 := hx22_cs1.trans hx22
  have hx25_1 : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_cs1, hx25, hsp1_s]
  have hx26_1 : s1.readReg64 .x26 = outPtr := hx26_cs1.trans hx26
  have hx28_1 : s1.readReg64 .x28 = errTag := hx28_cs1.trans hx28
  have hrepack380 := repack20_32_64_64_to_64_64_32 (s.sp + 0x380#64) (w2.extractLsb' 32 32) w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack380
  refine SepWPp.weaken_frame (Entails.of_eq hrepack380) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (outPtr48_split_eq outPtr)) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0))
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_ret2c => SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret1c => SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret0c => SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0 => ?_
  have hstep2 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_tail_b_wp_trap b C abs s1 coroPtr outPtr errTag prevStatesPtr
    (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
    (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
    (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
    u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
    (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
    (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
    (w0.extractLsb' 0 32) (w4.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
    hpc1 hrun1 hsp1_align hx19_1 hx22_1 hx25_1 hx26_1 hx28_1
  rw [hsp1_s] at hstep2
  refine SepWPp.bind_sepWP_frame hF1 hsym1 hstep2 (by sep_focus)
    fun sf hpcf hrunf hFf hsymf hregsf => ?_
  rcases hregsf with ⟨hspf_s, htrf_1, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
    hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
  refine SepWPp.weaken_frame (Entails.of_eq hrepack380.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (sp370_36_err_fold s.sp
      (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
      (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
      w3 w4 (w2.extractLsb' 32 32))
    (by sep_focus) ?_
  have hrepack_out1c := (repack20_32_64_64_to_64_64_32 (outPtr + 0x1c#64)
    (w2.extractLsb' 32 32) w3 w4).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out1c
  refine SepWPp.weaken_frame (Entails.of_eq hrepack_out1c) (by sep_focus) ?_
  have hrepack_out8 := (words3_repack_w32_2w64_w32 (outPtr + 0x8#64) w0 w1 w2).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out8
  refine SepWPp.weaken_frame (Entails.of_eq hrepack_out8) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm)
    (by sep_focus) ?_
  have hout_words :
      ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₆₄ w0) ∗
      ((outPtr + 0x10#64) ↦₆₄ w1) ∗ ((outPtr + 0x18#64) ↦₆₄ w2) ∗
      ((outPtr + 0x20#64) ↦₆₄ w3) ∗ ((outPtr + 0x28#64) ↦₆₄ w4) ⊢
      words6At outPtr errTag w0 w1 w2 w3 w4 := by
    unfold words6At
    rw [BitVec.add_zero]
    exact Entails.refl _
  refine SepWPp.weaken_frame hout_words (by sep_focus) ?_
  have hcc : ClosureCalleeSaved s0 sf :=
    ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩
  refine SepWPp.done hpcf hrunf ⟨Entails.of_eq (eq_of_sep_emp (by sep_focus)),
    hspf_s, htrf_1.trans (htr1_s.trans htr), hcc, hFf, hsymf⟩

set_option maxHeartbeats 4000000 in
/-- Common error epilogue (`drop_glue::<SessionStructure> [local#4] → s0.readReg64 .x30`): calls `drop_session_structure3_ok` on `coroPtr + 0xf8#64`, repacks the 5 payload words `w0..w4` at `s.sp + 0x370#64..0x394#64` and `x22`, executes `p3_err_tail_b_wp` (`+0x359c#64 → s0.readReg64 .x30`), and reassembles `words6At outPtr errTag w0 w1 w2 w3 w4`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_err_tail_common_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
  (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr outPtr errTag prevStatesPtr
    w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")))
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = coroPtr + 0xf8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hx30 : s.readReg64 .x30 =
      (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 .x30) s
      (sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       ((s.sp + 0x370#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
       ((s.sp + 0x378#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
       ((s.sp + 0x380#64) ↦₃₂ w2.extractLsb' 32 32) ∗ ((s.sp + 0x384#64) ↦₆₄ w3) ∗
       ((s.sp + 0x38c#64) ↦₆₄ w4) ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢
          memRegion (coroPtr + 0xf8#64) 344 ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ words6At outPtr errTag w0 w1 w2 w3 w4 ∗
          memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗ stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hx30
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_err_tail_common_ok_trap img b C
      abs hA s0 s coroPtr outPtr errTag prevStatesPtr w0 w1 w2 w3 w4 b_2c0 recG recSt hF hsym hpc
      hrun hsp_align htr hx0 hx19 hx22 hx25 hx26 hx28 hx30)

private theorem SepWPp.call_frame_inImage_nopanic {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_frame_frozen_nopanic hF hsym hcall hpc hrun hsp hlr
    (φ := (img.FrozenLoaded s ∧ s.symtab = img.symtab) ∧ φ)
    (T := T) (F := F) ?_ ⟨⟨hF, hsym⟩, hφ⟩ hP hpan_false hexit_false hnext hoom_false
  dsimp only [Spec.inImage]
  rw [hspec, pure_sepConj_pure_assoc]

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_err_tail_dup_ok_trap {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr outPtr errsPtr prevStatesPtr
    w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000017#64) :
    SepWPp (trTrapProgAt b C abs) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
       ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗
       ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗
       memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (coroPtr + 0xf8#64) 344 ∗
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          words6At outPtr 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x250#64) 20 ∗
          memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
          stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  refine SepWPp.weaken_frame
    (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG recSt)
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) w0 w1 w2
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine SepWPp.weaken_frame (Entails.of_eq hrepack278) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64))) (by sep_focus)
    ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 =>
    SepWPp.exists_elim fun u_250 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 =>
    SepWPp.exists_elim fun u_370 => ?_
  refine SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hstep1 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_tail_dup_a_wp_trap b C abs s coroPtr errsPtr recG.localIk.cap
    (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
    (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    w3 w4 u_250 u_258 u_370 u_378 u_384 u_38c
    (w0.extractLsb' 0 32) (w2.extractLsb' 32 32) u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc hrun hsp_align hx19 hx24 hx25 hx28
  refine SepWPp.bind_sepWP_frame hF hsym hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, hx28_1, _,
    hx30_1⟩
  have hpack_ss :
      ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG recSt ⊢
      sessionStateAt A (coroPtr + 0xf8#64) recG recSt := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG recSt hinl
  refine SepWPp.weaken_frame hpack_ss (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (words6_entails_memRegion48 (s.sp + 0x270#64) 0x8000000000000017#64 w0 w1 w2 w3 w4)
    (by sep_focus) ?_
  have hfold250 :
      ((s.sp + 0x250#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ w2.extractLsb' 32 32) ⊢
      memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion20_fold (s.sp + 0x250#64)
        (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        (w2.extractLsb' 32 32)
  refine SepWPp.weaken_frame hfold250 (by sep_focus) ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1_s]; exact hsp_align
  have hx25_1' : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_1, hsp1_s]
  have hcommon := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_err_tail_common_ok_trap img b C abs hA
    s0 s1 coroPtr outPtr 0x8000000000000017#64 prevStatesPtr
    w0 w1 w2 w3 w4 b_2c0 recG recSt
    hF1 hsym1 hpc1 hrun1 hsp1_align (htr1_s.trans htr)
    hx0_1 hx19_1 hx22_1 hx25_1' (hx26_1.trans hx26) hx28_1 hx30_1
  rw [hsp1_s] at hcommon
  refine SepWPp.ret_sepWPp_frame hcommon (by sep_focus)
    fun sf hpcf hrunf ⟨hspf, htrf, hcc, hFf, hsymf⟩ => ?_
  exact ⟨Entails.of_eq (eq_of_sep_emp (by sep_focus)), hspf, htrf, hcc, hFf, hsymf⟩

set_option maxHeartbeats 4000000 in
/-- Duplicate-Error Tail (`+0x34dc#64 -> s0.readReg64 .x30` when `errs.len = 0`): Executes `p3_err_tail_dup_a_wp` (`+0x34dc#64 -> SessionStructure> [local#5]`) and chains
`stageP3_err_tail_common_ok` (`SessionStructure> [local#5] -> s0.readReg64 .x30`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_err_tail_dup_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto) (ctl
  : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr outPtr errsPtr prevStatesPtr
    w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000017#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
       ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗
       ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗
       memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (coroPtr + 0xf8#64) 344 ∗
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          words6At outPtr 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x250#64) 20 ∗
          memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
          stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_err_tail_dup_ok_trap img b C abs
      hA s0 s coroPtr outPtr errsPtr prevStatesPtr w0 w1 w2 w3 w4 b_2c0 recG recSt hF hsym hpc hrun
      hsp_align htr hx19 hx24 hx25 hx26 hx28)

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_err_dup_ok_trap {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr outPtr errsPtr prevStatesPtr : BitVec 64)
    (ratVer counter : BitVec 32)
    (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (trTrapProgAt b C abs) (s0.readReg64 .x30) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       vecResultAt A (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ∗
       sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
         stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
          memRegion (s.sp + 0xa90#64) 344 ∗ memRegion (coroPtr + 0xf8#64) 344 ∗
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          recordResultAt A outPtr (.error (.duplicatedMessage ratVer counter)) ∗
          memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
          memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗ stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hdecomp :
      vecResultAt A (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ c : BitVec 64,
          words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
            speAt A (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝ ∗
        ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
        ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗
        ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗ H := by
    have h1 := speAt_decomp6 A (utf8 "decrypt") (s.sp + 0x270#64)
      (.duplicatedMessage ratVer counter) (by nofun)
    dsimp only [vecResultAt, speTag, speWord] at h1 ⊢
    refine Entails.trans h1 ?_
    apply Entails.sepExists_elim; intro w0
    apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2
    apply Entails.sepExists_elim; intro w3
    apply Entails.sepExists_elim; intro w4
    apply Entails.sepExists_elim; intro H
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3
        (Entails.sepExists_right w4 (Entails.sepExists_right H ?_)))))
    unfold words6At
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    exact Entails.refl _
  refine SepWPp.weaken_frame hdecomp (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
    SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun w3 =>
    SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun H => ?_
  refine SepWPp.weaken_frame
    (P₁ := ⌜∀ c : BitVec 64,
      words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
        speAt A (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝)
    (P₂ := ⌜∀ c : BitVec 64,
      words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
        speAt A (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hreassemble => ?_
  have hstep1 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_dup_wp_trap b C abs s coroPtr outPtr
    hpc hrun hsp_align hx19 hx24
  refine SepWPp.bind_sepWP_frame hF hsym hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, hx24_1, hx25_1, hx26_1, _, hx28_1, _, hx30_1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hdropSs3 := CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.drop_session_structure3_ok_trap
    (b := b) (C := C) (abs := abs) hA
  have hpc1_drop : s1.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name := by
    rw [hpc1, trTrapProgAt, Program.fnAddr_rebase, (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")]
  refine SepWPp.call_frame_frozen_nopanic
    (x := (⟨s.sp + 0xa90#64, G₂, st₂⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ A.pool ∗
      stackAt s.sp dropSessionStructure2Stack)
    hF1 hsym1 hdropSs3 hpc1_drop hrun1 hsp1_al hx30_1
    (by dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec]; rw [hsp1_s])
    hx0_1 (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 hsp2_al hcs2 hF2 hsym2 => ?_)
  dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec]
  rw [hsp1_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, _, hx28_cs2, _, _⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx24_2 : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_cs2, hx24_1, hsp2_s]
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hsp2_s]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans hx26_1
  have hx28_2 : s2.readReg64 .x28 = 0x8000000000000017#64 := hx28_cs2.trans hx28_1
  have htail := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_err_tail_dup_ok_trap img b C abs hA
    s0 s2 coroPtr outPtr errsPtr prevStatesPtr w0 w1 w2 w3 w4 b_2c0 recG recSt
    hF2 hsym2 hpc2 hrun2 hsp2_align (htr2_1.trans (htr1_s.trans htr))
    hx19_2 hx24_2 hx25_2 hx26_2 hx28_2
  rw [hsp2_s] at htail
  refine SepWPp.ret_sepWPp_frame htail (by sep_focus)
    fun sf hpcf hrunf ⟨hspf, htrf, hcc, hFf, hsymf⟩ => ?_
  have hrec : words6At outPtr 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
      recordResultAt A outPtr (.error (.duplicatedMessage ratVer counter)) :=
    hreassemble outPtr
  exact ⟨entails_replace_sub hrec (by sep_focus) (eq_of_sep_emp (by sep_focus)),
    hspf, htrf, hcc, hFf, hsymf⟩

set_option maxHeartbeats 4000000 in
/-- Substage P3.5 duplicate-message error path (`+0x1cd8#64 → s0.readReg64 .x30`): composes `p3_err_dup_wp`, `drop_session_structure3_ok` on `s.sp + 0xa90#64`, and `stageP3_err_tail_dup_ok` (`+0x34dc#64 → s0.readReg64 .x30`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_err_dup_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto) (ctl
  : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr outPtr errsPtr prevStatesPtr : BitVec 64)
    (ratVer counter : BitVec 32)
    (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 .x30) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       vecResultAt A (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ∗
       sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
         stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
          memRegion (s.sp + 0xa90#64) 344 ∗ memRegion (coroPtr + 0xf8#64) 344 ∗
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          recordResultAt A outPtr (.error (.duplicatedMessage ratVer counter)) ∗
          memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
          memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗ stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_err_dup_ok_trap img b C abs
      hA s0 s coroPtr outPtr errsPtr prevStatesPtr ratVer counter b_2c0 G₂ recG st₂ recSt hF hsym
      hpc hrun hsp_align htr hx19 hx24)

/-! ## 2. Non-Duplicate & Unified Error Paths (`stageP3_sub5_err_ok`) -/

private theorem growOneSpe_pre_zero_eq (A : RustAlloc) (s : State) (v ptr : BitVec 64)
    (hx0 : s.readReg64 .x0 = v) (hptr : ptr ≠ 0) :
    (growOneSpeSpec A).pre (v, 0#64, ptr, []) s =
      (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ A.pool ∗ stackAt s.sp growOneSpeStack := by
  dsimp only [growOneSpeSpec]
  have hp : (s.readReg64 .x0 = v ∧ ([] : List (BitVec 8)).length = (0#64 : BitVec 64).toNat * 48 ∧
      ptr ≠ 0 ∧ max (2 * (0#64 : BitVec 64).toNat) 4 * 48 + 8 ≤ 2 ^ 63) = True :=
    propext ⟨fun _ => trivial, fun _ => ⟨hx0, rfl, hptr, by decide⟩⟩
  have hif : ((0#64 : BitVec 64) = 0) = True := propext ⟨fun _ => trivial, fun _ => rfl⟩
  simp only [hp, pure_true, hif, ite_true, emp_sepConj, sepConj_emp, sepConj_assoc]

private theorem growOneSpe_post_zero_eq (A : RustAlloc) (s0 sf : State) (v ptr : BitVec 64) :
    (growOneSpeSpec A).post (v, 0#64, ptr, []) s0 sf =
      ⌜sf.trace = s0.trace⌝ ∗
      ∃∗ p' : BitVec 64,
        ⌜p' ≠ 0⌝ ∗ (v ↦₆₄ 4#64) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' 192 8 ∗ memRegion p' 192 ∗ A.pool ∗ stackAt s0.sp growOneSpeStack := by
  dsimp only [growOneSpeSpec]
  have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
  simp only [h0, Nat.mul_zero, Nat.sub_zero, show max 0 4 = 4 from rfl,
    show 4 * 48 = 192 from rfl, show ([] : List (BitVec 8)).length = 0 from rfl,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero, pointsToBytes_nil,
    emp_sepConj, sepConj_emp, sepConj_assoc]

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_err_tail_nondup_dec_ok_trap {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr outPtr errsPtr prevStatesPtr w0 w1 w2 w3 w4 : BitVec 64)
    (e : SignalProtocolError) (_he_npan : e ≠ .panic)
    (b_2c0 : BitVec 8)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000018#64) :
    SepWPp (trTrapProgAt b C abs) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ A.live errsPtr 192 8 ∗
       speAt A (utf8 "decrypt") errsPtr e ∗ memRegion (errsPtr + 0x30#64) 144 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗
       ((s.sp + 0x278#64) ↦₆₄ w0) ∗ ((s.sp + 0x280#64) ↦₆₄ w1) ∗
       ((s.sp + 0x288#64) ↦₆₄ w2) ∗ ((s.sp + 0x290#64) ↦₆₄ w3) ∗
       ((s.sp + 0x298#64) ↦₆₄ w4) ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
         stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ memRegion (coroPtr + 0xf8#64) 344 ∗
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          words6At outPtr 0x8000000000000018#64 w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x250#64) 20 ∗
          memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
          stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  refine SepWPp.weaken_frame
    (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG recSt)
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  refine SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) w0 w1 w2
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine SepWPp.weaken_frame (Entails.of_eq hrepack278) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64))) (by sep_focus)
    ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 =>
    SepWPp.exists_elim fun u_250 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 =>
    SepWPp.exists_elim fun u_370 => ?_
  have hstep1 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_tail_nondup_a1_wp_trap b C abs s coroPtr errsPtr
    hpc hrun hsp_align hx19
  refine SepWPp.bind_sepWP_frame hF hsym hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, hx21_1, hx22_1, hx23_1,
    hx24_1, hx25_1, hx26_1, _, hx28_1, _, hx30_1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hdropSpe := CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_spe2_ok_trap
    (img := img) (C := C) (abs := abs) himg hA
  have hpc1_drop : s1.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.dropSpe2Name := by
    rw [hpc1, ← hb, trTrapProgAt, Program.fnAddr_rebase, (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")]
  rw [← hb] at hdropSpe hpc1_drop
  have hstack_drop :
      stackAt s.sp dropSessionStructure2Stack =
        memRegion (s.sp - 4192#64) 64 ∗ stackAt s.sp dropSpeStack := by
    exact stackAt_split_bottom s.sp dropSpeStack 64 (by decide)
  refine SepWPp.weaken_frame (Entails.of_eq hstack_drop) (by sep_focus) ?_
  refine SepWPp.call_frame_inImage_nopanic
    (spec := dropSpeSpec A)
    (x := (⟨errsPtr, utf8 "decrypt", e⟩ : DropSpeGhost))
    (T := speAt A (utf8 "decrypt") errsPtr e ∗ A.pool ∗ stackAt s.sp dropSpeStack)
    hF1 hsym1 hdropSpe hpc1_drop hrun1 hsp1_al hx30_1
    (by dsimp only [dropSpeSpec]; rw [hsp1_s])
    hx0_1
    (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 hsp2_al hcs2 hF2 hsym2 => ?_)
  dsimp only [dropSpeSpec]
  rw [hsp1_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hjoin192 :
      memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 144 ⊢
        memRegion errsPtr 192 := by
    rw [ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144)
          (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine SepWPp.weaken_frame hjoin192 (by sep_focus) ?_
  have hstack_alloc :
      stackAt s.sp dropSpeStack =
        memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack := by
    exact stackAt_split_bottom s.sp allocHookStack 32 (by decide)
  refine SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2, hx25_cs2, hx26_cs2, _,
    hx28_cs2, _, _⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx21_2 : s2.readReg64 .x21 = errsPtr := hx21_cs2.trans hx21_1
  have hx22_2 : s2.readReg64 .x22 = errsPtr := hx22_cs2.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = 1#64 := hx23_cs2.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_cs2, hx24_1, hx24, hsp2_s]
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hx25, hsp2_s]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans (hx26_1.trans hx26)
  have hx28_2 : s2.readReg64 .x28 = 0x8000000000000018#64 := hx28_cs2.trans (hx28_1.trans hx28)
  have hstep3 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_tail_nondup_a2_wp_trap b C abs hA s2 coroPtr errsPtr recG.localIk.cap
    (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
    (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    w3 w4 u_250 u_258 u_370 u_378 u_384 u_38c
    (w0.extractLsb' 0 32) (w2.extractLsb' 32 32) u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc2 hrun2 hsp2_align
    hx19_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx28_2
  rw [hsp2_s] at hstep3
  refine SepWPp.bind_sepWP_frame hF2 hsym2 hstep3 (by sep_focus)
    fun s3 hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx22_3, _, hx25_3, hx26_3, _, hx28_3, _,
    hx30_3⟩
  have hstack_restore :
      memRegion (s.sp - 4192#64) 64 ∗ memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack ⊢
        stackAt s.sp dropSessionStructure2Stack := by
    rw [hstack_drop, hstack_alloc]; exact Entails.refl _
  refine SepWPp.weaken_frame hstack_restore (by sep_focus) ?_
  have hpack_ss :
      ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG recSt ⊢
      sessionStateAt A (coroPtr + 0xf8#64) recG recSt := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG recSt hinl
  refine SepWPp.weaken_frame hpack_ss (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (words6_entails_memRegion48 (s.sp + 0x270#64) 0x8000000000000018#64 w0 w1 w2 w3 w4)
    (by sep_focus) ?_
  have hfold250 :
      ((s.sp + 0x250#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ w2.extractLsb' 32 32) ⊢
      memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion20_fold (s.sp + 0x250#64)
        (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        (w2.extractLsb' 32 32)
  refine SepWPp.weaken_frame hfold250 (by sep_focus) ?_
  have hsp3_s : s3.sp = s.sp := hsp3_2
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = s3.sp + 0x210#64 := by rw [hx25_3, hsp3_s]
  have hcommon := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_err_tail_common_ok_trap img b C abs hA
    s0 s3 coroPtr outPtr 0x8000000000000018#64 prevStatesPtr
    w0 w1 w2 w3 w4 b_2c0 recG recSt
    hF3 hsym3 hpc3 hrun3 hsp3_align
    (htr3_2.trans (htr2_1.trans (htr1_s.trans htr)))
    hx0_3 hx19_3 hx22_3 hx25_3' (hx26_3.trans hx26_2) hx28_3 hx30_3
  rw [hsp3_s] at hcommon
  refine SepWPp.ret_sepWPp_frame hcommon (by sep_focus)
    fun sf hpcf hrunf ⟨hspf, htrf, hcc, hFf, hsymf⟩ => ?_
  exact ⟨Entails.of_eq (eq_of_sep_emp (by sep_focus)), hspf, htrf, hcc, hFf, hsymf⟩

set_option maxHeartbeats 8000000 in
/-- Substage P3.5 non-duplicate error tail (`+0x34dc#64 → s0.readReg64 .x30`): composes `p3_err_tail_nondup_a1_wp`, `drop_spe2_ok`, `p3_err_tail_nondup_a2_wp` (deallocating `errsPtr`), and `stageP3_err_tail_common_ok`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_err_tail_nondup_dec_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C :
  Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr outPtr errsPtr prevStatesPtr w0 w1 w2 w3 w4 : BitVec 64)
    (e : SignalProtocolError) (_he_npan : e ≠ .panic)
    (b_2c0 : BitVec 8)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000018#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ A.live errsPtr 192 8 ∗
       speAt A (utf8 "decrypt") errsPtr e ∗ memRegion (errsPtr + 0x30#64) 144 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗
       ((s.sp + 0x278#64) ↦₆₄ w0) ∗ ((s.sp + 0x280#64) ↦₆₄ w1) ∗
       ((s.sp + 0x288#64) ↦₆₄ w2) ∗ ((s.sp + 0x290#64) ↦₆₄ w3) ∗
       ((s.sp + 0x298#64) ↦₆₄ w4) ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
         stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ memRegion (coroPtr + 0xf8#64) 344 ∗
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          words6At outPtr 0x8000000000000018#64 w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x250#64) 20 ∗
          memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
          stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_err_tail_nondup_dec_ok_trap img
      b C abs himg hb hA s0 s coroPtr outPtr errsPtr prevStatesPtr w0 w1 w2 w3 w4 e _he_npan b_2c0
      recG recSt hF hsym hpc hrun hsp_align htr hx19 hx24 hx25 hx26 hx28)

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_err_nondup_ok_trap {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (htag_ne23 : speTag e ≠ speWord 23)
    (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (trTrapProgAt b C abs) (s0.readReg64 .x30) s
      (stageP3ErrPre A b s0 s coroPtr outPtr initErrsPtr prevStatesPtr e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        (P_f ⊢ stageP3ErrPost A b s0 s coroPtr outPtr prevStatesPtr e) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  unfold stageP3ErrPre stageP3ErrPost
  have hrec_err : SessionState.recordError .preKey e = .invalidMessage .preKey .decryptionFailed :=
    recordError_preKey_of_speTag_ne_speWord23 he_npan htag_ne23
  rw [hrec_err]
  have hb_align : b &&& 0xfff#64 = 0#64 := hb ▸ ProofLib.ObjectLoad.base_aligned_of_loads himg
  refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.SepWPp.intro_rodata_5ac90_5ac98 himg hb hF ?_
  have hdecomp :
      vecResultAt A (s.sp + 0x270#64) (.error e) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ c : BitVec 64,
          words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢
            speAt A (utf8 "decrypt") c e⌝ ∗ ((s.sp + 0x270#64) ↦₆₄ speTag e) ∗
        ((s.sp + 0x278#64) ↦₆₄ w0) ∗ ((s.sp + 0x280#64) ↦₆₄ w1) ∗
        ((s.sp + 0x288#64) ↦₆₄ w2) ∗ ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗
          H := by
    have h1 := speAt_decomp6 A (utf8 "decrypt") (s.sp + 0x270#64) e he_npan
    dsimp only [vecResultAt] at h1 ⊢
    refine Entails.trans h1 ?_
    apply Entails.sepExists_elim; intro w0
    apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2
    apply Entails.sepExists_elim; intro w3
    apply Entails.sepExists_elim; intro w4
    apply Entails.sepExists_elim; intro H
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3
        (Entails.sepExists_right w4 (Entails.sepExists_right H ?_)))))
    unfold words6At
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    exact Entails.refl _
  refine SepWPp.weaken_frame hdecomp (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
    SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun w3 =>
    SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun H => ?_
  refine SepWPp.weaken_frame
    (P₁ := ⌜∀ c : BitVec 64,
      words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢
        speAt A (utf8 "decrypt") c e⌝)
    (P₂ := ⌜∀ c : BitVec 64,
      words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢
        speAt A (utf8 "decrypt") c e⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hreassemble => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x930#64)))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u930 => SepWPp.exists_elim fun u938 =>
    SepWPp.exists_elim fun u940 => SepWPp.exists_elim fun u948 =>
    SepWPp.exists_elim fun u950 => SepWPp.exists_elim fun u958 => ?_
  have hstep1 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_nondup_a_wp_trap b C abs s coroPtr outPtr (speTag e)
    w0 w1 w2 w3 w4 u930 u938 u940 u948 u950 u958
    hb_align (speTag_ne_ok_of_ne_panic he_npan) htag_ne23 hpc hrun hsp_align hx19 hx24
  refine SepWPp.bind_sepWP_frame hF hsym hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, _, _, _, _, _, hx19_1, hx24_1, hx25_1, hx26_1, _, _, _,
    hx30_1⟩
  refine SepWPp.weaken_frame
    (words6_entails_memRegion48 (s.sp + 0x930#64) (speTag e) w0 w1 w2 w3 w4)
    (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hlog : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName)
      ((ResponderStore.pqxdhLogClosureSpec img).inImage img) :=
    hb ▸ CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdh_log_closure_ok_trap himg
  have hpc1_log : s1.pc =
    (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName := by
    rw [hpc1, trTrapProgAt, Program.fnAddr_rebase,
      show libsignalSessionCode.fnOff CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName = (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}") from
        (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hstack_log :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp ResponderStore.pqxdhClosureStack := by
    exact stackAt_split_bottom s.sp ResponderStore.pqxdhClosureStack 4176 (by decide)
  have hlogOff_eq : logOff img = ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) := by
    dsimp only [logOff, CryptoVerification.LibsignalSession.logFilterAddr]
    rw [hb]
  refine SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine SepWPp.call_frame_inImage_nopanic
    (spec := ResponderStore.pqxdhLogClosureSpec img)
    (x := ())
    (φ := True)
    (T := ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ stackAt s.sp ResponderStore.pqxdhClosureStack)
    hF1 hsym1 hlog hpc1_log hrun1 hsp1_al hx30_1
    (by dsimp only [ResponderStore.pqxdhLogClosureSpec]; rw [hlogOff_eq, hsp1_s, pure_true,
      emp_sepConj])
    trivial
    (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 hsp2_al hcs2 hF2 hsym2 => ?_)
  dsimp only [ResponderStore.pqxdhLogClosureSpec]
  rw [hlogOff_eq, hsp1_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hstack_restore1 :
      memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp ResponderStore.pqxdhClosureStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_log]; exact Entails.refl _
  refine SepWPp.weaken_frame hstack_restore1 (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, _, _, _, _⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx24_2 : s2.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs2.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs2.trans hx25_1
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans hx26_1
  have hstep3 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_nondup_b_wp_trap b C abs s2 coroPtr
    hpc2 hrun2 hsp2_align hx19_2
  rw [hsp2_s] at hstep3
  refine SepWPp.bind_sepWP_frame hF2 hsym2 hstep3 (by sep_focus)
    fun s3 hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx21_3, hx24_3, hx25_3, hx26_3, _, _, _,
    hx30_3⟩
  have hsp3_s : s3.sp = s.sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3_s] using hsp_align
  have hgrow := FromRecordCallees.grow_one_spe_ok_trap
    (b := b) (C := C) (abs := abs) hA
  have hpc3_grow : s3.pc = (trTrapProgAt b C abs).fnAddr growOneSpeName := by
    rw [hpc3, trTrapProgAt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x15c44]
  have htr3_0 : s3.trace = s0.trace := htr3_2.trans (htr2_1.trans (htr1_s.trans htr))
  refine SepWPp.call_frame_frozen_oom
    (x := (s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8))))
    (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
          A.pool ∗ stackAt s.sp growOneSpeStack)
    hF3 hsym3 htr3_0 hgrow hpc3_grow hrun3 hsp3_al hx30_3
    (by
      rw [growOneSpe_pre_zero_eq A s3 (s.sp + 0x3c8#64) initErrsPtr hx0_3 hinit_ne, hsp3_s,
        pure_true, emp_sepConj]
      simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial
    (by sep_focus)
    (hnext := fun s4 hpc4 hrun4 hsp4_3 hsp4_al hcs4 hF4 hsym4 => ?_)
  rw [growOneSpe_post_zero_eq A s3 s4 (s.sp + 0x3c8#64) initErrsPtr, hsp3_s]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => ?_
  refine SepWPp.pure_elim fun htr4_3 => ?_
  refine SepWPp.pure_elim fun _ => ?_
  have hsplit192 :
      memRegion errsPtr 192 =
        memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 144 := by
    rw [ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144)
          (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]
  refine SepWPp.weaken_frame (Entails.of_eq hsplit192) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq errsPtr))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e1 =>
    SepWPp.exists_elim fun e2 => SepWPp.exists_elim fun e3 =>
    SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 => ?_
  have hsp4_s : s4.sp = s.sp := hsp4_3.trans hsp3_s
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4_s]; exact hsp_align
  rcases hcs4 with ⟨hx19_cs4, _, hx21_cs4, _, _, hx24_cs4, hx25_cs4, hx26_cs4, _, _, _, _⟩
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hx19_cs4.trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = 0#64 := hx21_cs4.trans hx21_3
  have hx24_4 : s4.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs4.trans (hx24_3.trans hx24_2)
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x210#64 := by
    rw [hx25_cs4, hx25_3, hx25_2, hsp4_s]
  have hx26_4 : s4.readReg64 .x26 = outPtr := hx26_cs4.trans (hx26_3.trans hx26_2)
  have hstep5 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_nondup_c_wp_trap b C abs s4 coroPtr errsPtr (speTag e)
    w0 w1 w2 w3 w4 e0 e1 e2 e3 e4 e5
    hb_align hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx25_4
  rw [hsp4_s] at hstep5
  refine SepWPp.bind_sepWP_frame hF4 hsym4 hstep5 (by sep_focus)
    fun s5 hpc5 hrun5 hF5 hsym5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5_4, htr5_4, hx0_5, hx1_5, hx19_5, hx24_5, hx25_5, hx26_5, _, _, _⟩
  have hsp5_s : s5.sp = s.sp := hsp5_4
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5_s]; exact hsp_align
  have htr5_0 : s5.trace = s0.trace := htr5_4.trans (htr4_3.trans htr3_0)
  have hreasm_errs :
      ((errsPtr + 0x0#64) ↦₆₄ speTag e) ∗ ((errsPtr + 0x8#64) ↦₆₄ w0) ∗
      ((errsPtr + 0x10#64) ↦₆₄ w1) ∗ ((errsPtr + 0x18#64) ↦₆₄ w2) ∗
      ((errsPtr + 0x20#64) ↦₆₄ w3) ∗ ((errsPtr + 0x28#64) ↦₆₄ w4) ∗ H ⊢
      speAt A (utf8 "decrypt") errsPtr e := by
    simpa only [words6At, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      using hreassemble errsPtr
  refine SepWPp.weaken_frame hreasm_errs (by sep_focus) ?_
  have hstack_alloc :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack := by
    exact stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have halloc17 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_2eac_ok_trap (A := A) img b C abs hA s0 s5
    emp hF5 hsym5 hpc5 hrun5 hsp5_align htr5_0 hx0_5 hx1_5
  rw [sepConj_emp, hsp5_s] at halloc17
  refine SepWPp.bind_sepWPp_frame_raw
    halloc17 (by sep_focus)
    fun s6 P_m6 hpc6 hrun6 ⟨hP6, hdf_ne, hsp6_5, htr6_5, hcs6, hF6, hsym6⟩ => ?_
  rw [sepConj_emp] at hP6
  refine SepWPp.weaken_frame hP6 (by sep_focus) ?_
  have hstack_restore2 :
      memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_alloc]; exact Entails.refl _
  refine SepWPp.weaken_frame hstack_restore2 (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (memRegion17_split_eq (s6.readReg64 .x0)))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun df_10 => SepWPp.exists_elim fun df_8 =>
    SepWPp.exists_elim fun df_0 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (cell_split_head8 (s.sp + 0x290#64) w3))
    (by sep_focus) ?_
  have hsp6_s : s6.sp = s.sp := hsp6_5
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6_s]; exact hsp_align
  rcases hcs6 with ⟨hx19_cs6, _, _, _, _, hx24_cs6, hx25_cs6, hx26_cs6, _, _, _, _⟩
  have hx19_6 : s6.readReg64 .x19 = coroPtr := hx19_cs6.trans hx19_5
  have hx24_6 : s6.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs6.trans (hx24_5.trans hx24_4)
  have hx25_6 : s6.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs6.trans hx25_5
  have hx26_6 : s6.readReg64 .x26 = outPtr := hx26_cs6.trans (hx26_5.trans hx26_4)
  have hstep7 := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_err_nondup_d_wp_trap b C abs s6 coroPtr (s6.readReg64 .x0)
    0x6974707972636564#64 0x656c696166206e6f#64
    df_0 df_8 (speTag e) w0 w1 w2 df_10 (w3.extractLsb' 0 8)
    hb_align hdf_ne hpc6 hrun6 hsp6_align rfl hx19_6
  rw [hsp6_s] at hstep7
  refine SepWPp.bind_sepWP_frame hF6 hsym6 hstep7 (by sep_focus)
    fun s7 hpc7 hrun7 hF7 hsym7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6, htr7_6, hx0_7, hx19_7, hx24_7, hx25_7, hx26_7, _, hx28_7, _, hx30_7⟩
  have hsp7_s : s7.sp = s.sp := hsp7_6
  have hsp7_al : s7.spAligned = true := by simpa only [State.spAligned, hsp7_s] using hsp_align
  refine SepWPp.drop_frame
    (P_drop := ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) ↦₆₄ᵣ 0x6974707972636564#64) ∗
               ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8)) ↦₆₄ᵣ 0x656c696166206e6f#64))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (dfPtr_words_eq_decryptionFailedStr (s6.readReg64 .x0)))
    (by sep_focus) ?_
  obtain ⟨w3', hw3'_unpack, hw3'_join⟩ := cell_join_head8 3#8 w3
  have hw3'_head : w3'.extractLsb' 0 8 = 3#8 := extractLsb0_8_of_unpack64_cons hw3'_unpack
  refine SepWPp.weaken_frame (Entails.of_eq (hw3'_join (s.sp + 0x290#64))) (by sep_focus) ?_
  have hdropSs3 := CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.drop_session_structure3_ok_trap
    (b := b) (C := C) (abs := abs) hA
  have hpc7_drop : s7.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name := by
    rw [hpc7, trTrapProgAt, Program.fnAddr_rebase, (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")]
  have hstack_drop2 :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack := by
    exact stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine SepWPp.call_frame_frozen_nopanic
    (x := (⟨s.sp + 0xa90#64, G₂, st₂⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ A.pool ∗
      stackAt s.sp dropSessionStructure2Stack)
    hF7 hsym7 hdropSs3 hpc7_drop hrun7 hsp7_al hx30_7
    (by dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec]; rw [hsp7_s])
    hx0_7 (by sep_focus)
    (hnext := fun s8 hpc8 hrun8 hsp8_7 hsp8_al hcs8 hF8 hsym8 => ?_)
  dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec]
  rw [hsp7_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr8_7 => ?_
  have hsp8_s : s8.sp = s.sp := hsp8_7.trans hsp7_s
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8_s]; exact hsp_align
  rcases hcs8 with ⟨hx19_cs8, _, _, _, _, hx24_cs8, hx25_cs8, hx26_cs8, _, hx28_cs8, _, _⟩
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hx19_cs8.trans hx19_7
  have hx24_8 : s8.readReg64 .x24 = s8.sp + 0x370#64 := by
    rw [hx24_cs8, hx24_7, hx24_6, hsp8_s]
  have hx25_8 : s8.readReg64 .x25 = s8.sp + 0x210#64 := by
    rw [hx25_cs8, hx25_7, hx25_6, hsp8_s]
  have hx26_8 : s8.readReg64 .x26 = outPtr := hx26_cs8.trans (hx26_7.trans hx26_6)
  have hx28_8 : s8.readReg64 .x28 = 0x8000000000000018#64 := hx28_cs8.trans hx28_7
  have htail := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_err_tail_nondup_dec_ok_trap img b C abs himg hb hA
    s0 s8 coroPtr outPtr errsPtr prevStatesPtr
    17#64 (s6.readReg64 .x0) 17#64 w3' w4 e he_npan b_2c0 recG recSt
    hF8 hsym8 hpc8 hrun8 hsp8_align
    (htr8_7.trans (htr7_6.trans (htr6_5.trans htr5_0)))
    hx19_8 hx24_8 hx25_8 hx26_8 hx28_8
  rw [hsp8_s] at htail
  refine SepWPp.ret_sepWPp_frame htail (by sep_focus)
    fun sf hpcf hrunf ⟨hspf, htrf, hcc, hFf, hsymf⟩ => ?_
  have hrec := words6At_preKey_decryptionFailed_entails_recordResultAt A
    outPtr (s6.readReg64 .x0) w3' w4 hdf_ne hw3'_head
  have hstack_restore3 :
      memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_drop2]; exact Entails.refl _
  refine ⟨?_, hspf, htrf, hcc, hFf, hsymf⟩
  refine Entails.sepExists_right 4#64 (Entails.sepExists_right errsPtr
    (Entails.sepExists_right 1#64 ?_))
  refine Entails.trans (entails_replace_sub hrec (by sep_focus) rfl) ?_
  exact entails_replace_sub hstack_restore3 (by sep_focus) (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 8000000 in
/-- Substage P3.5 non-duplicate error path (`+0x1cd8#64 → s0.readReg64 .x30`): for `e ≠ .panic` with `speTag e ≠ speWord 23`, logs via `pqxdh_log_closure_ok`, grows `errs` to capacity 4 via `grow_one_spe_ok`, moves `speAt` into `errsPtr`, allocates `"decryption failed"` (`17` B), drops the cloned `SessionState` at `s.sp + 0xa90#64`, and finishes via `stageP3_err_tail_nondup_dec_ok`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_err_nondup_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
  (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (htag_ne23 : speTag e ≠ speWord 23)
    (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 .x30) s
      (stageP3ErrPre A b s0 s coroPtr outPtr initErrsPtr prevStatesPtr e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        (P_f ⊢ stageP3ErrPost A b s0 s coroPtr outPtr prevStatesPtr e) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_err_nondup_ok_trap img b C
      abs himg hb hA s0 s coroPtr outPtr initErrsPtr prevStatesPtr hinit_ne e he_npan htag_ne23
      b_2c0 G₂ recG st₂ recSt hF hsym hpc hrun hsp_align htr hx19 hx24)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_err_ok_trap {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0)
    (e : SignalProtocolError) (he_npan : e ≠ .panic)
    (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (trTrapProgAt b C abs) (s0.readReg64 .x30) s
      (stageP3ErrPre A b s0 s coroPtr outPtr initErrsPtr prevStatesPtr e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        (P_f ⊢ stageP3ErrPost A b s0 s coroPtr outPtr prevStatesPtr e) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  by_cases htag23 : speTag e = speWord 23
  · obtain ⟨ratVer, counter, rfl⟩ := speTag_eq_speWord23_iff.mp htag23
    unfold stageP3ErrPre stageP3ErrPost
    have hstack_drop2 :
        stackAt s.sp growOneSpeStack =
          memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack := by
      exact stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
    rw [hstack_drop2]
    have hdup := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_err_dup_ok_trap img b C abs hA
      s0 s coroPtr outPtr initErrsPtr prevStatesPtr ratVer counter b_2c0 G₂ recG st₂ recSt
      hF hsym hpc hrun hsp_align htr hx19 hx24
    refine SepWPp.ret_sepWPp_frame hdup (by sep_focus)
      fun sf hpcf hrunf ⟨hspf, htrf, hcc, hFf, hsymf⟩ => ?_
    have herrs :
        ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
        ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ⊢
        ∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
          ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
      Entails.sepExists_right 0#64 (Entails.sepExists_right initErrsPtr
        (Entails.sepExists_right 0#64 (Entails.refl _)))
    dsimp only [SessionState.recordError]
    exact ⟨entails_replace_sub herrs (by sep_focus) (eq_of_sep_emp (by sep_focus)),
      hspf, htrf, hcc, hFf, hsymf⟩
  · exact CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_err_nondup_ok_trap img b C abs himg hb hA
      s0 s coroPtr outPtr initErrsPtr prevStatesPtr hinit_ne e he_npan htag23
      b_2c0 G₂ recG st₂ recSt hF hsym hpc hrun hsp_align htr hx19 hx24

/-- Substage P3.5 / P3.7 Unified Error Path (`stageP3_sub5_err_ok`,
  `+0x1cd8#64 -> s0.readReg64 .x30`): For any `try_decrypt_with_state` error `e ≠ .panic`, dispatches between `stageP3_sub5_err_dup_ok`
(when `e = .duplicatedMessage ratVer counter`) and `stageP3_sub5_err_nondup_ok`
(when `speTag e ≠ speWord 23`),
  establishing `recordResultAt A outPtr (.error (SessionState.recordError .preKey e))`
and returning to `s0.readReg64 .x30`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_err_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto) (ctl :
  BitVec 64)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0)
    (e : SignalProtocolError) (he_npan : e ≠ .panic)
    (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 .x30) s
      (stageP3ErrPre A b s0 s coroPtr outPtr initErrsPtr prevStatesPtr e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        (P_f ⊢ stageP3ErrPost A b s0 s coroPtr outPtr prevStatesPtr e) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_err_ok_trap img b C abs
      himg hb hA s0 s coroPtr outPtr initErrsPtr prevStatesPtr hinit_ne e he_npan
      b_2c0 G₂ recG st₂ recSt hF hsym hpc hrun hsp_align htr hx19 hx24)

abbrev _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub7_err_ok_trap := @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_err_ok_trap

abbrev _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub7_err_ok := @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_err_ok

/-!
## 3. Stage P3 Post-`tryDecrypt` Dispatch (`stageP3_sub5_dispatch_ok` & `stageP3_ok_of_parts`)
-/

private theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_dispatch_ok_ext_trap_aux {A : RustAlloc} {P : Program}
    (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hTraps : ProofLib.Variant.TrapsOnly (trTrapProgAt b C abs) P)
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0)
    (res : Except SignalProtocolError (List (BitVec 8))) (hnpan : res ≠ .error .panic)
    (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (Q : State → SepProp → Prop)
    (hOk : ∀ pt ptCap ptPtr s' P_s',
      res = .ok pt →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      s'.pc = P.fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64 →
      s'.status = .Running →
      s'.sp = s.sp →
      s'.trace = s0.trace →
      s'.readReg64 .x19 = coroPtr →
      s'.readReg64 .x24 = s.sp + 0x370#64 →
      s'.readReg64 .x25 = s.sp + 0x210#64 →
      s'.readReg64 .x26 = outPtr →
      s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
      img.FrozenLoaded s' →
      s'.symtab = img.symtab →
      (P_s' ⊢ stageP3DispatchOkMid A b s0 s coroPtr outPtr initErrsPtr prevStatesPtr ptCap ptPtr pt
        b_2c0 G₂ st₂) →
      SepWPp P (s0.readReg64 .x30) s' P_s' Q (PanicOomProp s0))
    (hErr : ∀ e sf P_f,
      res = .error e →
      e ≠ .panic →
      (P_f ⊢
        ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPost A b s0 s coroPtr outPtr prevStatesPtr e) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s0.trace →
      ClosureCalleeSaved s0 sf →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      Q sf P_f)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = P.fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp P (s0.readReg64 .x30) s
      (stageP3DispatchPre A b s0 s coroPtr outPtr initErrsPtr prevStatesPtr res b_2c0 G₂ recG st₂
        recSt)
      Q
      (PanicOomProp s0) := by
  have hpc_trap : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64 := by
    rw [hTraps.fnAddr]; exact hpc
  unfold stageP3DispatchPre
  rcases res with e | pt
  · have he_npan : e ≠ .panic := fun h => hnpan (h ▸ rfl)
    have herr := SepWPp.of_trapsOnly hTraps
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_err_ok_trap img b C abs himg hb hA
        s0 s coroPtr outPtr initErrsPtr prevStatesPtr hinit_ne e he_npan
        b_2c0 G₂ recG st₂ recSt hF hsym hpc_trap hrun hsp_align htr hx19 hx24)
    unfold stageP3ErrPre at herr
    refine SepWPp.ret_sepWPp_frame herr (by sep_focus)
      fun sf _ _ ⟨hspf, htrf, hcc, hFf, hsymf⟩ => ?_
    refine hErr e sf _ rfl he_npan ?_ hspf htrf hcc hFf hsymf
    exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
  · have hb_align : b &&& 0xfff#64 = 0#64 := hb ▸ ProofLib.ObjectLoad.base_aligned_of_loads himg
    have hstack_set :
        stackAt s.sp growOneSpeStack =
          memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack := by
      exact stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
    rw [hstack_set]
    have hok := SepWPp.of_trapsOnly hTraps
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_decResult_ok_trap img b C abs hA
        s0 s coroPtr outPtr pt G₂ recG st₂ recSt hb_align
        hF hsym hpc_trap hrun hsp_align htr hx19)
    rw [hTraps.fnAddr] at hok
    refine SepWPp.bind_sepWPp_frame_raw hok (by sep_focus)
      fun s' P_m hpc' hrun' ⟨ptCap, ptPtr, hpt_le, hpt_lt, hpt_ne, hPs',
        hsp', htr', hF', hsym', hx19', hx24', hx25', hx26', _, hx28', _⟩ => ?_
    refine hOk pt ptCap ptPtr s' _ rfl hpt_le hpt_lt hpt_ne hpc' hrun' hsp' htr'
      hx19' (hx24'.trans hx24) hx25' hx26' hx28' hF' hsym' ?_
    unfold stageP3DispatchOkMid
    rw [hstack_set]
    exact Entails.trans (sepConj_mono_left hPs') (Entails.of_eq (eq_of_sep_emp (by sep_focus)))

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_dispatch_ok_trap {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0)
    (res : Except SignalProtocolError (List (BitVec 8))) (hnpan : res ≠ .error .panic)
    (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (Q : State → SepProp → Prop)
    (hOk : ∀ pt ptCap ptPtr s' P_s',
      res = .ok pt →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      s'.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64 →
      s'.status = .Running →
      s'.sp = s.sp →
      s'.trace = s0.trace →
      s'.readReg64 .x19 = coroPtr →
      s'.readReg64 .x24 = s.sp + 0x370#64 →
      s'.readReg64 .x25 = s.sp + 0x210#64 →
      s'.readReg64 .x26 = outPtr →
      s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
      img.FrozenLoaded s' →
      s'.symtab = img.symtab →
      (P_s' ⊢ stageP3DispatchOkMid A b s0 s coroPtr outPtr initErrsPtr prevStatesPtr ptCap ptPtr pt
        b_2c0 G₂ st₂) →
      SepWPp (trTrapProgAt b C abs) (s0.readReg64 .x30) s' P_s' Q (PanicOomProp s0))
    (hErr : ∀ e sf P_f,
      res = .error e →
      e ≠ .panic →
      (P_f ⊢
        ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPost A b s0 s coroPtr outPtr prevStatesPtr e) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s0.trace →
      ClosureCalleeSaved s0 sf →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      Q sf P_f)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (trTrapProgAt b C abs) (s0.readReg64 .x30) s
      (stageP3DispatchPre A b s0 s coroPtr outPtr initErrsPtr prevStatesPtr res b_2c0 G₂ recG st₂
        recSt)
      Q
      (PanicOomProp s0) :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_dispatch_ok_ext_trap_aux img b
    C abs (ProofLib.Variant.TrapsOnly.refl _) himg hb hA s0 s coroPtr outPtr initErrsPtr
    prevStatesPtr hinit_ne res hnpan b_2c0 G₂ recG st₂ recSt Q hOk hErr hF hsym hpc hrun hsp_align
    htr hx19 hx24

/-- Stage P3 Sub5 Unified Dispatch (`stageP3_sub5_dispatch_ok`): At `+0x1cd8#64` after `try_decrypt_with_state` produces `res` (`res ≠ .error .panic`),
dispatches between `stageP3_sub5_decResult_ok` on `res = .ok pt` (stepping to `+0x34dc#64`)
and `stageP3_sub5_err_ok` on `res = .error e` (stepping to `s0.readReg64 .x30`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_dispatch_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto) (ctl
  : BitVec 64)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0)
    (res : Except SignalProtocolError (List (BitVec 8))) (hnpan : res ≠ .error .panic)
    (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (Q : State → SepProp → Prop)
    (hOk : ∀ pt ptCap ptPtr s' P_s',
      res = .ok pt →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      s'.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64 →
      s'.status = .Running →
      s'.sp = s.sp →
      s'.trace = s0.trace →
      s'.readReg64 .x19 = coroPtr →
      s'.readReg64 .x24 = s.sp + 0x370#64 →
      s'.readReg64 .x25 = s.sp + 0x210#64 →
      s'.readReg64 .x26 = outPtr →
      s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
      img.FrozenLoaded s' →
      s'.symtab = img.symtab →
      (P_s' ⊢ stageP3DispatchOkMid A b s0 s coroPtr outPtr initErrsPtr prevStatesPtr ptCap ptPtr pt
        b_2c0 G₂ st₂) →
      SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 .x30) s' P_s' Q (PanicOomProp s0))
    (hErr : ∀ e sf P_f,
      res = .error e →
      e ≠ .panic →
      (P_f ⊢
        ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPost A b s0 s coroPtr outPtr prevStatesPtr e) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s0.trace →
      ClosureCalleeSaved s0 sf →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      Q sf P_f)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 .x30) s
      (stageP3DispatchPre A b s0 s coroPtr outPtr initErrsPtr prevStatesPtr res b_2c0 G₂ recG st₂
        recSt)
      Q
      (PanicOomProp s0) :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_dispatch_ok_ext_trap_aux img b
    C abs (trapsOnly_trTrap_kit b C ctl abs) himg hb hA s0 s coroPtr outPtr initErrsPtr
    prevStatesPtr hinit_ne res hnpan b_2c0 G₂ recG st₂ recSt Q hOk hErr hF hsym hpc hrun hsp_align
    htr hx19 hx24

private theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_ok_of_parts_ext_trap_aux
    {A : RustAlloc} {P : Program} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hTraps : ProofLib.Variant.TrapsOnly (trTrapProgAt b C abs) P)
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0)
    (res : Except SignalProtocolError (List (BitVec 8)))
    (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (P_pre : SepProp) (Q : State → SepProp → Prop)
    (hPrefix :
      SepWPp P
        (P.fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64) s P_pre
        (fun s_mid P_mid =>
          (P_mid ⊢ stageP3DispatchPre A b s0 s coroPtr outPtr initErrsPtr prevStatesPtr res b_2c0 G₂
            recG st₂ recSt) ∧
          res ≠ .error .panic ∧ s_mid.sp = s.sp ∧
          s_mid.trace = s0.trace ∧ s_mid.readReg64 .x19 = coroPtr ∧
          s_mid.readReg64 .x24 = s.sp + 0x370#64 ∧ img.FrozenLoaded s_mid ∧
          s_mid.symtab = img.symtab)
        (PanicOomProp s0))
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hOk : ∀ pt ptCap ptPtr s' P_s',
      res = .ok pt →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      s'.pc = P.fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64 →
      s'.status = .Running →
      s'.sp = s.sp →
      s'.trace = s0.trace →
      s'.readReg64 .x19 = coroPtr →
      s'.readReg64 .x24 = s.sp + 0x370#64 →
      s'.readReg64 .x25 = s.sp + 0x210#64 →
      s'.readReg64 .x26 = outPtr →
      s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
      img.FrozenLoaded s' →
      s'.symtab = img.symtab →
      (P_s' ⊢ stageP3DispatchOkMid A b s0 s coroPtr outPtr initErrsPtr prevStatesPtr ptCap ptPtr pt
        b_2c0 G₂ st₂) →
      SepWPp P (s0.readReg64 .x30) s' P_s' Q (PanicOomProp s0))
    (hErr : ∀ e sf P_f,
      res = .error e →
      e ≠ .panic →
      (P_f ⊢
        ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPost A b s0 s coroPtr outPtr prevStatesPtr e) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s0.trace →
      ClosureCalleeSaved s0 sf →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      Q sf P_f) :
    SepWPp P (s0.readReg64 .x30) s P_pre Q (PanicOomProp s0) := by
  refine SepWPp.bind_sepWPp_frame
    (F := emp)
    hPrefix
    (sepConj_emp P_pre).symm
    fun s_mid hpc_mid hrun_mid ⟨hnpan, hsp_mid, htr_mid, hx19_mid, hx24_mid, hF_mid, hsym_mid⟩ => ?_
  rw [sepConj_emp]
  have hsp_align_mid : (s_mid.sp &&& 15#64 == 0#64) = true := by rw [hsp_mid]; exact hsp_align
  have hx24_mid' : s_mid.readReg64 .x24 = s_mid.sp + 0x370#64 := by rw [hx24_mid, hsp_mid]
  have hdisp := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_dispatch_ok_ext_trap_aux img b C abs hTraps himg hb hA
    s0 s_mid coroPtr outPtr initErrsPtr prevStatesPtr hinit_ne res hnpan
    b_2c0 G₂ recG st₂ recSt Q
    (fun pt ptCap ptPtr s' P_s' hres hpt_le hpt_lt hpt_ne hpc' hrun' hsp' htr'
         hx19' hx24' hx25' hx26' hx28' hF' hsym' hPs' => by
      unfold stageP3DispatchOkMid at hPs'
      rw [hsp_mid] at hsp' hx24' hx25' hPs'
      exact hOk pt ptCap ptPtr s' P_s' hres hpt_le hpt_lt hpt_ne hpc' hrun' hsp' htr'
        hx19' hx24' hx25' hx26' hx28' hF' hsym' hPs')
    (fun e sf P_f hres he_npan hPf hspf htrf hcc hFf hsymf => by
      unfold stageP3ErrPost at hPf
      rw [hsp_mid] at hPf hspf
      exact hErr e sf P_f hres he_npan hPf hspf htrf hcc hFf hsymf)
    hF_mid hsym_mid hpc_mid hrun_mid hsp_align_mid htr_mid hx19_mid hx24_mid'
  unfold stageP3DispatchPre at hdisp ⊢
  rw [hsp_mid] at hdisp
  exact hdisp

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_ok_of_parts_trap
    {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0)
    (res : Except SignalProtocolError (List (BitVec 8)))
    (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (P_pre : SepProp) (Q : State → SepProp → Prop)
    (hPrefix :
      SepWPp (trTrapProgAt b C abs)
        ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64) s P_pre
        (fun s_mid P_mid =>
          (P_mid ⊢ stageP3DispatchPre A b s0 s coroPtr outPtr initErrsPtr prevStatesPtr res b_2c0 G₂
            recG st₂ recSt) ∧
          res ≠ .error .panic ∧ s_mid.sp = s.sp ∧
          s_mid.trace = s0.trace ∧ s_mid.readReg64 .x19 = coroPtr ∧
          s_mid.readReg64 .x24 = s.sp + 0x370#64 ∧ img.FrozenLoaded s_mid ∧
          s_mid.symtab = img.symtab)
        (PanicOomProp s0))
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hOk : ∀ pt ptCap ptPtr s' P_s',
      res = .ok pt →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      s'.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64 →
      s'.status = .Running →
      s'.sp = s.sp →
      s'.trace = s0.trace →
      s'.readReg64 .x19 = coroPtr →
      s'.readReg64 .x24 = s.sp + 0x370#64 →
      s'.readReg64 .x25 = s.sp + 0x210#64 →
      s'.readReg64 .x26 = outPtr →
      s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
      img.FrozenLoaded s' →
      s'.symtab = img.symtab →
      (P_s' ⊢ stageP3DispatchOkMid A b s0 s coroPtr outPtr initErrsPtr prevStatesPtr ptCap ptPtr pt
        b_2c0 G₂ st₂) →
      SepWPp (trTrapProgAt b C abs) (s0.readReg64 .x30) s' P_s' Q (PanicOomProp s0))
    (hErr : ∀ e sf P_f,
      res = .error e →
      e ≠ .panic →
      (P_f ⊢
        ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPost A b s0 s coroPtr outPtr prevStatesPtr e) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s0.trace →
      ClosureCalleeSaved s0 sf →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      Q sf P_f) :
    SepWPp (trTrapProgAt b C abs) (s0.readReg64 .x30) s P_pre Q (PanicOomProp s0) :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_ok_of_parts_ext_trap_aux img b C abs
    (ProofLib.Variant.TrapsOnly.refl _) himg hb hA s0 s coroPtr outPtr initErrsPtr prevStatesPtr
    hinit_ne res b_2c0 G₂ recG st₂ recSt P_pre Q hPrefix hsp_align hOk hErr

/-- Stage P3 Composition (`stageP3_ok_of_parts`): Chains the Stage P3 prefix (`+0x1778#64 -> +0x1cd8#64`: `stageP3_clone_ok` +
  `stageP3_tryDecrypt_v4_ok`)
with `stageP3_sub5_dispatch_ok` (`stageP3_sub5_decResult_ok` on `Ok` -> `+0x34dc#64` and
`stageP3_sub5_err_ok` on `Err` -> `s0.readReg64 .x30`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_ok_of_parts {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto) (ctl :
  BitVec 64)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    (hA : AllocHooks A abs)
    (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0)
    (res : Except SignalProtocolError (List (BitVec 8)))
    (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (P_pre : SepProp) (Q : State → SepProp → Prop)
    (hPrefix :
      SepWPp (tripleRatchetProgAt b C ctl abs)
        ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64) s P_pre
        (fun s_mid P_mid =>
          (P_mid ⊢ stageP3DispatchPre A b s0 s coroPtr outPtr initErrsPtr prevStatesPtr res b_2c0 G₂
            recG st₂ recSt) ∧
          res ≠ .error .panic ∧ s_mid.sp = s.sp ∧
          s_mid.trace = s0.trace ∧ s_mid.readReg64 .x19 = coroPtr ∧
          s_mid.readReg64 .x24 = s.sp + 0x370#64 ∧ img.FrozenLoaded s_mid ∧
          s_mid.symtab = img.symtab)
        (PanicOomProp s0))
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hOk : ∀ pt ptCap ptPtr s' P_s',
      res = .ok pt →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      s'.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64 →
      s'.status = .Running →
      s'.sp = s.sp →
      s'.trace = s0.trace →
      s'.readReg64 .x19 = coroPtr →
      s'.readReg64 .x24 = s.sp + 0x370#64 →
      s'.readReg64 .x25 = s.sp + 0x210#64 →
      s'.readReg64 .x26 = outPtr →
      s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
      img.FrozenLoaded s' →
      s'.symtab = img.symtab →
      (P_s' ⊢ stageP3DispatchOkMid A b s0 s coroPtr outPtr initErrsPtr prevStatesPtr ptCap ptPtr pt
        b_2c0 G₂ st₂) →
      SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 .x30) s' P_s' Q (PanicOomProp s0))
    (hErr : ∀ e sf P_f,
      res = .error e →
      e ≠ .panic →
      (P_f ⊢
        ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPost A b s0 s coroPtr outPtr prevStatesPtr e) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s0.trace →
      ClosureCalleeSaved s0 sf →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      Q sf P_f) :
    SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 .x30) s P_pre Q (PanicOomProp s0) :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_ok_of_parts_ext_trap_aux img b C abs
    (trapsOnly_trTrap_kit b C ctl abs) himg hb hA s0 s coroPtr outPtr initErrsPtr prevStatesPtr
    hinit_ne res b_2c0 G₂ recG st₂ recSt P_pre Q hPrefix hsp_align hOk hErr

end P3P4

end CryptoVerification.E2E.Pqxdh.ResponderClosure
