/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Fetch
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhHChain
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHChain
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHWp
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Ext DH Commit WP Lemmas (Part 2: Sub-Segments 4 & 5)

Basic-block `SepWP` lemmas on `tripleRatchetProgAtExt b ext` for
`try_decrypt_with_state::<signal_session_handshake::Coins>` DH commit sub-segments 4–5
(`+0xaf0 .. +0xbfc → +0x3e4`).
-/

@[expose] public section

set_option autoImplicit false

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH.BS10 (setMem_trace setPC_trace
  setPState_trace spAligned_of_sp_eq writeReg32_trace writeReg64_trace)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegDhHWp2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "wp_reg" : tactic =>
  `(tactic| simp only [wp_norm,
    writeReg64_trace, writeReg32_trace, setPC_trace,
    setPState_trace, setMem_trace, State.trace_writeVReg128,
    *])

/-! ## 1. Sub-Segment 4: `+0xaf0 → +0xb04 .. +0xb94 → +0xb98` (Eviction Loop) -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.commit_step4a_lo_wp_ext
    (b : BitVec 64) (ext : String → Option (State → State))
    (sp newLen : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xaf0#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hlo : BitVec.ult newLen 6#64 = true) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xb98#64) s
      ((sp + 0x48#64) ↦₆₄ newLen)
      (fun sf P_f =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = newLen ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ ((sp + 0x48#64) ↦₆₄ newLen))) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  td_fetches_cli b (Rust.withPanics ext) hfn 0xaf0 12
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg, by wp_reg, Entails.refl _⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.commit_step4a_ge_wp_ext
    (b : BitVec 64) (ext : String → Option (State → State))
    (sp newLen : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xaf0#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hge : BitVec.ult newLen 6#64 = false) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xb04#64) s
      ((sp + 0x48#64) ↦₆₄ newLen)
      (fun sf P_f =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = sp + 0x190#64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x27 = 0xffffffffffffff98#64 ∧
        sf.readReg64 .x28 = newLen ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ ((sp + 0x48#64) ↦₆₄ newLen))) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  td_fetches_cli b (Rust.withPanics ext) hfn 0xaf0 20
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, Entails.refl _⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.commit_step4b_pre_memmove_wp_ext
    (b : BitVec 64) (ext : String → Option (State → State))
    (sp chainsPtr curLen : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 : BitVec 64)
    (s500 s508 s510 s518 s520 s528 s530 s538 s540 s548 s550 s558 : BitVec 64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xb04#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx23 : s.readReg64 .x23 = sp + 0x500#64)
    (hx24 : s.readReg64 .x24 = sp + 0x190#64)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx27 : s.readReg64 .x27 = 0xffffffffffffff98#64)
    (hx28 : s.readReg64 .x28 = curLen) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
      bv% ((2^64 + ls_off% "memmove" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64)) s
      (((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       (chainsPtr ↦₆₄ c0) ∗
       ((chainsPtr + 8#64) ↦₆₄ c1) ∗
       ((chainsPtr + 16#64) ↦₆₄ c2) ∗
       ((chainsPtr + 24#64) ↦₆₄ c3) ∗
       ((chainsPtr + 32#64) ↦₆₄ c4) ∗
       ((chainsPtr + 40#64) ↦₆₄ c5) ∗
       ((chainsPtr + 48#64) ↦₆₄ c6) ∗
       ((chainsPtr + 56#64) ↦₆₄ c7) ∗
       ((chainsPtr + 64#64) ↦₆₄ c8) ∗
       ((chainsPtr + 72#64) ↦₆₄ c9) ∗
       ((chainsPtr + 80#64) ↦₆₄ c10) ∗
       ((chainsPtr + 88#64) ↦₆₄ c11) ∗
       ((chainsPtr + 96#64) ↦₆₄ c12) ∗
       ((sp + 0x500#64) ↦₆₄ s500) ∗
       ((sp + 0x508#64) ↦₆₄ s508) ∗
       ((sp + 0x510#64) ↦₆₄ s510) ∗
       ((sp + 0x518#64) ↦₆₄ s518) ∗
       ((sp + 0x520#64) ↦₆₄ s520) ∗
       ((sp + 0x528#64) ↦₆₄ s528) ∗
       ((sp + 0x530#64) ↦₆₄ s530) ∗
       ((sp + 0x538#64) ↦₆₄ s538) ∗
       ((sp + 0x540#64) ↦₆₄ s540) ∗
       ((sp + 0x548#64) ↦₆₄ s548) ∗
       ((sp + 0x550#64) ↦₆₄ s550) ∗
       ((sp + 0x558#64) ↦₆₄ s558))
      (fun sf P_f =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x0 = chainsPtr ∧
        sf.readReg64 .x1 = chainsPtr + 104#64 ∧
        sf.readReg64 .x2 = 0xffffffffffffff98#64 + curLen * 104#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = sp + 0x500#64 ∧
        sf.readReg64 .x24 = sp + 0x190#64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x26 = c0 ∧
        sf.readReg64 .x27 = 0xffffffffffffff98#64 ∧
        sf.readReg64 .x28 = curLen ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xb4c#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
          (chainsPtr ↦₆₄ c0) ∗
          ((chainsPtr + 8#64) ↦₆₄ c1) ∗
          ((chainsPtr + 16#64) ↦₆₄ c2) ∗
          ((chainsPtr + 24#64) ↦₆₄ c3) ∗
          ((chainsPtr + 32#64) ↦₆₄ c4) ∗
          ((chainsPtr + 40#64) ↦₆₄ c5) ∗
          ((chainsPtr + 48#64) ↦₆₄ c6) ∗
          ((chainsPtr + 56#64) ↦₆₄ c7) ∗
          ((chainsPtr + 64#64) ↦₆₄ c8) ∗
          ((chainsPtr + 72#64) ↦₆₄ c9) ∗
          ((chainsPtr + 80#64) ↦₆₄ c10) ∗
          ((chainsPtr + 88#64) ↦₆₄ c11) ∗
          ((chainsPtr + 96#64) ↦₆₄ c12) ∗
          ((sp + 0x500#64) ↦₆₄ c1) ∗
          ((sp + 0x508#64) ↦₆₄ c2) ∗
          ((sp + 0x510#64) ↦₆₄ c3) ∗
          ((sp + 0x518#64) ↦₆₄ c4) ∗
          ((sp + 0x520#64) ↦₆₄ c5) ∗
          ((sp + 0x528#64) ↦₆₄ c6) ∗
          ((sp + 0x530#64) ↦₆₄ c7) ∗
          ((sp + 0x538#64) ↦₆₄ c8) ∗
          ((sp + 0x540#64) ↦₆₄ c9) ∗
          ((sp + 0x548#64) ↦₆₄ c10) ∗
          ((sp + 0x550#64) ↦₆₄ c11) ∗
          ((sp + 0x558#64) ↦₆₄ c12))) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  td_fetches_cli b (Rust.withPanics ext) hfn 0xb04 72
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg, by wp_reg, Entails.refl _⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.commit_step4b_post_memmove_wp_ext
    (b : BitVec 64) (ext : String → Option (State → State))
    (sp curLen : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 : BitVec 64)
    (s190 s198 s1a0 s1a8 s1b0 s1b8 s1c0 s1c8 s1d0 s1d8 s1e0 s1e8 s1f0 : BitVec 64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xb4c#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx23 : s.readReg64 .x23 = sp + 0x500#64)
    (hx24 : s.readReg64 .x24 = sp + 0x190#64)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx26 : s.readReg64 .x26 = c0)
    (hx27 : s.readReg64 .x27 = 0xffffffffffffff98#64)
    (hx28 : s.readReg64 .x28 = curLen)
    (hc0_ne : c0 + 1#64 ≠ 0#64) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
      bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64)) s
      (((sp + 0x48#64) ↦₆₄ curLen) ∗
       ((sp + 0x190#64) ↦₆₄ s190) ∗
       ((sp + 0x198#64) ↦₆₄ s198) ∗
       ((sp + 0x1a0#64) ↦₆₄ s1a0) ∗
       ((sp + 0x1a8#64) ↦₆₄ s1a8) ∗
       ((sp + 0x1b0#64) ↦₆₄ s1b0) ∗
       ((sp + 0x1b8#64) ↦₆₄ s1b8) ∗
       ((sp + 0x1c0#64) ↦₆₄ s1c0) ∗
       ((sp + 0x1c8#64) ↦₆₄ s1c8) ∗
       ((sp + 0x1d0#64) ↦₆₄ s1d0) ∗
       ((sp + 0x1d8#64) ↦₆₄ s1d8) ∗
       ((sp + 0x1e0#64) ↦₆₄ s1e0) ∗
       ((sp + 0x1e8#64) ↦₆₄ s1e8) ∗
       ((sp + 0x1f0#64) ↦₆₄ s1f0) ∗
       ((sp + 0x500#64) ↦₆₄ c1) ∗
       ((sp + 0x508#64) ↦₆₄ c2) ∗
       ((sp + 0x510#64) ↦₆₄ c3) ∗
       ((sp + 0x518#64) ↦₆₄ c4) ∗
       ((sp + 0x520#64) ↦₆₄ c5) ∗
       ((sp + 0x528#64) ↦₆₄ c6) ∗
       ((sp + 0x530#64) ↦₆₄ c7) ∗
       ((sp + 0x538#64) ↦₆₄ c8) ∗
       ((sp + 0x540#64) ↦₆₄ c9) ∗
       ((sp + 0x548#64) ↦₆₄ c10) ∗
       ((sp + 0x550#64) ↦₆₄ c11) ∗
       ((sp + 0x558#64) ↦₆₄ c12))
      (fun sf P_f =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x0 = sp + 0x190#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = sp + 0x500#64 ∧
        sf.readReg64 .x24 = sp + 0x190#64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x26 = c0 ∧
        sf.readReg64 .x27 = 0xffffffffffffff98#64 ∧
        sf.readReg64 .x28 = curLen ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xb8c#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          ((sp + 0x48#64) ↦₆₄ (curLen - 1#64)) ∗
          ((sp + 0x190#64) ↦₆₄ c0) ∗
          ((sp + 0x198#64) ↦₆₄ c1) ∗
          ((sp + 0x1a0#64) ↦₆₄ c2) ∗
          ((sp + 0x1a8#64) ↦₆₄ c3) ∗
          ((sp + 0x1b0#64) ↦₆₄ c4) ∗
          ((sp + 0x1b8#64) ↦₆₄ c5) ∗
          ((sp + 0x1c0#64) ↦₆₄ c6) ∗
          ((sp + 0x1c8#64) ↦₆₄ c7) ∗
          ((sp + 0x1d0#64) ↦₆₄ c8) ∗
          ((sp + 0x1d8#64) ↦₆₄ c9) ∗
          ((sp + 0x1e0#64) ↦₆₄ c10) ∗
          ((sp + 0x1e8#64) ↦₆₄ c11) ∗
          ((sp + 0x1f0#64) ↦₆₄ c12) ∗
          ((sp + 0x500#64) ↦₆₄ c1) ∗
          ((sp + 0x508#64) ↦₆₄ c2) ∗
          ((sp + 0x510#64) ↦₆₄ c3) ∗
          ((sp + 0x518#64) ↦₆₄ c4) ∗
          ((sp + 0x520#64) ↦₆₄ c5) ∗
          ((sp + 0x528#64) ↦₆₄ c6) ∗
          ((sp + 0x530#64) ↦₆₄ c7) ∗
          ((sp + 0x538#64) ↦₆₄ c8) ∗
          ((sp + 0x540#64) ↦₆₄ c9) ∗
          ((sp + 0x548#64) ↦₆₄ c10) ∗
          ((sp + 0x550#64) ↦₆₄ c11) ∗
          ((sp + 0x558#64) ↦₆₄ c12))) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  have hbeq : (c0 + 1#64 == 0#64) = false := beq_false_of_ne hc0_ne
  td_fetches_cli b (Rust.withPanics ext) hfn 0xb4c 64
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, Entails.refl _⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.commit_step4c_hi_wp_ext
    (b : BitVec 64) (ext : String → Option (State → State))
    (sp nextLen : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xb8c#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hhi : BitVec.ult 5#64 nextLen = true) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xb04#64) s
      ((sp + 0x48#64) ↦₆₄ nextLen)
      (fun sf P_f =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = nextLen ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ ((sp + 0x48#64) ↦₆₄ nextLen))) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  td_fetches_cli b (Rust.withPanics ext) hfn 0xb8c 12
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, Entails.refl _⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.commit_step4c_le_wp_ext
    (b : BitVec 64) (ext : String → Option (State → State))
    (sp nextLen : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xb8c#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hle : BitVec.ult 5#64 nextLen = false) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xb98#64) s
      ((sp + 0x48#64) ↦₆₄ nextLen)
      (fun sf P_f =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = nextLen ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ ((sp + 0x48#64) ↦₆₄ nextLen))) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  td_fetches_cli b (Rust.withPanics ext) hfn 0xb8c 12
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg, by wp_reg, Entails.refl _⟩

/-!
## 2. Sub-Segment 5: `+0xb98 .. +0xbfc → +0x3e4` (Commit `sender_chain` & Stage `S4State`)
-/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.commit_step5_wp_ext
    (b : BitVec 64) (ext : String → Option (State → State))
    (sp : BitVec 64)
    (sck16 rck16 msgW oldTag oldSck16 v2d0 : BitVec 32)
    (oldSpk0 oldSpk1 oldSpk2 oldSpk3 oldSk0 oldSk1 oldSk2 oldSk3
     oldSck0 oldSck1 oldSck2 oldSck3
     spk0 spk1 spk2 spk3 sk0 sk1 sk2 sk3
     sck0 sck1 sck2 sck3
     rck0 rck1 rck2 rck3
     v2b0 v2b8 v2c0 v2c8
     v450 v458 v460 v468 v470 v478 v480 v488 v490 v498 : BitVec 64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xb98#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0x3e4#64) s
      (((sp + 0x8#64) ↦₃₂ sck16) ∗
       ((sp + 0x10#64) ↦₃₂ rck16) ∗
       ((sp + 0x1c#64) ↦₃₂ msgW) ∗
       ((sp + 0x50#64) ↦₃₂ oldTag) ∗
       ((sp + 0x54#64) ↦₆₄ oldSpk0) ∗
       ((sp + 0x5c#64) ↦₆₄ oldSpk1) ∗
       ((sp + 0x64#64) ↦₆₄ oldSpk2) ∗
       ((sp + 0x6c#64) ↦₆₄ oldSpk3) ∗
       ((sp + 0x74#64) ↦₆₄ oldSk0) ∗
       ((sp + 0x7c#64) ↦₆₄ oldSk1) ∗
       ((sp + 0x84#64) ↦₆₄ oldSk2) ∗
       ((sp + 0x8c#64) ↦₆₄ oldSk3) ∗
       ((sp + 0x94#64) ↦₆₄ oldSck0) ∗
       ((sp + 0x9c#64) ↦₆₄ oldSck1) ∗
       ((sp + 0xa4#64) ↦₃₂ oldSck16) ∗
       ((sp + 0xa8#64) ↦₆₄ oldSck2) ∗
       ((sp + 0xb0#64) ↦₆₄ oldSck3) ∗
       ((sp + 0x2b0#64) ↦₆₄ v2b0) ∗
       ((sp + 0x2b8#64) ↦₆₄ v2b8) ∗
       ((sp + 0x2c0#64) ↦₆₄ v2c0) ∗
       ((sp + 0x2c8#64) ↦₆₄ v2c8) ∗
       ((sp + 0x2d0#64) ↦₃₂ v2d0) ∗
       ((sp + 0x400#64) ↦₆₄ spk0) ∗
       ((sp + 0x408#64) ↦₆₄ spk1) ∗
       ((sp + 0x410#64) ↦₆₄ spk2) ∗
       ((sp + 0x418#64) ↦₆₄ spk3) ∗
       ((sp + 0x420#64) ↦₆₄ sk0) ∗
       ((sp + 0x428#64) ↦₆₄ sk1) ∗
       ((sp + 0x430#64) ↦₆₄ sk2) ∗
       ((sp + 0x438#64) ↦₆₄ sk3) ∗
       ((sp + 0x450#64) ↦₆₄ v450) ∗
       ((sp + 0x458#64) ↦₆₄ v458) ∗
       ((sp + 0x460#64) ↦₆₄ v460) ∗
       ((sp + 0x468#64) ↦₆₄ v468) ∗
       ((sp + 0x470#64) ↦₆₄ v470) ∗
       ((sp + 0x478#64) ↦₆₄ v478) ∗
       ((sp + 0x480#64) ↦₆₄ v480) ∗
       ((sp + 0x488#64) ↦₆₄ v488) ∗
       ((sp + 0x490#64) ↦₆₄ v490) ∗
       ((sp + 0x498#64) ↦₆₄ v498) ∗
       ((sp + 0x4c0#64) ↦₆₄ rck2) ∗
       ((sp + 0x4c8#64) ↦₆₄ rck3) ∗
       ((sp + 0x4d0#64) ↦₆₄ rck0) ∗
       ((sp + 0x4d8#64) ↦₆₄ rck1) ∗
       ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
       ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
       ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
       ((sp + 0x4f8#64) ↦₆₄ sck1))
      (fun sf P_f =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x12 = sp + 0x2c0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = msgW.zeroExtend 64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = s.readReg64 .x30 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          ((sp + 0x8#64) ↦₃₂ sck16) ∗
          ((sp + 0x10#64) ↦₃₂ rck16) ∗
          ((sp + 0x1c#64) ↦₃₂ msgW) ∗
          ((sp + 0x50#64) ↦₃₂ 1#32) ∗
          ((sp + 0x54#64) ↦₆₄ spk0) ∗
          ((sp + 0x5c#64) ↦₆₄ spk1) ∗
          ((sp + 0x64#64) ↦₆₄ spk2) ∗
          ((sp + 0x6c#64) ↦₆₄ spk3) ∗
          ((sp + 0x74#64) ↦₆₄ sk0) ∗
          ((sp + 0x7c#64) ↦₆₄ sk1) ∗
          ((sp + 0x84#64) ↦₆₄ sk2) ∗
          ((sp + 0x8c#64) ↦₆₄ sk3) ∗
          ((sp + 0x94#64) ↦₆₄ sck0) ∗
          ((sp + 0x9c#64) ↦₆₄ sck1) ∗
          ((sp + 0xa4#64) ↦₃₂ sck16) ∗
          ((sp + 0xa8#64) ↦₆₄ sck2) ∗
          ((sp + 0xb0#64) ↦₆₄ sck3) ∗
          ((sp + 0x2b0#64) ↦₆₄ rck2) ∗
          ((sp + 0x2b8#64) ↦₆₄ rck3) ∗
          ((sp + 0x2c0#64) ↦₆₄ rck0) ∗
          ((sp + 0x2c8#64) ↦₆₄ rck1) ∗
          ((sp + 0x2d0#64) ↦₃₂ rck16) ∗
          ((sp + 0x400#64) ↦₆₄ spk0) ∗
          ((sp + 0x408#64) ↦₆₄ spk1) ∗
          ((sp + 0x410#64) ↦₆₄ spk2) ∗
          ((sp + 0x418#64) ↦₆₄ spk3) ∗
          ((sp + 0x420#64) ↦₆₄ sk0) ∗
          ((sp + 0x428#64) ↦₆₄ sk1) ∗
          ((sp + 0x430#64) ↦₆₄ sk2) ∗
          ((sp + 0x438#64) ↦₆₄ sk3) ∗
          ((sp + 0x450#64) ↦₆₄ spk0) ∗
          ((sp + 0x458#64) ↦₆₄ spk1) ∗
          ((sp + 0x460#64) ↦₆₄ spk2) ∗
          ((sp + 0x468#64) ↦₆₄ spk3) ∗
          ((sp + 0x470#64) ↦₆₄ sk0) ∗
          ((sp + 0x478#64) ↦₆₄ sk1) ∗
          ((sp + 0x480#64) ↦₆₄ sk2) ∗
          ((sp + 0x488#64) ↦₆₄ sk3) ∗
          ((sp + 0x490#64) ↦₆₄ sck0) ∗
          ((sp + 0x498#64) ↦₆₄ sck1) ∗
          ((sp + 0x4c0#64) ↦₆₄ rck2) ∗
          ((sp + 0x4c8#64) ↦₆₄ rck3) ∗
          ((sp + 0x4d0#64) ↦₆₄ rck0) ∗
          ((sp + 0x4d8#64) ↦₆₄ rck1) ∗
          ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
          ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
          ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
          ((sp + 0x4f8#64) ↦₆₄ sck1))) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  td_fetches_cli b (Rust.withPanics ext) hfn 0xb98 104
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, Entails.refl _⟩

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegDhHWp2
