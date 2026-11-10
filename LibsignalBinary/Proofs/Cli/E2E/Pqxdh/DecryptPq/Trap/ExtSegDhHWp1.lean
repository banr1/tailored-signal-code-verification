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
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHPack
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHWp
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Ext DH Commit WP Lemmas (Part 1: Sub-Segments 1, 2, 3)

Basic-block `SepWP` lemmas on `tripleRatchetProgAtExt b ext` for
`try_decrypt_with_state::<signal_session_handshake::Coins>` DH commit sub-segments 1–3
(`+0x8ac .. +0xaf0`).
-/

@[expose] public section

set_option autoImplicit false

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH (saturating_sub_one_u32)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH.BS10 (setMem_trace setPC_trace
  setPState_trace spAligned_of_sp_eq writeReg32_trace writeReg64_trace)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegDhHWp1

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "wp_reg" : tactic =>
  `(tactic| simp only [wp_norm,
    writeReg64_trace, writeReg32_trace, setPC_trace,
    setPState_trace, setMem_trace, State.trace_writeVReg128,
    *])

/-! ## 1. Sub-Segment 1: `+0x8ac .. +0x8f8` (`commit_step1_wp_ext`) -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.commit_step1_wp_ext
    (b : BitVec 64) (ext : String → Option (State → State))
    (sp msgA : BitVec 64) (scIdx : BitVec 32)
    (oldRk0 oldRk28 rk0 rk28 sck16 prevCtr0 : BitVec 32)
    (oldRk4 oldRk12 oldRk20 rk4 rk12 rk20 sck0 sck1 sck2 sck3
     v440 v448 v4e0 v4e8 v4f0 v4f8 : BitVec 64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0x8ac#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = msgA)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx27 : s.readReg64 .x27 = sp + 0x38#64)
    (hx28 : s.readReg64 .x28 = sp + 0x3d0#64) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
      bv% ((2^64 + ls_off% "<libsignal_core::curve::PublicKey>::serialize" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64)) s
      (((sp + 0xb4#64) ↦₃₂ scIdx) ∗
       ((sp + 0xb8#64) ↦₃₂ oldRk0) ∗
       ((sp + 0xbc#64) ↦₆₄ oldRk4) ∗
       ((sp + 0xc4#64) ↦₆₄ oldRk12) ∗
       ((sp + 0xcc#64) ↦₆₄ oldRk20) ∗
       ((sp + 0xd4#64) ↦₃₂ oldRk28) ∗
       ((sp + 0xe0#64) ↦₃₂ prevCtr0) ∗
       ((sp + 0x194#64) ↦₃₂ rk0) ∗
       ((sp + 0x198#64) ↦₆₄ rk4) ∗
       ((sp + 0x1a0#64) ↦₆₄ rk12) ∗
       ((sp + 0x1a8#64) ↦₆₄ rk20) ∗
       ((sp + 0x1b0#64) ↦₃₂ rk28) ∗
       ((sp + 0x1b4#64) ↦₆₄ sck0) ∗
       ((sp + 0x1bc#64) ↦₆₄ sck1) ∗
       ((sp + 0x1c4#64) ↦₃₂ sck16) ∗
       ((sp + 0x1c8#64) ↦₆₄ sck2) ∗
       ((sp + 0x1d0#64) ↦₆₄ sck3) ∗
       ((sp + 0x440#64) ↦₆₄ v440) ∗
       ((sp + 0x448#64) ↦₆₄ v448) ∗
       ((sp + 0x4e0#64) ↦₆₄ v4e0) ∗
       ((sp + 0x4e8#64) ↦₆₄ v4e8) ∗
       ((sp + 0x4f0#64) ↦₆₄ v4f0) ∗
       ((sp + 0x4f8#64) ↦₆₄ v4f8))
      (fun sf P_f =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x0 = msgA + 0x38#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = msgA ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = sck16.zeroExtend 64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x27 = sp + 0x38#64 ∧
        sf.readReg64 .x28 = sp + 0x3d0#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0x8fc#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          ((sp + 0xb4#64) ↦₃₂ scIdx) ∗
          ((sp + 0xb8#64) ↦₃₂ rk0) ∗
          ((sp + 0xbc#64) ↦₆₄ rk4) ∗
          ((sp + 0xc4#64) ↦₆₄ rk12) ∗
          ((sp + 0xcc#64) ↦₆₄ rk20) ∗
          ((sp + 0xd4#64) ↦₃₂ rk28) ∗
          ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (scIdx.toNat - 1)) ∗
          ((sp + 0x194#64) ↦₃₂ rk0) ∗
          ((sp + 0x198#64) ↦₆₄ rk4) ∗
          ((sp + 0x1a0#64) ↦₆₄ rk12) ∗
          ((sp + 0x1a8#64) ↦₆₄ rk20) ∗
          ((sp + 0x1b0#64) ↦₃₂ rk28) ∗
          ((sp + 0x1b4#64) ↦₆₄ sck0) ∗
          ((sp + 0x1bc#64) ↦₆₄ sck1) ∗
          ((sp + 0x1c4#64) ↦₃₂ sck16) ∗
          ((sp + 0x1c8#64) ↦₆₄ sck2) ∗
          ((sp + 0x1d0#64) ↦₆₄ sck3) ∗
          ((sp + 0x440#64) ↦₆₄ sck0) ∗
          ((sp + 0x448#64) ↦₆₄ sck1) ∗
          ((sp + 0x4e0#64) ↦₆₄ sck2) ∗
          ((sp + 0x4e8#64) ↦₆₄ sck3) ∗
          ((sp + 0x4f0#64) ↦₆₄ sck0) ∗
          ((sp + 0x4f8#64) ↦₆₄ sck1))) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  td_fetches_cli b (Rust.withPanics ext) hfn 0x8ac 80
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
    by wp_reg, by wp_reg, by wp_reg, by wp_reg, ?_⟩
  rw [← saturating_sub_one_u32 scIdx]
  exact Entails.refl _

/-! ## 2. Sub-Segment 2: `+0x8fc → +0x9dc → +0x9ec → +0x9fc → +0xa04 → +0xa80` -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.commit_step2_pre_shim_wp_ext
    (b : BitVec 64) (ext : String → Option (State → State))
    (sp boxPtr vSp0 : BitVec 64) (vSp8 sck16 : BitVec 32)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0x8fc#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = boxPtr)
    (hx1 : s.readReg64 .x1 = 33#64)
    (hx24 : s.readReg64 .x24 = sck16.zeroExtend 64) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
      bv% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64)) s
      ((sp ↦₆₄ vSp0) ∗
       ((sp + 8#64) ↦₃₂ vSp8))
      (fun sf P_f =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = sck16.zeroExtend 64 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = boxPtr ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0x9f0#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          (sp ↦₆₄ boxPtr) ∗
          ((sp + 8#64) ↦₃₂ sck16))) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  td_fetches_cli b (Rust.withPanics ext) hfn 0x8fc 8
  td_fetches_cli b (Rust.withPanics ext) hfn 0x9dc 20
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
    by wp_reg, by wp_reg, by wp_reg, by wp_reg, ?_⟩
  exact Entails.refl _

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.commit_step2_pre_alloc_wp_ext
    (b : BitVec 64) (ext : String → Option (State → State))
    (sp : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0x9f0#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx26 : s.readReg64 .x26 = 33#64) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
      bv% ((2^64 + ls_off% "__rustc::__rust_alloc" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64)) s
      emp
      (fun sf P_f =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x0 = 33#64 ∧
        sf.readReg64 .x1 = 1#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = 1#64 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xa00#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ emp)) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  td_fetches_cli b (Rust.withPanics ext) hfn 0x9f0 16
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
    by wp_reg, by wp_reg, by wp_reg, Entails.refl _⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.commit_step2_oom_wp_ext
    (b : BitVec 64) (ext : String → Option (State → State))
    (sp : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xa00#64)
    (hrun : s.status = .Running)
    (_hsp : s.sp = sp)
    (_hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
      bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64)) s
      emp
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢ emp)) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  td_fetches_cli b (Rust.withPanics ext) hfn 0xa00 4
  td_fetches_cli b (Rust.withPanics ext) hfn 0x908 12
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  exact ⟨by wp_reg, Entails.refl _⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.commit_step2_post_alloc_wp_ext
    (b : BitVec 64) (ext : String → Option (State → State))
    (sp srkPtr boxPtr : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xa00#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = srkPtr)
    (hsrk_ne : srkPtr ≠ 0#64)
    (hx26 : s.readReg64 .x26 = 33#64) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
      bv% ((2^64 + ls_off% "memcpy" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64)) s
      (sp ↦₆₄ boxPtr)
      (fun sf P_f =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x0 = srkPtr ∧
        sf.readReg64 .x1 = boxPtr ∧
        sf.readReg64 .x2 = 33#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = boxPtr ∧
        sf.readReg64 .x28 = srkPtr ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xa18#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ (sp ↦₆₄ boxPtr))) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  have hbeq : (srkPtr == 0#64) = false := beq_false_of_ne hsrk_ne
  td_fetches_cli b (Rust.withPanics ext) hfn 0xa00 24
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

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.commit_step2_to_pb_wp_ext
    (b : BitVec 64) (ext : String → Option (State → State))
    (sp : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xa18#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
      bv% ((2^64 + ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64)) s
      emp
      (fun sf P_f =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x0 = sp + 0x3d0#64 ∧
        sf.readReg64 .x8 = sp + 0x190#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xa84#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ emp)) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  td_fetches_cli b (Rust.withPanics ext) hfn 0xa18 4
  td_fetches_cli b (Rust.withPanics ext) hfn 0xa78 12
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
    by wp_reg, by wp_reg, by wp_reg, Entails.refl _⟩

/-! ## 3. Sub-Segment 3: `+0xa84 → +0xa9c → +0xaf0` (Push New Receiver Chain & Free Box) -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.commit_step3a_nogrow_wp_ext
    (b : BitVec 64) (ext : String → Option (State → State))
    (sp chainsCap rcLen : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xa84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hne : rcLen ≠ chainsCap) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xa9c#64) s
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗
       ((sp + 0x48#64) ↦₆₄ rcLen))
      (fun sf P_f =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = rcLen ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          ((sp + 0x38#64) ↦₆₄ chainsCap) ∗
          ((sp + 0x48#64) ↦₆₄ rcLen))) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  have hbeq : (rcLen == chainsCap) = false := beq_false_of_ne hne
  have hne' : (rcLen != chainsCap) = true := by simp [hne]
  td_fetches_cli b (Rust.withPanics ext) hfn 0xa84 16
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
    by wp_reg, by wp_reg, by wp_reg, Entails.refl _⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.commit_step3a_grow_wp_ext
    (b : BitVec 64) (ext : String → Option (State → State))
    (sp rcLen : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xa84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
      bv% ((2^64 + ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64)) s
      (((sp + 0x38#64) ↦₆₄ rcLen) ∗
       ((sp + 0x48#64) ↦₆₄ rcLen))
      (fun sf P_f =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x0 = sp + 0x38#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = rcLen ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xa9c#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          ((sp + 0x38#64) ↦₆₄ rcLen) ∗
          ((sp + 0x48#64) ↦₆₄ rcLen))) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  td_fetches_cli b (Rust.withPanics ext) hfn 0xa84 24
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

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.commit_step3b_wp_ext
    (b : BitVec 64) (ext : String → Option (State → State))
    (sp chainsPtr1 rcLen boxPtr srkPtr : BitVec 64)
    (ck0 ck1 ck2 ck3 : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xa9c#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = rcLen)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx26 : s.readReg64 .x26 = 33#64)
    (hx27 : s.readReg64 .x27 = boxPtr)
    (hx28 : s.readReg64 .x28 = srkPtr) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
      bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64)) s
      (((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
       ((sp + 0x48#64) ↦₆₄ rcLen) ∗
       ((sp + 0x190#64) ↦₆₄ ck0) ∗
       ((sp + 0x198#64) ↦₆₄ ck1) ∗
       ((sp + 0x1a0#64) ↦₆₄ ck2) ∗
       ((sp + 0x1a8#64) ↦₆₄ ck3) ∗
       ((chainsPtr1 + rcLen * 104#64) ↦₆₄ w0) ∗
       ((chainsPtr1 + rcLen * 104#64 + 8#64) ↦₆₄ w1) ∗
       ((chainsPtr1 + rcLen * 104#64 + 16#64) ↦₆₄ w2) ∗
       ((chainsPtr1 + rcLen * 104#64 + 24#64) ↦₆₄ w3) ∗
       ((chainsPtr1 + rcLen * 104#64 + 32#64) ↦₆₄ w4) ∗
       ((chainsPtr1 + rcLen * 104#64 + 40#64) ↦₆₄ w5) ∗
       ((chainsPtr1 + rcLen * 104#64 + 48#64) ↦₆₄ w6) ∗
       ((chainsPtr1 + rcLen * 104#64 + 56#64) ↦₆₄ w7) ∗
       ((chainsPtr1 + rcLen * 104#64 + 64#64) ↦₆₄ w8) ∗
       ((chainsPtr1 + rcLen * 104#64 + 72#64) ↦₆₄ w9) ∗
       ((chainsPtr1 + rcLen * 104#64 + 80#64) ↦₆₄ w10) ∗
       ((chainsPtr1 + rcLen * 104#64 + 88#64) ↦₆₄ w11) ∗
       ((chainsPtr1 + rcLen * 104#64 + 96#64) ↦₆₄ w12))
      (fun sf P_f =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x0 = boxPtr ∧
        sf.readReg64 .x1 = 33#64 ∧
        sf.readReg64 .x2 = 1#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = rcLen ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = boxPtr ∧
        sf.readReg64 .x28 = rcLen + 1#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xaf0#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
          ((sp + 0x48#64) ↦₆₄ (rcLen + 1#64)) ∗
          ((sp + 0x190#64) ↦₆₄ ck0) ∗
          ((sp + 0x198#64) ↦₆₄ ck1) ∗
          ((sp + 0x1a0#64) ↦₆₄ ck2) ∗
          ((sp + 0x1a8#64) ↦₆₄ ck3) ∗
          ((chainsPtr1 + rcLen * 104#64) ↦₆₄ 33#64) ∗
          ((chainsPtr1 + rcLen * 104#64 + 8#64) ↦₆₄ srkPtr) ∗
          ((chainsPtr1 + rcLen * 104#64 + 16#64) ↦₆₄ 33#64) ∗
          ((chainsPtr1 + rcLen * 104#64 + 24#64) ↦₆₄ 0#64) ∗
          ((chainsPtr1 + rcLen * 104#64 + 32#64) ↦₆₄ 1#64) ∗
          ((chainsPtr1 + rcLen * 104#64 + 40#64) ↦₆₄ 0#64) ∗
          ((chainsPtr1 + rcLen * 104#64 + 48#64) ↦₆₄ 0#64) ∗
          ((chainsPtr1 + rcLen * 104#64 + 56#64) ↦₆₄ 8#64) ∗
          ((chainsPtr1 + rcLen * 104#64 + 64#64) ↦₆₄ 0#64) ∗
          ((chainsPtr1 + rcLen * 104#64 + 72#64) ↦₆₄ ck0) ∗
          ((chainsPtr1 + rcLen * 104#64 + 80#64) ↦₆₄ ck1) ∗
          ((chainsPtr1 + rcLen * 104#64 + 88#64) ↦₆₄ ck2) ∗
          ((chainsPtr1 + rcLen * 104#64 + 96#64) ↦₆₄ ck3))) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
  td_fetches_cli b (Rust.withPanics ext) hfn 0xa9c 84
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

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegDhHWp1
