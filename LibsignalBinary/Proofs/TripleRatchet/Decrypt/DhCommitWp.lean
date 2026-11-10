/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitPack
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym130
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# DH Step Commit Sub-Segment: Basic-Block `SepWP` Stepping Lemmas

Instruction-level `SepWP` stepping lemmas (`commit_step1_wp` .. `commit_step5_wp`) and relocatable
`[LibsignalPlacement]` `DhCommitBlockWp` instances for blocks `130` (`159`) and `433` (`549`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace DhCommitFacts

theorem writeReg64_trace (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).trace = s.trace := rfl
theorem writeReg32_trace (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := rfl
theorem setPC_trace (s : State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := rfl
theorem setPState_trace (s : State) (ps : PState) :
    (s.setPState ps).trace = s.trace := rfl
theorem setMem_trace (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := rfl

@[simp, wp_norm] theorem calleeSavedVRegs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    calleeSavedVRegs (s.writeReg64 r v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    calleeSavedVRegs (s.writeReg32 r v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_setPC (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_setPState (s : State) (ps : PState) :
    calleeSavedVRegs (s.setPState ps) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_setMem (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_0 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_1 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 1#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_2 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 2#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_3 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 3#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_4 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 4#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_5 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 5#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_6 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 6#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_7 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 7#5 v) = calleeSavedVRegs s := rfl

end DhCommitFacts

local macro "wp_reg" : tactic =>
  `(tactic| simp only [wp_norm,
    DhCommitFacts.writeReg64_trace, DhCommitFacts.writeReg32_trace, DhCommitFacts.setPC_trace,
    DhCommitFacts.setPState_trace, DhCommitFacts.setMem_trace, State.trace_writeVReg128,
    *])

/-! ## 7. Sub-Segment 1: `+0x8ac .. +0x8f8` (`commit_step1_wp`) -/

theorem commit_step1_wp (b : BitVec 64) (ext : String → Option (State → State))
    (sp msgA : BitVec 64) (scIdx : BitVec 32)
    (oldRk0 oldRk28 rk0 rk28 sck16 prevCtr0 : BitVec 32)
    (oldRk4 oldRk12 oldRk20 rk4 rk12 rk20 sck0 sck1 sck2 sck3
     v440 v448 v4e0 v4e8 v4f0 v4f8 : BitVec 64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0x8ac#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = msgA)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx27 : s.readReg64 .x27 = sp + 0x38#64)
    (hx28 : s.readReg64 .x28 = sp + 0x3d0#64) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + bv% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) s
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
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0x8fc#64 ∧
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
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  td_fetches b (Rust.withPanics ext) hfn 0x8ac 80
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, DhCommitFacts.spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg, by wp_reg, ?_⟩
  rw [← saturating_sub_one_u32 scIdx]
  exact Entails.refl _

/-! ## 8. Sub-Segment 2: `+0x8fc → +0x9dc → +0x9ec → +0x9fc → +0xa04 → +0xa80` -/

/-- `+0x8fc .. +0x900` (`mov x26, x1; tbz x1, #63, +0x9dc`) followed by `+0x9dc .. +0x9ec`
(`mov x27, x0; str w24, [sp, #8]; cbz x26, ...; str x27, [sp]; bl shim`). -/
theorem commit_step2_pre_shim_wp (b : BitVec 64) (ext : String → Option (State → State))
    (sp boxPtr vSp0 : BitVec 64) (vSp8 sck16 : BitVec 32)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0x8fc#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = boxPtr)
    (hx1 : s.readReg64 .x1 = 33#64)
    (hx24 : s.readReg64 .x24 = sck16.zeroExtend 64) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) s
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
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0x9f0#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          (sp ↦₆₄ boxPtr) ∗
          ((sp + 8#64) ↦₃₂ sck16))) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  td_fetches b (Rust.withPanics ext) hfn 0x8fc 8
  td_fetches b (Rust.withPanics ext) hfn 0x9dc 20
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, DhCommitFacts.spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg, by wp_reg, ?_⟩
  exact Entails.refl _

/-- `+0x9f0 .. +0x9fc` (`mov x0, x26; mov w1, #1; mov w27, #1; bl __rust_alloc`). -/
theorem commit_step2_pre_alloc_wp (b : BitVec 64) (ext : String → Option (State → State))
    (sp : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0x9f0#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx26 : s.readReg64 .x26 = 33#64) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) s
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
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xa00#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ emp)) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  td_fetches b (Rust.withPanics ext) hfn 0x9f0 16
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, DhCommitFacts.spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg, Entails.refl _⟩

/-- `+0xa00` (`cbz x0, +0x908`) when `x0 = 0#64`, followed by `+0x908 .. +0x910`
(`mov x0, x27; mov x1, x26; bl handle_error` at `entry + 0x13bd0#64`). -/
theorem commit_step2_oom_wp (b : BitVec 64) (ext : String → Option (State → State))
    (sp : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xa00#64)
    (hrun : s.status = .Running)
    (_hsp : s.sp = sp)
    (_hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) s
      emp
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢ emp)) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  td_fetches b (Rust.withPanics ext) hfn 0xa00 4
  td_fetches b (Rust.withPanics ext) hfn 0x908 12
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  exact ⟨by wp_reg, Entails.refl _⟩

/-- `+0xa00 .. +0xa14` (`cbz x0, +0x908; ldr x27, [sp]; mov x2, x26; mov x28, x0; mov x1, x27; bl memcpy`)
when `x0 = srkPtr ≠ 0#64`. -/
theorem commit_step2_post_alloc_wp (b : BitVec 64) (ext : String → Option (State → State))
    (sp srkPtr boxPtr : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xa00#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = srkPtr)
    (hsrk_ne : srkPtr ≠ 0#64)
    (hx26 : s.readReg64 .x26 = 33#64) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + bv% (ls_off% "memcpy" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) s
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
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xa18#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ (sp ↦₆₄ boxPtr))) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  have hbeq : (srkPtr == 0#64) = false := beq_false_of_ne hsrk_ne
  td_fetches b (Rust.withPanics ext) hfn 0xa00 24
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, DhCommitFacts.spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg, by wp_reg, Entails.refl _⟩

/-- `+0xa18` (`b +0xa78`) followed by `+0xa78 .. +0xa80`
(`add x0, sp, #0x3d0; mov x8, x25; bl ChainKey::to_pb`). -/
theorem commit_step2_to_pb_wp (b : BitVec 64) (ext : String → Option (State → State))
    (sp : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xa18#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xfffffffffffd8944#64) s
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
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xa84#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢ emp)) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  td_fetches b (Rust.withPanics ext) hfn 0xa18 4
  td_fetches b (Rust.withPanics ext) hfn 0xa78 12
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, DhCommitFacts.spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg, Entails.refl _⟩

/-! ## 9. Sub-Segment 3: `+0xa84 → +0xa9c → +0xaf0` (Push New Receiver Chain & Free Box) -/

/-- `+0xa84 .. +0xa90` (`ldr x24, [sp, #0x48]; ldr x8, [sp, #0x38]; cmp x24, x8; b.ne +0xa9c`)
when `rcLen ≠ chainsCap`. -/
theorem commit_step3a_nogrow_wp (b : BitVec 64) (ext : String → Option (State → State))
    (sp chainsCap rcLen : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xa84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hne : rcLen ≠ chainsCap) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xa9c#64) s
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
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  have hbeq : (rcLen == chainsCap) = false := beq_false_of_ne hne
  have hne' : (rcLen != chainsCap) = true := by simp [hne]
  td_fetches b (Rust.withPanics ext) hfn 0xa84 16
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, DhCommitFacts.spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg, Entails.refl _⟩

/-- `+0xa84 .. +0xa98` (`ldr x24, [sp, #0x48]; ldr x8, [sp, #0x38]; cmp x24, x8; b.ne +0xa9c; add x0, sp, #0x38; bl grow_one`)
when `rcLen = chainsCap`. -/
theorem commit_step3a_grow_wp (b : BitVec 64) (ext : String → Option (State → State))
    (sp rcLen : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xa84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xfffffffffffe1688#64) s
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
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xa9c#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (P_f ⊢
          ((sp + 0x38#64) ↦₆₄ rcLen) ∗
          ((sp + 0x48#64) ↦₆₄ rcLen))) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  td_fetches b (Rust.withPanics ext) hfn 0xa84 24
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, DhCommitFacts.spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, Entails.refl _⟩

/-- `+0xa9c .. +0xaec`: writes the new `Chain` slot at `chainsPtr1 + rcLen * 104#64`,
increments `[sp + 0x48]` to `rcLen + 1#64`, and calls `bl __rust_dealloc(boxPtr, 33, 1)` at `+0xaec`. -/
theorem commit_step3b_wp (b : BitVec 64) (ext : String → Option (State → State))
    (sp chainsPtr1 rcLen boxPtr srkPtr : BitVec 64)
    (ck0 ck1 ck2 ck3 : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xa9c#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = rcLen)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx26 : s.readReg64 .x26 = 33#64)
    (hx27 : s.readReg64 .x27 = boxPtr)
    (hx28 : s.readReg64 .x28 = srkPtr) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) s
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
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xaf0#64 ∧
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
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  td_fetches b (Rust.withPanics ext) hfn 0xa9c 84
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, DhCommitFacts.spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg, by wp_reg, Entails.refl _⟩

/-! ## 10. Sub-Segment 4: `+0xaf0 → +0xb04 .. +0xb94 → +0xb98` (Eviction Loop) -/

/-- `+0xaf0 .. +0xaf8` (`ldr x28, [sp, #0x48]; cmp x28, #6; b.lo +0xb98`) when `newLen < 6`. -/
theorem commit_step4a_lo_wp (b : BitVec 64) (ext : String → Option (State → State))
    (sp newLen : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xaf0#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hlo : BitVec.ult newLen 6#64 = true) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xb98#64) s
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
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  td_fetches b (Rust.withPanics ext) hfn 0xaf0 12
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, DhCommitFacts.spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg, by wp_reg, Entails.refl _⟩

/-- `+0xaf0 .. +0xb00` (`ldr x28, [sp, #0x48]; cmp x28, #6; b.lo +0xb98; mov x24, x25; mov x27, #-104`)
when `newLen ≥ 6`. -/
theorem commit_step4a_ge_wp (b : BitVec 64) (ext : String → Option (State → State))
    (sp newLen : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xaf0#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hge : BitVec.ult newLen 6#64 = false) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xb04#64) s
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
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  td_fetches b (Rust.withPanics ext) hfn 0xaf0 20
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, DhCommitFacts.spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, Entails.refl _⟩

/-- `+0xb04 .. +0xb48`: first half of the eviction loop body (`Vec::remove(0)` up to `bl memmove`). -/
theorem commit_step4b_pre_memmove_wp (b : BitVec 64) (ext : String → Option (State → State))
    (sp chainsPtr curLen : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 : BitVec 64)
    (s500 s508 s510 s518 s520 s528 s530 s538 s540 s548 s550 s558 : BitVec 64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xb04#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx23 : s.readReg64 .x23 = sp + 0x500#64)
    (hx24 : s.readReg64 .x24 = sp + 0x190#64)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx27 : s.readReg64 .x27 = 0xffffffffffffff98#64)
    (hx28 : s.readReg64 .x28 = curLen) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + bv% (ls_off% "memmove" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) s
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
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xb4c#64 ∧
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
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  td_fetches b (Rust.withPanics ext) hfn 0xb04 72
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, DhCommitFacts.spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg, by wp_reg, Entails.refl _⟩

/-- `+0xb4c .. +0xb88`: second half of the eviction loop body (after `bl memmove` returns to `+0xb4c`,
writes `curLen - 1#64` to `[sp + 0x48]`, reassembles `gc₀` at `sp + 0x190..0x1f8`, and calls
`bl drop_glue<Chain>` at `+0xb88`). -/
theorem commit_step4b_post_memmove_wp (b : BitVec 64) (ext : String → Option (State → State))
    (sp curLen : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 : BitVec 64)
    (s190 s198 s1a0 s1a8 s1b0 s1b8 s1c0 s1c8 s1d0 s1d8 s1e0 s1e8 s1f0 : BitVec 64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xb4c#64)
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
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) s
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
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xb8c#64 ∧
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
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  have hbeq : (c0 + 1#64 == 0#64) = false := beq_false_of_ne hc0_ne
  td_fetches b (Rust.withPanics ext) hfn 0xb4c 64
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, DhCommitFacts.spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, Entails.refl _⟩

/-- `+0xb8c .. +0xb94` (`ldr x28, [sp, #0x48]; cmp x28, #5; b.hi +0xb04`) when `5 < nextLen`. -/
theorem commit_step4c_hi_wp (b : BitVec 64) (ext : String → Option (State → State))
    (sp nextLen : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xb8c#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hhi : BitVec.ult 5#64 nextLen = true) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xb04#64) s
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
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  td_fetches b (Rust.withPanics ext) hfn 0xb8c 12
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, DhCommitFacts.spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, Entails.refl _⟩

/-- `+0xb8c .. +0xb94` (`ldr x28, [sp, #0x48]; cmp x28, #5; b.hi +0xb04`) when `nextLen ≤ 5`. -/
theorem commit_step4c_le_wp (b : BitVec 64) (ext : String → Option (State → State))
    (sp nextLen : BitVec 64) (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xb8c#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hle : BitVec.ult 5#64 nextLen = false) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xb98#64) s
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
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  td_fetches b (Rust.withPanics ext) hfn 0xb8c 12
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, DhCommitFacts.spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg, by wp_reg, Entails.refl _⟩

/-! ## 11. Sub-Segment 5: `+0xb98 .. +0xbfc → +0x3e4` (Commit `sender_chain` & Stage `ConsumeMsgKeyState`) -/

/-- `+0xb98 .. +0xbfc`: commits `sender_chain = some ⟨newSenderKey, senderChainKey⟩` into
`sp + 0x50..0xb8`, stages `receiverChainKey` across `sp + 0x2b0..0x2d4` with `x12 = sp + 0x2c0`,
loads `w24` from `[sp + 0x1c]`, and branches (`b 0x34780`) to `+0x3e4` (`segConsumeMsgKeyPC`). -/
theorem commit_step5_wp (b : BitVec 64) (ext : String → Option (State → State))
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
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0xb98#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0x3e4#64) s
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
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  td_fetches b (Rust.withPanics ext) hfn 0xb98 104
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr tryDecryptName = entry0
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rfl) (by wp_reg) ?_
  refine ⟨by wp_reg, DhCommitFacts.spAligned_of_sp_eq (by wp_reg) hsp_align, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, by wp_reg,
    by wp_reg, by wp_reg, Entails.refl _⟩

/-! ## 12. Relocatable `[LibsignalPlacement]` `DhCommitBlockWp` Instances (`159` and `549`) -/

local macro "wp_done_reg" hsp_al:ident : tactic =>
  `(tactic| (
    wp_steps
    refine SepWP.done (by rfl) (by wp_reg) ?_
    refine And.intro (by wp_reg) (And.intro (DhCommitFacts.spAligned_of_sp_eq (by wp_reg) $hsp_al) ?_)
    repeat' (refine And.intro ?_ ?_ <;> [wp_reg; skip])
    try rw [← saturating_sub_one_u32 _]
    exact Entails.refl _))

set_option maxHeartbeats 1600000 in
theorem dhCommitBlockWp_159 [LibsignalPlacement] (H : String → Option (State → State)) :
    DhCommitBlockWp ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base (lsmpl.base 142) where
  step1 := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx22 hx25 hx27 hx28; wp_done_reg hsp_align
  step2_pre_shim := by intro _ _ _ _ _ s hpc hrun hsp hsp_align hx0 hx1 hx24; wp_done_reg hsp_align
  step2_pre_alloc := by intro _ s hpc hrun hsp hsp_align hx26; wp_done_reg hsp_align
  step2_oom := by intro _ s hpc hrun _hsp _hsp_align hx0; wp_steps; exact SepWP.done (by rfl) (by wp_reg) ⟨by wp_reg, Entails.refl _⟩
  step2_post_alloc := by
    intro _ srkPtr _ s hpc hrun hsp hsp_align hx0 hsrk_ne hx26
    have hbeq : (srkPtr == 0#64) = false := beq_false_of_ne hsrk_ne; wp_done_reg hsp_align
  step2_to_pb := by intro _ s hpc hrun hsp hsp_align hx25; wp_done_reg hsp_align
  step3a_nogrow := by
    intro _ chainsCap rcLen s hpc hrun hsp hsp_align hne
    have hbeq : (rcLen == chainsCap) = false := beq_false_of_ne hne
    have hne' : (rcLen != chainsCap) = true := by simp [hne]
    wp_done_reg hsp_align
  step3a_grow := by intro _ _ s hpc hrun hsp hsp_align; wp_done_reg hsp_align
  step3b := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx24 hx25 hx26 hx27 hx28; wp_done_reg hsp_align
  step4a_lo := by intro _ _ s hpc hrun hsp hsp_align hlo; wp_done_reg hsp_align
  step4a_ge := by intro _ _ s hpc hrun hsp hsp_align hx25 hge; wp_done_reg hsp_align
  step4b_pre_memmove := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx23 hx24 hx25 hx27 hx28; wp_done_reg hsp_align
  step4b_post_memmove := by
    intro _ _ c0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx23 hx24 hx25 hx26 hx27 hx28 hc0_ne
    have hbeq : (c0 + 1#64 == 0#64) = false := beq_false_of_ne hc0_ne; wp_done_reg hsp_align
  step4c_hi := by intro _ _ s hpc hrun hsp hsp_align hhi; wp_done_reg hsp_align
  step4c_le := by intro _ _ s hpc hrun hsp hsp_align hle; wp_done_reg hsp_align
  step5 := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx25; wp_done_reg hsp_align

set_option maxHeartbeats 1600000 in
theorem dhCommitBlockWp_549 [LibsignalPlacement] (H : String → Option (State → State)) :
    DhCommitBlockWp ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base (lsmpl.base 445) where
  step1 := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx22 hx25 hx27 hx28; wp_done_reg hsp_align
  step2_pre_shim := by intro _ _ _ _ _ s hpc hrun hsp hsp_align hx0 hx1 hx24; wp_done_reg hsp_align
  step2_pre_alloc := by intro _ s hpc hrun hsp hsp_align hx26; wp_done_reg hsp_align
  step2_oom := by intro _ s hpc hrun _hsp _hsp_align hx0; wp_steps; exact SepWP.done (by rfl) (by wp_reg) ⟨by wp_reg, Entails.refl _⟩
  step2_post_alloc := by
    intro _ srkPtr _ s hpc hrun hsp hsp_align hx0 hsrk_ne hx26
    have hbeq : (srkPtr == 0#64) = false := beq_false_of_ne hsrk_ne; wp_done_reg hsp_align
  step2_to_pb := by intro _ s hpc hrun hsp hsp_align hx25; wp_done_reg hsp_align
  step3a_nogrow := by
    intro _ chainsCap rcLen s hpc hrun hsp hsp_align hne
    have hbeq : (rcLen == chainsCap) = false := beq_false_of_ne hne
    have hne' : (rcLen != chainsCap) = true := by simp [hne]
    wp_done_reg hsp_align
  step3a_grow := by intro _ _ s hpc hrun hsp hsp_align; wp_done_reg hsp_align
  step3b := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx24 hx25 hx26 hx27 hx28; wp_done_reg hsp_align
  step4a_lo := by intro _ _ s hpc hrun hsp hsp_align hlo; wp_done_reg hsp_align
  step4a_ge := by intro _ _ s hpc hrun hsp hsp_align hx25 hge; wp_done_reg hsp_align
  step4b_pre_memmove := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx23 hx24 hx25 hx27 hx28; wp_done_reg hsp_align
  step4b_post_memmove := by
    intro _ _ c0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx23 hx24 hx25 hx26 hx27 hx28 hc0_ne
    have hbeq : (c0 + 1#64 == 0#64) = false := beq_false_of_ne hc0_ne; wp_done_reg hsp_align
  step4c_hi := by intro _ _ s hpc hrun hsp hsp_align hhi; wp_done_reg hsp_align
  step4c_le := by intro _ _ s hpc hrun hsp hsp_align hle; wp_done_reg hsp_align
  step5 := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx25; wp_done_reg hsp_align

end CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit
