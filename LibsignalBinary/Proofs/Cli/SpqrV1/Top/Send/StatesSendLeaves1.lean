/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# Inlined `States::send` Immediate Arms & Join Invariant for CLI `spqr::send`

Defines the `+3068` join-state invariant and proves the three immediate arms
(`ekSentCt1Received`, `noHeaderReceived`, `ct1Acknowledged`) on the CLI image.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames.LibsignalSession (ShaCompress)

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Auth

open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16

open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.NextChunk

open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.States

open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.CodeLayout

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

open CryptoVerification.CodeLayout in
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_memcpy_ok {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy")) sessionMemcpyRegionSpec :=
  hA.session_memcpy_region_ok_at CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName (num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy"))

/-- Register and state conditions at the post-`States::send` join point `entry + 3068#64`. -/
structure _root_.CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendJoinState {F : ShaCompress} (b sp : BitVec 64)
    (ext : String → Option (State → State)) (s0 sf : State) (msg : Message spqrPolyApi)
    (st1 : States spqrPolyApi (spqrAuthApi F)) : Prop where
  pc : sf.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3068#64
  run : sf.status = .Running
  sp_eq : sf.sp = sp
  trace : sf.trace = s0.trace
  x19 : sf.readReg64 .x19 = s0.readReg64 .x19
  x20 : sf.readReg64 .x20 = chunkedStatesWord0 st1
  x22 : sf.readReg64 .x22 = msg.epoch
  x25 : sf.readReg64 .x25 = sp + 0x550#64
  x26 : sf.readReg64 .x26 = sp + 0x1260#64
  x28 : sf.readReg64 .x28 = s0.readReg64 .x28
  vregs : calleeSavedVRegs sf = calleeSavedVRegs s0

/-! ## 1. Immediate Arms (`.ekSentCt1Received`, `.noHeaderReceived`, `.ct1Acknowledged`) -/

/-- Immediate arm 1: `.ekSentCt1Received s` (`+924 -> +3064 -> +3068`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_arm_ekSentCt1Received {F : ShaCompress}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) {s0 s : State} (sp : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 924#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = 6#64) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx25 : s.readReg64 .x25 = sp + 0x550#64) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedStatesAt A (sp + 0x950#64) (.ekSentCt1Received st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920) ∗ Frame)
    (hnext : ∀ sf : State, CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendJoinState b sp ext s0 sf
        { epoch := st.uc.epoch, payload := .ct1Ack true } (.ekSentCt1Received st) →
      SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3068#64) sf
        ((memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1Ack true) ∗
          spqrSendKeySlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A (sp + 0x590#64) (.ekSentCt1Received st)) ∗ Frame) post) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3068#64) s P post := by
  have hmemcpy := CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_memcpy_ok hA
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 924 28
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3064 4
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry
  examples_hide_fetches; subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x950#64) (.ekSentCt1Received st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by bv_omega]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ekSentCt1Received A sp st; rw [h_ep]; wp_steps; rw [← h_ep]
  refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedStatesTail920At A (.ekSentCt1Received st))
    (sp + 0x590#64) (sp + 0x958#64) (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 0x950#64) ↦₆₄ 6#64) ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := entry + 944#64) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by dsimp only [chunkedStatesWord0]; ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf; wp_steps
  refine finish_sepWP
    (hnext _ ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩)
    (imm_arm_post_entails A sp 6#64 _ _ _ (.ct1Ack true) (.ekSentCt1Received st) Frame
      (by simp only [arm64_norm]; rfl) (by dsimp only [spqrSendPayloadSlotAt]; simp only [arm64_norm]))

/-- Immediate arm 2: `.noHeaderReceived s` (`+1284 -> +3064 -> +3068`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_arm_noHeaderReceived {F : ShaCompress}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) {s0 s : State} (sp : BitVec 64)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 1284#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = 7#64) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx25 : s.readReg64 .x25 = sp + 0x550#64) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedStatesAt A (sp + 0x950#64) (.noHeaderReceived st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920) ∗ Frame)
    (hnext : ∀ sf : State, CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendJoinState b sp ext s0 sf
        { epoch := st.uc.epoch, payload := .none } (.noHeaderReceived st) →
      SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3068#64) sf
        ((memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) .none ∗
          spqrSendKeySlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A (sp + 0x590#64) (.noHeaderReceived st)) ∗ Frame) post) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3068#64) s P post := by
  have hmemcpy := CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_memcpy_ok hA
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 1284 28
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3064 4
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry
  examples_hide_fetches; subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x950#64) (.noHeaderReceived st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by bv_omega]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_noHeaderReceived A sp st; rw [h_ep]; wp_steps; rw [← h_ep]
  refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedStatesTail920At A (.noHeaderReceived st))
    (sp + 0x590#64) (sp + 0x958#64) (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 0x950#64) ↦₆₄ 7#64) ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := entry + 1304#64) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by dsimp only [chunkedStatesWord0]; ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf; wp_steps
  refine finish_sepWP
    (hnext _ ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩)
    (imm_arm_post_entails A sp 7#64 _ _ _ .none (.noHeaderReceived st) Frame
      (by simp only [arm64_norm]; rfl) (by dsimp only [spqrSendPayloadSlotAt]; simp only [arm64_norm]))

/-- Immediate arm 3: `.ct1Acknowledged s` (`+952 -> +1288 -> +3064 -> +3068`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_send_arm_ct1Acknowledged {F : ShaCompress}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) {s0 s : State} (sp : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 952#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = 11#64) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx25 : s.readReg64 .x25 = sp + 0x550#64) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedStatesAt A (sp + 0x950#64) (.ct1Acknowledged st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920) ∗ Frame)
    (hnext : ∀ sf : State, CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendJoinState b sp ext s0 sf
        { epoch := st.uc.epoch, payload := .none } (.ct1Acknowledged st) →
      SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3068#64) sf
        ((memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) .none ∗
          spqrSendKeySlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A (sp + 0x590#64) (.ct1Acknowledged st)) ∗ Frame) post) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3068#64) s P post := by
  have hmemcpy := CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_memcpy_ok hA
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 952 8
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 1288 24
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 3064 4
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry
  examples_hide_fetches; subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x950#64) (.ct1Acknowledged st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by bv_omega]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ct1Acknowledged A sp st; rw [h_ep]; wp_steps; rw [← h_ep]
  refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedStatesTail920At A (.ct1Acknowledged st))
    (sp + 0x590#64) (sp + 0x958#64) (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 0x950#64) ↦₆₄ 11#64) ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := entry + 1304#64) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by dsimp only [chunkedStatesWord0]; ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf; wp_steps
  refine finish_sepWP
    (hnext _ ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩)
    (imm_arm_post_entails A sp 11#64 _ _ _ .none (.ct1Acknowledged st) Frame
      (by simp only [arm64_norm]; rfl) (by dsimp only [spqrSendPayloadSlotAt]; simp only [arm64_norm]))

end CryptoVerification.SpqrV1.Top.Send
