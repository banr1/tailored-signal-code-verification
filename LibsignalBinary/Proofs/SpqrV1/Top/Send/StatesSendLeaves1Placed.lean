/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlaced
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1StepsPlaced

/-!
# Relocatable Inlined `States::send` Immediate Arms and Leaf-Call Combinators (Block 124)

Defines `SpqrSendJoinStatePlaced` at `spqrSendPlacedEntry + 3068#64`, verifies the three
immediate arms under `[LibsignalPlacement]`, and provides `LibsignalCodeRoLoaded` leaf-call
combinators.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Send.Placed

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

/-- Relocatable register and state conditions at the post-`States::send` join point
    `spqrSendPlacedEntry + 3068#64`. -/
structure SpqrSendJoinStatePlaced {F : ShaCompress} (sp : BitVec 64)
    (ext : String → Option (State → State)) (s0 sf : State) (msg : Message spqrPolyApi)
    (st1 : States spqrPolyApi (spqrAuthApi F)) : Prop where
  pc : sf.pc = spqrSendPlacedEntry + 3068#64
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

/-! ## Immediate Arms (`.ekSentCt1Received`, `.noHeaderReceived`, `.ct1Acknowledged`) -/

/-- Relocatable immediate arm 1: `.ekSentCt1Received s` (`+924 -> +3064 -> +3068`). -/
theorem step_send_arm_ekSentCt1Received_placed {F : ShaCompress}
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext) {s0 s : State} (sp : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 924#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = 6#64) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx25 : s.readReg64 .x25 = sp + 0x550#64) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedStatesAt A (sp + 0x950#64) (.ekSentCt1Received st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920) ∗ Frame)
    (hnext : ∀ sf : State, SpqrSendJoinStatePlaced sp ext s0 sf
        { epoch := st.uc.epoch, payload := .ct1Ack true } (.ekSentCt1Received st) →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) sf
        ((memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1Ack true) ∗
          spqrSendKeySlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A (sp + 0x590#64) (.ekSentCt1Received st)) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) s P post := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x950#64) (.ekSentCt1Received st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by bv_omega]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ekSentCt1Received A sp st; rw [h_ep]; wp_steps; rw [← h_ep]
  refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedStatesTail920At A (.ekSentCt1Received st))
    (sp + 0x590#64) (sp + 0x958#64) (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 0x950#64) ↦₆₄ 6#64) ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_124).base + 944#64) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by dsimp only [chunkedStatesWord0]; ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf; wp_steps
  refine finish_sepWP
    (hnext _ ⟨by simp only [spqrSendPlacedEntry, arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩)
    (imm_arm_post_entails A sp 6#64 _ _ _ (.ct1Ack true) (.ekSentCt1Received st) Frame
      (by simp only [arm64_norm]; rfl) (by dsimp only [spqrSendPayloadSlotAt]; simp only [arm64_norm]))

/-- Relocatable immediate arm 2: `.noHeaderReceived s` (`+1284 -> +3064 -> +3068`). -/
theorem step_send_arm_noHeaderReceived_placed {F : ShaCompress}
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext) {s0 s : State} (sp : BitVec 64)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 1284#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = 7#64) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx25 : s.readReg64 .x25 = sp + 0x550#64) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedStatesAt A (sp + 0x950#64) (.noHeaderReceived st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920) ∗ Frame)
    (hnext : ∀ sf : State, SpqrSendJoinStatePlaced sp ext s0 sf
        { epoch := st.uc.epoch, payload := .none } (.noHeaderReceived st) →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) sf
        ((memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) .none ∗
          spqrSendKeySlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A (sp + 0x590#64) (.noHeaderReceived st)) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) s P post := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x950#64) (.noHeaderReceived st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by bv_omega]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_noHeaderReceived A sp st; rw [h_ep]; wp_steps; rw [← h_ep]
  refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedStatesTail920At A (.noHeaderReceived st))
    (sp + 0x590#64) (sp + 0x958#64) (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 0x950#64) ↦₆₄ 7#64) ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_124).base + 1304#64) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by dsimp only [chunkedStatesWord0]; ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf; wp_steps
  refine finish_sepWP
    (hnext _ ⟨by simp only [spqrSendPlacedEntry, arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩)
    (imm_arm_post_entails A sp 7#64 _ _ _ .none (.noHeaderReceived st) Frame
      (by simp only [arm64_norm]; rfl) (by dsimp only [spqrSendPayloadSlotAt]; simp only [arm64_norm]))

/-- Relocatable immediate arm 3: `.ct1Acknowledged s` (`+952 -> +1288 -> +3064 -> +3068`). -/
theorem step_send_arm_ct1Acknowledged_placed {F : ShaCompress}
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext) {s0 s : State} (sp : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 952#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = 11#64) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx25 : s.readReg64 .x25 = sp + 0x550#64) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedStatesAt A (sp + 0x950#64) (.ct1Acknowledged st) ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920) ∗ Frame)
    (hnext : ∀ sf : State, SpqrSendJoinStatePlaced sp ext s0 sf
        { epoch := st.uc.epoch, payload := .none } (.ct1Acknowledged st) →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) sf
        ((memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) .none ∗
          spqrSendKeySlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A (sp + 0x590#64) (.ct1Acknowledged st)) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 3068#64) s P post := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x950#64) (.ct1Acknowledged st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by bv_omega]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ct1Acknowledged A sp st; rw [h_ep]; wp_steps; rw [← h_ep]
  refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedStatesTail920At A (.ct1Acknowledged st))
    (sp + 0x590#64) (sp + 0x958#64) (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 0x950#64) ↦₆₄ 11#64) ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_124).base + 1304#64) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by dsimp only [chunkedStatesWord0]; ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf; wp_steps
  refine finish_sepWP
    (hnext _ ⟨by simp only [spqrSendPlacedEntry, arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩)
    (imm_arm_post_entails A sp 11#64 _ _ _ .none (.ct1Acknowledged st) Frame
      (by simp only [arm64_norm]; rfl) (by dsimp only [spqrSendPayloadSlotAt]; simp only [arm64_norm]))

/-! ## Leaf-Call Combinators with `LibsignalCodeRoLoaded` -/

/-- Run a non-panicking `SepWP` segment to `mid`, propagating `LibsignalCodeRoLoaded lsmpl` to the continuation. -/
theorem of_sepWP_lscro {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm => LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  sepWPp_seq_lscro hcrl h

/-- Call a panic-capable subroutine (`withLsCodeRoLoaded lsmpl spec`) that uses `n ≤ spqrSendCalleeStack` bytes of stack. -/
theorem call_lscro_calleeStack {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : State → SepProp} {Q : State → SepProp → Prop} {Fr F : SepProp}
    {φ_pre : Prop} {φ_post : State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap))
    (hspec_post : ∀ sf, spec.post x s sf = (⌜φ_post sf⌝ ∗ T_post sf ∗ stackAt s.sp n))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      φ_post sf → LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp prog ret sf ((stackAt sp spqrSendCalleeStack ∗ T_post sf) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  have hcall' : subroutine_ok prog entry
      { withLsCodeRoLoaded lsmpl spec with
        post := fun x' s0' sf => ⌜LibsignalCodeRoLoaded lsmpl sf.mem⌝ ∗ spec.post x' s0' sf } := by
    refine Arm64.subroutine_ok.of_codeLoaded fun x' R s0' hpc0 hrun0 hpre0 hsp0 hL0 => ?_
    have ⟨hcrl0, _⟩ := extract_withLsCodeRoLoaded hpre0
    obtain ⟨sf, hsteps, hout, -⟩ := hcall.no_fault_before_outcome x' R s0' hpc0 hrun0 hpre0 hsp0 hL0
    refine Arm64.reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
    rcases hout with ⟨hret, hcc, hpost⟩ | hrest
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hcrl0.of_keepsFrozen hsteps.keepsFrozen, hpost⟩
    · exact Or.inr hrest
  have hsp_al : s.spAligned = true := by unfold State.spAligned; rw [hsp]; exact hsp_align
  refine SepWPp.call_wpp (x := x)
    (F := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F)
    hcall' hpc hrun hsp_al hlr
    (fun R' hm => by
      change s.mem ⊨ (spec.pre x s ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗
        ((memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F) ∗ R')
      rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
      rw [hspec_pre, hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hφ, ?_⟩
      rw [hP, stackAt_spqrSendCallee_split sp n hle] at hm
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)
    (fun sm code R' _ hpost => by
      dsimp only [withLsCodeRoLoaded] at hpost; rw [hexit_eq code sm] at hpost
      exact allowPanic_not_exited hpost)
    (fun sm _ _ hmFr => by
      dsimp only [withLsCodeRoLoaded] at hmFr; rw [hpan_eq sm] at hmFr
      refine allowPanic_frame ?_ hmFr
      rintro ⟨haf, hpr⟩; unfold allocFailedIn at haf ⊢; rw [htr] at haf hpr; exact ⟨haf, hpr⟩)
    (fun sm hpcm hrunm hspm hcsm => ?_)
    (fun sm R' _ hpost => by
      dsimp only [withLsCodeRoLoaded] at hpost; rw [hoom_eq sm] at hpost
      exact (allowPanic_not_exited hpost).elim)
  rw [hsp] at hspm
  rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, _, hvregs⟩
  have hpeq : (⌜LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗ spec.post x s sm) ∗
      (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F) =
      ⌜LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗
        (⌜φ_post sm⌝ ∗ ((stackAt sp spqrSendCalleeStack ∗ T_post sm) ∗ F)) := by
    rw [hspec_post sm, hsp, stackAt_spqrSendCallee_split sp n hle]; ac_rfl
  dsimp only
  exact SepWPp.congr_pre hpeq (SepWPp.pure_left fun hcrl_m => SepWPp.pure_left fun hφ_post =>
    hnext sm hpcm hrunm hspm hφ_post hcrl_m hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs)

theorem finish_sepWP_lscro {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q onPanic : State → SepProp → Prop}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (hnext : LibsignalCodeRoLoaded lsmpl s.mem → SepWPp prog ret s P' Q onPanic) (hent : P ⊢ P') :
    SepWP prog mid s P (fun sm Pm => LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q onPanic) := by
  refine SepWP.fold hent (sepConj_emp _).symm ?_; rw [sepConj_emp]; exact SepWP.done hpc hrun hnext

theorem leaf_arm_post_entails_placed {F : ShaCompress} (A : RustAlloc)
    (sp w0 x21 x27 : BitVec 64) (x24_8 : BitVec 8) (sz : Nat)
    (P F_out : SepProp) (chunk : Chunk)
    (pay : MessagePayload spqrPolyApi) (nextSt : States spqrPolyApi (spqrAuthApi F))
    (Frame : SepProp) (hsz : sz ≤ 920 := by decide) (hx21 : x21 = LibsignalTripleRatchetRepr.noneCap)
    (hpay : chunkAt (sp + 0x550#64) chunk ∗ memRegion (sp + 0x572#64) 4 ⊢ spqrSendPayloadSlotAt sp x24_8 pay)
    (htail : F_out ∗ memRegion ((sp + 0x590#64) + BitVec.ofNat 64 sz) (920 - sz) =
      chunkedStatesTail920At A (sp + 0x590#64) nextSt)
    (hP_eq : P = (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        (((sp + 0x950#64) ↦₆₄ w0) ∗ memRegion (sp + 0x958#64) sz ∗
          memRegion ((sp + 0x958#64) + BitVec.ofNat 64 sz) (920 - sz)) ∗
        (memRegion (sp + 0x1260#64) sz ∗ chunkAt ((sp + 0x1260#64) + BitVec.ofNat 64 sz) chunk) ∗
        (chunkAt (sp + 0x550#64) chunk ∗ memRegion (sp + 0x572#64) 4) ∗ memRegion (sp + 0x580#64) 16 ∗
        (F_out ∗ memRegion ((sp + 0x590#64) + BitVec.ofNat 64 sz) (920 - sz))) ∗ Frame) :
    P ⊢ (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (sz + chunkSize) ∗
        spqrSendPayloadSlotAt sp x24_8 pay ∗ spqrSendKeySlotAt A sp x21 x27 none ∗
        chunkedStatesTail920At A (sp + 0x590#64) nextSt) ∗ Frame := by
  have hkey : memRegion (sp + 0x580#64) 16 ⊢ spqrSendKeySlotAt A sp x21 x27 none := by
    dsimp only [spqrSendKeySlotAt]; exact Entails.pure_right hx21 (Entails.refl _)
  have h1 := word0_sz_pad_entails_memRegion_928 sp w0 sz hsz
  have h2 := scratch_and_chunk_entails_memRegion sp sz chunk (by omega)
  rw [hP_eq, htail]
  exact sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono hpay (sepConj_mono_left hkey))))))))

end CryptoVerification.SpqrV1.Top.Send
