/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1Sampled
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmKeysSampled2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceived2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple3
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (`0x55454..0x5a0a0`): Top-Level Assembly

**Checked by Lean.** Combines all 11 jump-table arms (`13` `States` constructors) with the prologue
and jump-table dispatch to prove `states_recv_ok_x` and `states_recv_ok_x_ext`, plus `.rodata` witnesses.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## Prologue + Dispatch Wrappers for `.headerSent` and `.ct1Received` -/

/-- Per-variant specification proof for `States.headerSent st` (`tag = 4#64`, arm entry `+780`). -/
theorem states_recv_headerSent_ok_ext
    (A : RustAlloc) (F : ShaCompress) (K : MlKem) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hdealloc : DeallocOkExt b A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr headerSentRecvCt1ChunkName)
      (headerSentRecvCt1ChunkSpec A F b))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName)
      (statesRecvVariantSpec A F K b (.headerSent st) msg) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [statesRecvVariantSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hb, hx0, hx1, hx2, hinv⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗ (memRegion outA v1RecvSize ∗
      chunkedStatesAt A selfA (.headerSent st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  have hpro := states_recv_prologue (b := b) (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.headerSent st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool) hsp0_align hpc0 hrun0
  refine sepWPp_seq_clean hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  dsimp only [chunkedStatesAt]
  have hdisp := states_recv_dispatch (b := b) (ext := ext) hb s1 (s0.sp - 4240#64) selfA 4#64
    (chunkedHeaderSentAt A (selfA + 8#64) st ∗ memRegion (selfA + 888#64) 40 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
     statesRecvSavedCells s0)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hpc1 hrun1 hsp1 hx1_1
  dsimp only [statesRecvArmOffset] at hdisp
  refine sepWPp_seq_clean (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx2_2, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  have htr20 : TraceCalleeSaved s2 s0 := htr2.trans htr1
  refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [chunkedStatesAt]; ac_rfl))
    (states_recv_arm_headerSent hb hdealloc hcall hmemcpy s0 s2 outA selfA msgA st msg R
      hinv hpc2 hrun2 hsp2 hsp0_align hx1_2 hx19_2 hx24_2 htr20)

/-- Per-variant specification proof for `States.ct1Received st` (`tag = 5#64`, arm entry `+1204`). -/
theorem states_recv_ct1Received_ok_ext
    (A : RustAlloc) (F : ShaCompress) (K : MlKem) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hdealloc : DeallocOkExt b A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ct1ReceivedRecvCt2ChunkName)
      (ct1ReceivedRecvCt2ChunkSpec A F))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName)
      (statesRecvVariantSpec A F K b (.ct1Received st) msg) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [statesRecvVariantSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hb, hx0, hx1, hx2, _hinv⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗ (memRegion outA v1RecvSize ∗
      chunkedStatesAt A selfA (.ct1Received st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  have hpro := states_recv_prologue (b := b) (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Received st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool) hsp0_align hpc0 hrun0
  refine sepWPp_seq_clean hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  dsimp only [chunkedStatesAt]
  have hdisp := states_recv_dispatch (b := b) (ext := ext) hb s1 (s0.sp - 4240#64) selfA 5#64
    (chunkedCt1ReceivedAt A (selfA + 8#64) st ∗ memRegion (selfA + 512#64) 416 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
     statesRecvSavedCells s0)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) hpc1 hrun1 hsp1 hx1_1
  dsimp only [statesRecvArmOffset] at hdisp
  refine sepWPp_seq_clean (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx2_2, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  have htr20 : TraceCalleeSaved s2 s0 := htr2.trans htr1
  refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [chunkedStatesAt]; ac_rfl))
    (states_recv_arm_ct1Received hb hdealloc hcall hmemcpy s0 s2 outA selfA msgA st msg R
      hpc2 hrun2 hsp2 hsp0_align hx1_2 hx19_2 hx24_2 htr20)

/-! ## Per-Variant and Top-Level Assembly (`StatesRecvOkX`) -/

theorem deallocOkExt_of_allocContracts {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    DeallocOkExt b A ext :=
  hA.dealloc

/-- Per-variant in-image correctness of `<spqr::v1::chunked::states::States>::recv` (`0x55454`)
    across all 11 `States` constructors wired directly from `AllocContracts`
    and `StatesRecvContracts`. -/
theorem states_recv_variant_x
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hC : StatesRecvContracts img A F K ext)
    (self : States spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpec A F K img.base self msg).inImage img) := by
  have hdealloc : DeallocOkExt img.base A ext := deallocOkExt_of_allocContracts hA
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName) sessionMemcpyRegionSpec := by
    have h0 := hA.session_memcpy_region_ok_at memcpyName 0 (Nat.add_zero _)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h0
  cases self with
  | keysUnsampled st =>
    exact subroutine_ok_inImage_of_subroutine_ok img
      (states_recv_keysUnsampled_ok_ext A F K img.base ext hA st msg)
  | keysSampled st =>
    exact subroutine_ok_inImage_of_subroutine_ok img
      (states_recv_keysSampled_ok_ext A F K img.base ext hdealloc
        hC.keysSampledRecvCt1Chunk_ok hmemcpy st msg)
  | headerSent st =>
    exact subroutine_ok_inImage_of_subroutine_ok img
      (states_recv_headerSent_ok_ext A F K img.base ext hdealloc
        hC.headerSentRecvCt1Chunk_ok hmemcpy st msg)
  | ct1Received st =>
    exact subroutine_ok_inImage_of_subroutine_ok img
      (states_recv_ct1Received_ok_ext A F K img.base ext hdealloc
        hC.ct1ReceivedRecvCt2Chunk_ok hmemcpy st msg)
  | ekSentCt1Received st =>
    exact states_recv_ekSentCt1Received_ok_x hdealloc
      hC.ekSentCt1ReceivedRecvCt2Chunk_ok hmemcpy st msg
  | noHeaderReceived st =>
    exact states_recv_noHeaderReceived_ok_x img A F K ext hdealloc hmemcpy
      hC.noHeaderReceivedRecvHdrChunk_ok st msg
  | headerReceived st =>
    exact subroutine_ok_inImage_of_subroutine_ok img
      (states_recv_headerReceived_ok_ext A F K img.base ext hA st msg)
  | ct1Sampled st =>
    exact subroutine_ok_inImage_of_subroutine_ok img
      (states_recv_ct1Sampled_ok_ext A F K img.base ext hA hdealloc hmemcpy
        hC.polyDecodedMessage_ok hC.unchunkedCt1SentRecvEk_ok
        hC.unchunkedCt1SentEkReceivedSendCt2_ok hC.sendCt2Encoder_ok st msg)
  | ekReceivedCt1Sampled st =>
    exact subroutine_ok_inImage_of_subroutine_ok img
      (states_recv_ekReceivedCt1Sampled_ok_ext A F K img.base ext hdealloc hmemcpy
        hC.ekReceivedCt1SampledRecvCt1Ack_ok st msg)
  | ct1Acknowledged st =>
    exact subroutine_ok_inImage_of_subroutine_ok img
      (states_recv_ct1Acknowledged_ok_ext A F K img.base ext hdealloc hmemcpy
        hC.ct1AcknowledgedRecvEkChunk_ok st msg)
  | ct2Sampled st =>
    exact subroutine_ok_inImage_of_subroutine_ok img
      (states_recv_ct2Sampled_ok_ext A F K img.base ext hA st msg)

theorem states_recv_ok_x_of_variants
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hvar : ∀ (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi),
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
        ((statesRecvVariantSpec A F K img.base self msg).inImage img)) :
    StatesRecvOkX img A F K ext := by
  dsimp only [StatesRecvOkX]
  refine subroutine_ok_outcome_intro fun ⟨outA, selfA, msgA, self, msg⟩ R s0 hpc hrun hpre halign =>
    (hvar self msg).mono_outcome (outA, selfA, msgA) R s0 hpc hrun hpre halign fun _ hout => hout

/-- `<spqr::v1::chunked::states::States>::recv` (`0x55454`, 4,884 instructions)
    satisfies `statesRecvSpecX A F K img` on `tripleRatchetProgAtExt img.base ext`. -/
theorem states_recv_ok_x
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hC : StatesRecvContracts img A F K ext) :
    StatesRecvOkX img A F K ext :=
  states_recv_ok_x_of_variants (states_recv_variant_x hA hC)

/-- Complete `.ekSentCt1Received` arm of `<States>::recv` under `ImgCallInv img`
    (`RecvCt2ChunkOkExt`, `40176` bytes stack). -/
theorem states_recv_arm_ekSentCt1Received_inImage_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64) (hdealloc : DeallocOkExt img.base A ext)
    (hcall : RecvCt2ChunkOkExt img K F A ext)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (R : SepProp)
    (hinv : statesRecvPreInv (.ekSentCt1Received st)) (himg_s : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantSpecExt A F K img.base (.ekSentCt1Received st) msg).post (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantSpecExt A F K img.base (.ekSentCt1Received st) msg).onPanic (outA, selfA, msgA) s0 sf ∗ R)) := by
  have hpre_comm :
      memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 =
      (statesRecvRoAt img.base ∗ memRegion (s0.sp - 40176#64) 16384) ∗ memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.ekSentCt1Received st) ∗ messageAt spqrPolyApi msgA msg ∗
        A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 := by
    rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]; ac_rfl
  by_cases hgt : msg.epoch > st.uc.epoch
  · refine sepWPp_of_statesRecv_exit_ext s0 s outA selfA msgA (.ekSentCt1Received st) msg _ R ?_
    rw [states_recv_ekSentCt1Received_gt K st msg hgt, hpre_comm]
    refine SepWP.mono
      (ekSentCt1Received_arm_gt hdealloc s0 s outA selfA msgA st msg
        (statesRecvRoAt img.base ∗ memRegion (s0.sp - 40176#64) 16384)
        hgt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by rw [stackAt_statesRecvStackXExt_eq_X s0.sp]; ac_rfl)),
         hsp_sf, hcs_sf, htr_sf⟩)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · refine sepWPp_of_statesRecv_exit_ext s0 s outA selfA msgA (.ekSentCt1Received st) msg _ R ?_
      rw [states_recv_ekSentCt1Received_lt K st msg hlt, hpre_comm]
      refine SepWP.mono
        (ekSentCt1Received_arm_lt hmemcpy s0 s outA selfA msgA st msg
          (statesRecvRoAt img.base ∗ memRegion (s0.sp - 40176#64) 16384)
          hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
        (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by rw [stackAt_statesRecvStackXExt_eq_X s0.sp]; ac_rfl)),
           hsp_sf, hcs_sf, htr_sf⟩)
    · have heq : msg.epoch = st.uc.epoch :=
        BitVec.le_antisymm (BitVec.not_lt.mp hgt) (BitVec.not_lt.mp hlt)
      cases hpay : msg.payload with
      | ct2 chunk =>
        dsimp only [statesRecvRoAt, unchunkedSendCt2RoAt]
        rw [show memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
              messageAt spqrPolyApi msgA msg ∗
              (statesRecvJumpTableAt img.base ∗
                (((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
                  ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel)) ∗
                tokenInitAt img.base ∗ reduceTableAt img.base) ∗
              A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 =
            (statesRecvJumpTableAt img.base ∗
                ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
                memRegion (s0.sp - 40176#64) 15664) ∗
              memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
              messageAt spqrPolyApi msgA msg ∗
              ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
              tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool ∗
              stackAt (s0.sp - 4240#64) recvCt2ChunkStackExt ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 by
          rw [stackAt_statesRecvCalleeExt_eq_recvCt2Ext s0.sp]; ac_rfl]
        refine SepWPp.of_sepWP_inImage himg_s
          (ekSentCt1Received_arm_eq_ct2_stk (stk := recvCt2ChunkStackExt)
            (P_extra := memRegion ((s0.sp - 4240#64) - 20272#64) 720)
            (K := K) hb hcall hmemcpy s0 s outA selfA msgA st msg chunk
            (statesRecvJumpTableAt img.base ∗
              ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
              memRegion (s0.sp - 40176#64) 15664) R
            (stackAt_recvCt2ChunkExt_eq_X (s0.sp - 4240#64))
            hinv heq hpay hpc hrun hsp hsp_align hx1 hx19 hx24 htr
            (fun sf Pf _ _ ⟨hPf, hspf, hcs, htrf⟩ => ?_)
            (fun sf Pf hpan hmem_f => ?_))
        · refine ⟨fun hmem_f => ?_, hspf, hcs⟩
          dsimp only [statesRecvVariantSpecExt]
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨htrf, Satisfies.mono (sepConj_mono_left ?_) hmem_f⟩
          refine Entails.trans hPf (Entails.of_eq ?_)
          dsimp only [statesRecvRoAt, unchunkedSendCt2RoAt]
          rw [stackAt_statesRecvStackXExt_eq_X s0.sp, ← memRegion_statesRecv_15664_720 s0.sp]
          ac_rfl
        · have hpan' := hpan hmem_f
          dsimp only [statesRecvVariantSpecExt, statesRecvOnPanic]
          rw [sepConj_assoc, satisfies_pure_sepConj] at hpan' ⊢
          refine ⟨⟨?_, hpan'.1.2⟩, hpan'.2⟩
          cases hpan'.1.1 with
          | inl hp => exact Or.inl (states_recv_ekSentCt1Received_eq_ct2_panic K st msg chunk heq hpay hp)
          | inr haf => exact Or.inr haf
      | none | hdr _ | ek _ | ekCt1Ack _ | ct1 _ | ct1Ack _ =>
        have hct2 : ∀ c, msg.payload ≠ .ct2 c := by intro c hc; rw [hpay] at hc; cases hc
        refine sepWPp_of_statesRecv_exit_ext s0 s outA selfA msgA (.ekSentCt1Received st) msg _ R ?_
        rw [states_recv_ekSentCt1Received_eq_other K st msg heq hct2, hpre_comm]
        refine SepWP.mono
          (ekSentCt1Received_arm_eq_other hmemcpy s0 s outA selfA msgA st msg
            (statesRecvRoAt img.base ∗ memRegion (s0.sp - 40176#64) 16384)
            heq hct2 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
          (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            ⟨Entails.trans hPf (Entails.of_eq (by rw [stackAt_statesRecvStackXExt_eq_X s0.sp]; ac_rfl)),
             hsp_sf, hcs_sf, htr_sf⟩)

/-- Per-variant `.inImage img` specification proof for `States.ekSentCt1Received st`
    (`tag = 6#64`, `40176` bytes stack, `RecvCt2ChunkOkExt`). -/
theorem states_recv_ekSentCt1Received_ok_x_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt img.base A ext) (hcall : RecvCt2ChunkOkExt img K F A ext)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpecExt A F K img.base (.ekSentCt1Received st) msg).inImage img) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [Spec.inImage, statesRecvVariantSpecExt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg0, ⟨hb, hx0, hx1, hx2, hinv⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackXExt ∗ (memRegion outA v1RecvSize ∗
      chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  have hpro := states_recv_prologue_ext (b := img.base) (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool) hsp0_align hpc0 hrun0
  refine sepWPp_seq_clean_inImage_ct2 himg0 hpro ?_
  intro s1 hpc1 hrun1 himg1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1; dsimp only [chunkedStatesAt]
  have hdisp := states_recv_dispatch (b := img.base) (ext := ext) hb s1 (s0.sp - 4240#64) selfA 6#64
    (chunkedEkSentCt1ReceivedAt A (selfA + 8#64) st ∗ memRegion (selfA + 512#64) 416 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗ memRegion (s0.sp - 4240#64) 4144 ∗
     statesRecvSavedCells s0)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) hpc1 hrun1 hsp1 hx1_1
  dsimp only [statesRecvArmOffset] at hdisp
  refine sepWPp_seq_clean_inImage_ct2 himg1 (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 himg2 ⟨hsp2, hx0_2, hx1_2, hx2_2, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [chunkedStatesAt]; ac_rfl))
    (states_recv_arm_ekSentCt1Received_inImage_ext hb hdealloc hcall hmemcpy s0 s2 outA selfA msgA st msg R
      hinv himg2 hpc2 hrun2 hsp2 hsp0_align hx1_2 hx19_2 hx24_2 (htr2.trans htr1))

/-- Per-variant in-image correctness of `<spqr::v1::chunked::states::States>::recv` (`0x55454`)
    with `+ extHookStack` (`40176` bytes) across all 11 `States` constructors wired directly
    from `AllocContracts` and `StatesRecvContractsExt`. -/
theorem states_recv_variant_x_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hC : StatesRecvContractsExt img A F K ext)
    (self : States spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpecExt A F K img.base self msg).inImage img) := by
  have hdealloc : DeallocOkExt img.base A ext := deallocOkExt_of_allocContracts hA
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName) sessionMemcpyRegionSpec := by
    have h0 := hA.session_memcpy_region_ok_at memcpyName 0 (Nat.add_zero _)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h0
  cases self with
  | keysUnsampled st =>
    exact statesRecvVariant_inImage_grow_stack (subroutine_ok_inImage_of_subroutine_ok img
      (states_recv_keysUnsampled_ok_ext A F K img.base ext hA st msg))
  | keysSampled st =>
    exact statesRecvVariant_inImage_grow_stack (subroutine_ok_inImage_of_subroutine_ok img
      (states_recv_keysSampled_ok_ext A F K img.base ext hdealloc
        hC.keysSampledRecvCt1Chunk_ok hmemcpy st msg))
  | headerSent st =>
    exact statesRecvVariant_inImage_grow_stack (subroutine_ok_inImage_of_subroutine_ok img
      (states_recv_headerSent_ok_ext A F K img.base ext hdealloc
        hC.headerSentRecvCt1Chunk_ok hmemcpy st msg))
  | ct1Received st =>
    exact statesRecvVariant_inImage_grow_stack (subroutine_ok_inImage_of_subroutine_ok img
      (states_recv_ct1Received_ok_ext A F K img.base ext hdealloc
        hC.ct1ReceivedRecvCt2Chunk_ok hmemcpy st msg))
  | ekSentCt1Received st =>
    exact states_recv_ekSentCt1Received_ok_x_ext hdealloc
      hC.ekSentCt1ReceivedRecvCt2Chunk_ok hmemcpy st msg
  | noHeaderReceived st =>
    exact statesRecvVariant_inImage_grow_stack (states_recv_noHeaderReceived_ok_x img A F K ext
      hdealloc hmemcpy hC.noHeaderReceivedRecvHdrChunk_ok st msg)
  | headerReceived st =>
    exact statesRecvVariant_inImage_grow_stack (subroutine_ok_inImage_of_subroutine_ok img
      (states_recv_headerReceived_ok_ext A F K img.base ext hA st msg))
  | ct1Sampled st =>
    exact statesRecvVariant_inImage_grow_stack (subroutine_ok_inImage_of_subroutine_ok img
      (states_recv_ct1Sampled_ok_ext A F K img.base ext hA hdealloc hmemcpy
        hC.polyDecodedMessage_ok hC.unchunkedCt1SentRecvEk_ok
        hC.unchunkedCt1SentEkReceivedSendCt2_ok hC.sendCt2Encoder_ok st msg))
  | ekReceivedCt1Sampled st =>
    exact statesRecvVariant_inImage_grow_stack (subroutine_ok_inImage_of_subroutine_ok img
      (states_recv_ekReceivedCt1Sampled_ok_ext A F K img.base ext hdealloc hmemcpy
        hC.ekReceivedCt1SampledRecvCt1Ack_ok st msg))
  | ct1Acknowledged st =>
    exact statesRecvVariant_inImage_grow_stack (subroutine_ok_inImage_of_subroutine_ok img
      (states_recv_ct1Acknowledged_ok_ext A F K img.base ext hdealloc hmemcpy
        hC.ct1AcknowledgedRecvEkChunk_ok st msg))
  | ct2Sampled st =>
    exact statesRecvVariant_inImage_grow_stack (subroutine_ok_inImage_of_subroutine_ok img
      (states_recv_ct2Sampled_ok_ext A F K img.base ext hA st msg))

theorem states_recv_ok_x_of_variants_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hvar : ∀ (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi),
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
        ((statesRecvVariantSpecExt A F K img.base self msg).inImage img)) :
    StatesRecvOkXExt img A F K ext := by
  dsimp only [StatesRecvOkXExt]
  refine subroutine_ok_outcome_intro fun ⟨outA, selfA, msgA, self, msg⟩ R s0 hpc hrun hpre halign =>
    (hvar self msg).mono_outcome (outA, selfA, msgA) R s0 hpc hrun hpre halign fun _ hout => hout

/-- `<spqr::v1::chunked::states::States>::recv` (`0x55454`, 4,884 instructions)
    satisfies `statesRecvSpecXExt A F K img` (`40176` bytes stack) on
    `tripleRatchetProgAtExt img.base ext` under `StatesRecvContractsExt`. -/
theorem states_recv_ok_x_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hC : StatesRecvContractsExt img A F K ext) :
    StatesRecvOkXExt img A F K ext :=
  states_recv_ok_x_of_variants_ext (states_recv_variant_x_ext hA hC)

/-- `.rodata` slice at `0x83748` (`35` bytes): `Authenticator.ctLabel`. -/
theorem rodata_ctLabel_statesRecv {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) (n := 35) (bs := Authenticator.ctLabel)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

/-- Extract the `.rodata` components of `statesRecvRoAt img.base`
    (`statesRecvJumpTableAt img.base`, `(img.base + 0xa2748#64) ↦ᵣ Authenticator.ctLabel`,
    and `reduceTableAt img.base`) from `Obj.Loads libsignalSessionImage img` and `img.FrozenLoaded s`,
    requiring only the `.bss` globals `((img.base + 0xaa080#64) ↦₆₄ 0#64) ∗ tokenInitAt img.base` in `s.mem`. -/
theorem rodata_statesRecvRoAt {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp}
    (hP : s.mem ⊨ ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ tokenInitAt img.base ∗ P) :
    s.mem ⊨ statesRecvRoAt img.base ∗ P := by
  have h1 := rodata_statesRecvJumpTable himg hF hP
  have h2 := rodata_ctLabel_statesRecv himg hF h1
  have h3 := rodata_reduceTable himg hF h2
  refine Satisfies.mono (Entails.of_eq ?_) h3
  dsimp only [statesRecvRoAt, unchunkedSendCt2RoAt]
  ac_rfl

end CryptoVerification.SpqrV1.States.Recv
