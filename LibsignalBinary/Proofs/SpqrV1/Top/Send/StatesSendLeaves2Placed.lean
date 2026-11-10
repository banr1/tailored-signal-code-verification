/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1Placed
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1StepsPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves2
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Relocatable Inlined `States::send` Leaf-Call Arms (Block 124)

Verifies the six leaf-call arms of `<States>::send` inlined in Block 124
(`spqr::send::<HookRng>`) under `[LibsignalPlacement]`.
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

/-- Relocatable leaf-call arm 1: `.headerSent s` (`+960 -> +3068`). -/
theorem step_send_arm_headerSent_placed {F : ShaCompress}
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    (hcall : HeaderSentSendEkChunkPlacedOkX A F ext) {s0 s : State} (sp : BitVec 64)
    (st outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ek_chunk = .ok (outSt, chunk))
    {ret : BitVec 64} {P Frame Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 960#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A (sp + 0x950#64) (.headerSent st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (880 + chunkSize)) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ek chunk } (.headerSent outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (880 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ek chunk) ∗
          spqrSendKeySlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A (sp + 0x590#64) (.headerSent outSt)) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (spqrSendPlacedProg ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hcall_at : subroutine_ok ((blkPC_124).rebase (blkPl_124).base (Rust.withPanics ext))
      (lsmpl.base 336) (withLsCodeRoLoaded lsmpl (SpqrV1.headerSentSendEkChunkPlacedSpec A F)) := hcall
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x950#64) (.headerSent st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by rw [BitVec.add_assoc]; rfl]
  dsimp only [chunkedStatesWord0, chunkedStatesTail920At]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_headerSent A sp st; rw [h_ep]
  apply of_sepWP_lscro (mid := lsmpl.base 336) hcrl; wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hcrl_1
  refine call_lscro_calleeStack (x := ({
      outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } : HeaderSentSendEkChunkGhost F))
    (s0 := s0) sp (polyNextChunkStack + 1328) (by decide)
    (T_pre := memRegion (sp + 0x1260#64) (880 + chunkSize) ∗ chunkedHeaderSentAt A (sp + 0x958#64) st ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
    (T_post := fun _ => chunkedHeaderSentAt A (sp + 0x1260#64) outSt ∗
      chunkAt ((sp + 0x1260#64) + 880#64) chunk ∗ memRegion (sp + 0x958#64) 880 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
    (F := ((sp + 0x950#64) ↦₆₄ 4#64) ∗ memRegion ((sp + 0x958#64) + 880#64) 40 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗ Frame)
    (φ_pre := _) (φ_post := _) hcall_at hcrl_1
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (by simp only [arm64_norm, *]) (ret_pc := (blkPl_124).base + 980#64) (by simp only [arm64_norm, *])
    (by dsimp only [SpqrV1.headerSentSendEkChunkPlacedSpec]; ac_rfl) (by simp only [arm64_norm, *])
    (by rw [h_ep]; ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
    (by intro sf; dsimp only [SpqrV1.headerSentSendEkChunkPlacedSpec]; ac_rfl) ?_
  intro sm hpc_sm hrun_sm hsp_sm htr_sm hcrl_sm hx19_sm hx20_sm _ hx22_sm _ _ hx25_sm hx26_sm _ hx28_sm hvregs_sm
  simp only [arm64_norm, *] at htr_sm hx19_sm hx20_sm hx22_sm hx25_sm hx26_sm hx28_sm hvregs_sm
  apply of_sepWP_lscro (mid := (blkPl_124).base + 3068#64) hcrl_sm; wp_steps
  rw [ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 880) (k := 40) (b' := (sp + 0x590#64) + 880#64) rfl rfl (by decide)]
  refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedHeaderSentAt A outSt)
    (sp + 0x590#64) (sp + 0x1260#64) (s0 := s0) (sp_call := sp)
    (Frame := stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      ((sp + 0x950#64) ↦₆₄ 4#64) ∗ memRegion (sp + 0x958#64) 880 ∗
      memRegion ((sp + 0x958#64) + 880#64) 40 ∗ chunkAt ((sp + 0x1260#64) + 880#64) chunk ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion ((sp + 0x590#64) + 880#64) 40 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_124).base + 1000#64) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf
  obtain ⟨cw0, cw1, cw2, cw3, hchunk⟩ := chunkAt_extract_words chunk
  have h15d0 : (sp + 0x1260#64) + 880#64 = sp + 0x15d0#64 := by rw [BitVec.add_assoc]; rfl
  have hchunk_src := chunkAt_sp_add_eq sp 0x15d0#64 0x15d8#64 0x15e0#64 0x15e8#64 0x15f0#64 chunk cw0 cw1 cw2 cw3 hchunk
  have hchunk_dst := chunkAt_sp_add_eq sp 0x550#64 0x558#64 0x560#64 0x568#64 0x570#64 chunk cw0 cw1 cw2 cw3 hchunk
  rw [h15d0, hchunk_src, memRegion_38_eq_chunk_slot sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; iterate 5 (apply SepWP.exists_elim; intro _)
  wp_steps
  refine finish_sepWP_lscro (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (fun hcrl_f => hnext _ hcrl_f ⟨by simp only [spqrSendPlacedEntry, arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩) ?_
  exact leaf_arm_post_entails_placed A sp 4#64 _ _ _ 880 _
    (chunkedHeaderSentAt A (sp + 0x590#64) outSt) chunk (.ek chunk) (.headerSent outSt) Frame
    (by decide) (by simp only [arm64_norm]; rfl)
    (by dsimp only [spqrSendPayloadSlotAt]; exact Entails.pure_right (by simp only [arm64_norm]) (Entails.refl _))
    rfl (by rw [h15d0, hchunk_src, hchunk_dst]; ac_rfl)

/-- Relocatable leaf-call arm 2: `.ct1Received s` (`+1040 -> +3068`). -/
theorem step_send_arm_ct1Received_placed {F : ShaCompress}
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    (hcall : Ct1ReceivedSendEkChunkPlacedOkX A F ext) {s0 s : State} (sp : BitVec 64)
    (st outSt : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ek_chunk = .ok (outSt, chunk))
    {ret : BitVec 64} {P Frame Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 1040#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A (sp + 0x950#64) (.ct1Received st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (504 + chunkSize)) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ekCt1Ack chunk } (.ct1Received outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (504 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ekCt1Ack chunk) ∗
          spqrSendKeySlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A (sp + 0x590#64) (.ct1Received outSt)) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (spqrSendPlacedProg ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hcall_at : subroutine_ok ((blkPC_124).rebase (blkPl_124).base (Rust.withPanics ext))
      (lsmpl.base 345) (withLsCodeRoLoaded lsmpl (SpqrV1.ct1ReceivedSendEkChunkPlacedSpec A F)) := hcall
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x950#64) (.ct1Received st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by rw [BitVec.add_assoc]; rfl]
  dsimp only [chunkedStatesWord0, chunkedStatesTail920At]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ct1Received A sp st; rw [h_ep]
  apply of_sepWP_lscro (mid := lsmpl.base 345) hcrl; wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hcrl_1
  refine call_lscro_calleeStack (x := ({
      outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } : Ct1ReceivedSendEkChunkGhost F))
    (s0 := s0) sp (polyNextChunkStack + 944) (by decide)
    (T_pre := memRegion (sp + 0x1260#64) (504 + chunkSize) ∗ chunkedCt1ReceivedAt A (sp + 0x958#64) st ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
    (T_post := fun _ => chunkedCt1ReceivedAt A (sp + 0x1260#64) outSt ∗
      chunkAt ((sp + 0x1260#64) + 504#64) chunk ∗ memRegion (sp + 0x958#64) 504 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
    (F := ((sp + 0x950#64) ↦₆₄ 5#64) ∗ memRegion ((sp + 0x958#64) + 504#64) 416 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗ Frame)
    (φ_pre := _) (φ_post := _) hcall_at hcrl_1
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (by simp only [arm64_norm, *]) (ret_pc := (blkPl_124).base + 1068#64) (by simp only [arm64_norm, *])
    (by dsimp only [SpqrV1.ct1ReceivedSendEkChunkPlacedSpec]; ac_rfl) (by simp only [arm64_norm, *])
    (by rw [h_ep]; ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
    (by intro sf; dsimp only [SpqrV1.ct1ReceivedSendEkChunkPlacedSpec]; ac_rfl) ?_
  intro sm hpc_sm hrun_sm hsp_sm htr_sm hcrl_sm hx19_sm hx20_sm _ hx22_sm _ _ hx25_sm hx26_sm _ hx28_sm hvregs_sm
  simp only [arm64_norm, *] at htr_sm hx19_sm hx20_sm hx22_sm hx25_sm hx26_sm hx28_sm hvregs_sm
  apply of_sepWP_lscro (mid := (blkPl_124).base + 3068#64) hcrl_sm; wp_steps
  rw [ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 504) (k := 416) (b' := (sp + 0x590#64) + 504#64) rfl rfl (by decide)]
  refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedCt1ReceivedAt A outSt)
    (sp + 0x590#64) (sp + 0x1260#64) (s0 := s0) (sp_call := sp)
    (Frame := stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      ((sp + 0x950#64) ↦₆₄ 5#64) ∗ memRegion (sp + 0x958#64) 504 ∗
      memRegion ((sp + 0x958#64) + 504#64) 416 ∗ chunkAt ((sp + 0x1260#64) + 504#64) chunk ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion ((sp + 0x590#64) + 504#64) 416 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_124).base + 1088#64) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf
  obtain ⟨cw0, cw1, cw2, cw3, hchunk⟩ := chunkAt_extract_words chunk
  have h1458 : (sp + 0x1260#64) + 504#64 = sp + 0x1458#64 := by rw [BitVec.add_assoc]; rfl
  have hchunk_src := chunkAt_sp_add_eq sp 0x1458#64 0x1460#64 0x1468#64 0x1470#64 0x1478#64 chunk cw0 cw1 cw2 cw3 hchunk
  have hchunk_dst := chunkAt_sp_add_eq sp 0x550#64 0x558#64 0x560#64 0x568#64 0x570#64 chunk cw0 cw1 cw2 cw3 hchunk
  rw [h1458, hchunk_src, memRegion_38_eq_chunk_slot sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; iterate 5 (apply SepWP.exists_elim; intro _)
  wp_steps
  refine finish_sepWP_lscro (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (fun hcrl_f => hnext _ hcrl_f ⟨by simp only [spqrSendPlacedEntry, arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩) ?_
  exact leaf_arm_post_entails_placed A sp 5#64 _ _ _ 504 _
    (chunkedCt1ReceivedAt A (sp + 0x590#64) outSt) chunk (.ekCt1Ack chunk) (.ct1Received outSt) Frame
    (by decide) (by simp only [arm64_norm]; rfl)
    (by dsimp only [spqrSendPayloadSlotAt]; exact Entails.pure_right (by simp only [arm64_norm]) (Entails.refl _))
    rfl (by rw [h1458, hchunk_src, hchunk_dst]; ac_rfl)

/-- Relocatable leaf-call arm 3: `.keysSampled s` (`+1208 -> +3056 -> +3068`). -/
theorem step_send_arm_keysSampled_placed {F : ShaCompress}
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    (hcall : Ct1ReceivedSendEkChunkPlacedOkX A F ext) {s0 s : State} (sp : BitVec 64)
    (st outSt : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_hdr_chunk = .ok (outSt, chunk))
    {ret : BitVec 64} {P Frame Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 1208#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A (sp + 0x950#64) (.keysSampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (504 + chunkSize)) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .hdr chunk } (.keysSampled outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (504 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.hdr chunk) ∗
          spqrSendKeySlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A (sp + 0x590#64) (.keysSampled outSt)) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (spqrSendPlacedProg ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hcall_at : subroutine_ok ((blkPC_124).rebase (blkPl_124).base (Rust.withPanics ext))
      (lsmpl.base 345) (withLsCodeRoLoaded lsmpl (SpqrV1.ct1ReceivedSendEkChunkPlacedSpec A F)) := hcall
  have hsend' := keysSampled_send_hdr_chunk_to_ct1Received hsend
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x950#64) (.keysSampled st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by rw [BitVec.add_assoc]; rfl]
  dsimp only [chunkedStatesWord0, chunkedStatesTail920At]
  rw [chunkedKeysSampledAt_eq_ct1ReceivedAt]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ct1Received A sp (chunkedKeysSampledToCt1Received st); rw [h_ep]
  apply of_sepWP_lscro (mid := lsmpl.base 345) hcrl; wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hcrl_1
  refine call_lscro_calleeStack (x := ({
      outA := sp + 0x1260#64, stA := sp + 0x958#64, st := chunkedKeysSampledToCt1Received st,
      outSt := chunkedKeysSampledToCt1Received outSt, chunk := chunk } : Ct1ReceivedSendEkChunkGhost F))
    (s0 := s0) sp (polyNextChunkStack + 944) (by decide)
    (T_pre := memRegion (sp + 0x1260#64) (504 + chunkSize) ∗
      chunkedCt1ReceivedAt A (sp + 0x958#64) (chunkedKeysSampledToCt1Received st) ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
    (T_post := fun _ => chunkedCt1ReceivedAt A (sp + 0x1260#64) (chunkedKeysSampledToCt1Received outSt) ∗
      chunkAt ((sp + 0x1260#64) + 504#64) chunk ∗ memRegion (sp + 0x958#64) 504 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
    (F := ((sp + 0x950#64) ↦₆₄ 3#64) ∗ memRegion ((sp + 0x958#64) + 504#64) 416 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗ Frame)
    (φ_pre := _) (φ_post := _) hcall_at hcrl_1
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (by simp only [arm64_norm, *]) (ret_pc := (blkPl_124).base + 1236#64) (by simp only [arm64_norm, *])
    (by dsimp only [SpqrV1.ct1ReceivedSendEkChunkPlacedSpec]; ac_rfl) (by simp only [arm64_norm, *])
    (by rw [h_ep]; ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
    (by intro sf; dsimp only [SpqrV1.ct1ReceivedSendEkChunkPlacedSpec]; ac_rfl) ?_
  intro sm hpc_sm hrun_sm hsp_sm htr_sm hcrl_sm hx19_sm hx20_sm _ hx22_sm _ _ hx25_sm hx26_sm _ hx28_sm hvregs_sm
  simp only [arm64_norm, *] at htr_sm hx19_sm hx20_sm hx22_sm hx25_sm hx26_sm hx28_sm hvregs_sm
  rw [← chunkedKeysSampledAt_eq_ct1ReceivedAt]
  apply of_sepWP_lscro (mid := (blkPl_124).base + 3068#64) hcrl_sm; wp_steps
  rw [ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 504) (k := 416) (b' := (sp + 0x590#64) + 504#64) rfl rfl (by decide)]
  refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedKeysSampledAt A outSt)
    (sp + 0x590#64) (sp + 0x1260#64) (s0 := s0) (sp_call := sp)
    (Frame := stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      ((sp + 0x950#64) ↦₆₄ 3#64) ∗ memRegion (sp + 0x958#64) 504 ∗
      memRegion ((sp + 0x958#64) + 504#64) 416 ∗ chunkAt ((sp + 0x1260#64) + 504#64) chunk ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion ((sp + 0x590#64) + 504#64) 416 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_124).base + 1256#64) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  simp only [arm64_norm, chunkedKeysSampledToCt1Received,
    unchunkedHeaderSentToEkSentCt1Received, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf
  obtain ⟨cw0, cw1, cw2, cw3, hchunk⟩ := chunkAt_extract_words chunk
  have h1458 : (sp + 0x1260#64) + 504#64 = sp + 0x1458#64 := by rw [BitVec.add_assoc]; rfl
  have hchunk_src := chunkAt_sp_add_eq sp 0x1458#64 0x1460#64 0x1468#64 0x1470#64 0x1478#64 chunk cw0 cw1 cw2 cw3 hchunk
  have hchunk_dst := chunkAt_sp_add_eq sp 0x550#64 0x558#64 0x560#64 0x568#64 0x570#64 chunk cw0 cw1 cw2 cw3 hchunk
  rw [h1458, hchunk_src, memRegion_38_eq_chunk_slot sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; iterate 5 (apply SepWP.exists_elim; intro _)
  wp_steps
  refine finish_sepWP_lscro (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (fun hcrl_f => hnext _ hcrl_f ⟨by simp only [spqrSendPlacedEntry, arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩) ?_
  exact leaf_arm_post_entails_placed A sp 3#64 _ _ _ 504 _
    (chunkedKeysSampledAt A (sp + 0x590#64) outSt) chunk (.hdr chunk) (.keysSampled outSt) Frame
    (by decide) (by simp only [arm64_norm]; rfl)
    (by dsimp only [spqrSendPayloadSlotAt]; exact Entails.pure_right (by simp only [arm64_norm]) (Entails.refl _))
    rfl (by rw [h1458, hchunk_src, hchunk_dst]; ac_rfl)

theorem ct1Sampled_arm_post_entails_placed {F : ShaCompress} (A : RustAlloc)
    (sp w0 x21 x27 : BitVec 64) (x24_8 : BitVec 8)
    (P : SepProp) (outSt : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (Frame : SepProp) (hx21 : x21 = LibsignalTripleRatchetRepr.noneCap)
    (hpay : chunkAt (sp + 0x550#64) chunk ∗ memRegion (sp + 0x572#64) 4 ⊢
      spqrSendPayloadSlotAt sp x24_8 (.ct1 chunk))
    (hP_eq : P =
      (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        memRegion (sp + 0x950#64) 928 ∗
        (((sp + 0x1260#64) ↦₆₄ w0) ∗ memRegion (sp + 0x1268#64) 920 ∗
          chunkAt ((sp + 0x1260#64) + 928#64) chunk) ∗
        (chunkAt (sp + 0x550#64) chunk ∗ memRegion (sp + 0x572#64) 4) ∗
        memRegion (sp + 0x580#64) 16 ∗
        chunkedCt1SampledTail920At A (sp + 0x590#64) outSt) ∗ Frame) :
    P ⊢
      (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (928 + chunkSize) ∗
        spqrSendPayloadSlotAt sp x24_8 (.ct1 chunk) ∗ spqrSendKeySlotAt A sp x21 x27 none ∗
        chunkedStatesTail920At A (sp + 0x590#64) (.ct1Sampled outSt)) ∗ Frame := by
  have hkey : memRegion (sp + 0x580#64) 16 ⊢ spqrSendKeySlotAt A sp x21 x27 none := by
    dsimp only [spqrSendKeySlotAt]; exact Entails.pure_right hx21 (Entails.refl _)
  have h8 : ((sp + 0x1260#64) ↦₆₄ w0) ⊢ memRegion (sp + 0x1260#64) 8 := by
    rw [pointsTo64_eq_pointsToBytes, ← unpack64_length w0]; exact pointsToBytes_entails_memRegion _ _
  have h928 : ((sp + 0x1260#64) ↦₆₄ w0) ∗ memRegion (sp + 0x1268#64) 920 ⊢ memRegion (sp + 0x1260#64) 928 := by
    refine Entails.trans (sepConj_mono_left h8) ?_
    rw [ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 8) (k := 920) (b' := sp + 0x1268#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)]
    exact Entails.refl _
  have h2 : (((sp + 0x1260#64) ↦₆₄ w0) ∗ memRegion (sp + 0x1268#64) 920 ∗
      chunkAt ((sp + 0x1260#64) + 928#64) chunk) ⊢ memRegion (sp + 0x1260#64) (928 + chunkSize) := by
    rw [← sepConj_assoc]
    exact Entails.trans (sepConj_mono_left h928) (scratch_and_chunk_entails_memRegion sp 928 chunk)
  rw [hP_eq]; dsimp only [chunkedStatesTail920At]
  exact sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono h2 (sepConj_mono hpay (sepConj_mono_left hkey))))))))

/-- Relocatable leaf-call arm 4: `.ct1Sampled s` (`+1128 -> +2356 -> +3068`). -/
theorem step_send_arm_ct1Sampled_placed {F : ShaCompress}
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    (hcall : Ct1SampledSendCt1ChunkPlacedOkX A F ext) {s0 s : State} (sp : BitVec 64)
    (st outSt : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ct1_chunk = .ok (outSt, chunk))
    {ret : BitVec 64} {P Frame Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 1128#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A (sp + 0x950#64) (.ct1Sampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (928 + chunkSize)) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ct1 chunk } (.ct1Sampled outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (928 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1 chunk) ∗
          spqrSendKeySlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A (sp + 0x590#64) (.ct1Sampled outSt)) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (spqrSendPlacedProg ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hcall_at : subroutine_ok ((blkPC_124).rebase (blkPl_124).base (Rust.withPanics ext))
      (lsmpl.base 335) (withLsCodeRoLoaded lsmpl (SpqrV1.ct1SampledSendCt1ChunkPlacedSpec A F)) := hcall
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP; dsimp only [chunkedStatesAt]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ct1Sampled A sp st; rw [h_ep]
  apply of_sepWP_lscro (mid := lsmpl.base 335) hcrl; wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hcrl_1
  refine call_lscro_calleeStack (x := ({
      outA := sp + 0x1260#64, stA := sp + 0x950#64, st := st, outSt := outSt, chunk := chunk } : Ct1SampledSendCt1ChunkGhost F))
    (s0 := s0) sp (polyNextChunkStack + 1376) (by decide)
    (T_pre := memRegion (sp + 0x1260#64) (928 + chunkSize) ∗ chunkedCt1SampledAt A (sp + 0x950#64) st ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
    (T_post := fun _ => chunkedCt1SampledAt A (sp + 0x1260#64) outSt ∗
      chunkAt ((sp + 0x1260#64) + 928#64) chunk ∗ memRegion (sp + 0x950#64) 928 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
    (F := memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗ Frame)
    (φ_pre := _) (φ_post := _) hcall_at hcrl_1
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (by simp only [arm64_norm, *]) (ret_pc := (blkPl_124).base + 1156#64) (by simp only [arm64_norm, *])
    (by dsimp only [SpqrV1.ct1SampledSendCt1ChunkPlacedSpec]; ac_rfl) (by simp only [arm64_norm, *])
    (by rw [h_ep]; ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
    (by intro sf; dsimp only [SpqrV1.ct1SampledSendCt1ChunkPlacedSpec]; ac_rfl) ?_
  intro sm hpc_sm hrun_sm hsp_sm htr_sm hcrl_sm hx19_sm _ _ hx22_sm _ hx24_sm hx25_sm hx26_sm _ hx28_sm hvregs_sm
  simp only [arm64_norm, *] at htr_sm hx19_sm hx22_sm hx24_sm hx25_sm hx26_sm hx28_sm hvregs_sm
  rw [chunkedCt1SampledAt_eq_tag_tail920 A (sp + 0x1260#64) outSt,
      show (sp + 0x1260#64) + 8#64 = sp + 0x1268#64 by rw [BitVec.add_assoc]; rfl]
  apply of_sepWP_lscro (mid := (blkPl_124).base + 3068#64) hcrl_sm; wp_steps
  refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedCt1SampledTail920At A outSt)
    (sp + 0x590#64) (sp + 0x1268#64) (s0 := s0) (sp_call := sp)
    (Frame := stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      memRegion (sp + 0x950#64) 928 ∗ ((sp + 0x1260#64) ↦₆₄ polyEncoderTagVal outSt.sending_ct1.s) ∗
      chunkAt ((sp + 0x1260#64) + 928#64) chunk ∗ memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_124).base + 1176#64) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hx19_sf hx20_sf _ hx22_sf _ hx24_sf hx25_sf hx26_sf _ hx28_sf hvregs_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx24_sf hx25_sf hx26_sf hx28_sf hvregs_sf
  obtain ⟨cw0, cw1, cw2, cw3, hchunk⟩ := chunkAt_extract_words chunk
  have h1600 : (sp + 0x1260#64) + 928#64 = sp + 0x1600#64 := by rw [BitVec.add_assoc]; rfl
  have hchunk_src := chunkAt_sp_add_eq sp 0x1600#64 0x1608#64 0x1610#64 0x1618#64 0x1620#64 chunk cw0 cw1 cw2 cw3 hchunk
  have hchunk_dst := chunkAt_sp_add_eq sp 0x550#64 0x558#64 0x560#64 0x568#64 0x570#64 chunk cw0 cw1 cw2 cw3 hchunk
  rw [h1600, hchunk_src, memRegion_38_eq_chunk_slot sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; iterate 5 (apply SepWP.exists_elim; intro _)
  wp_steps
  refine finish_sepWP_lscro (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (fun hcrl_f => hnext _ hcrl_f ⟨by simp only [spqrSendPlacedEntry, arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩) ?_
  exact ct1Sampled_arm_post_entails_placed A sp (polyEncoderTagVal outSt.sending_ct1.s) _ _ _ _
    outSt chunk Frame (by simp only [arm64_norm]; rfl)
    (by dsimp only [spqrSendPayloadSlotAt]; exact Entails.pure_right (by simp only [arm64_norm, *]) (Entails.refl _))
    (by rw [h1600, hchunk_src, hchunk_dst]; ac_rfl)

/-- Relocatable leaf-call arm 5: `.ct2Sampled s` (`+2372 -> +3068`). -/
theorem step_send_arm_ct2Sampled_placed {F : ShaCompress}
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    (hcall : Ct2SampledSendCt2ChunkPlacedOkX A F ext) {s0 s : State} (sp : BitVec 64)
    (st outSt : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ct2_chunk = .ok (outSt, chunk))
    {ret : BitVec 64} {P Frame Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 2372#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A (sp + 0x950#64) (.ct2Sampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (456 + chunkSize)) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ct2 chunk } (.ct2Sampled outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (456 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct2 chunk) ∗
          spqrSendKeySlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A (sp + 0x590#64) (.ct2Sampled outSt)) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (spqrSendPlacedProg ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hcall_at : subroutine_ok ((blkPC_124).rebase (blkPl_124).base (Rust.withPanics ext))
      (lsmpl.base 354) (withLsCodeRoLoaded lsmpl (SpqrV1.ct2SampledSendCt2ChunkPlacedSpec A F)) := hcall
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x950#64) (.ct2Sampled st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by rw [BitVec.add_assoc]; rfl]
  dsimp only [chunkedStatesWord0, chunkedStatesTail920At]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ct2Sampled A sp st; rw [h_ep]
  apply of_sepWP_lscro (mid := lsmpl.base 354) hcrl; wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hcrl_1
  refine call_lscro_calleeStack (x := ({
      outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } : Ct2SampledSendCt2ChunkGhost F))
    (s0 := s0) sp (polyNextChunkStack + 896) (by decide)
    (T_pre := memRegion (sp + 0x1260#64) (456 + chunkSize) ∗ chunkedCt2SampledAt A (sp + 0x958#64) st ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
    (T_post := fun _ => chunkedCt2SampledAt A (sp + 0x1260#64) outSt ∗
      chunkAt ((sp + 0x1260#64) + 456#64) chunk ∗ memRegion (sp + 0x958#64) 456 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
    (F := ((sp + 0x950#64) ↦₆₄ 12#64) ∗ memRegion ((sp + 0x958#64) + 456#64) 464 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗ Frame)
    (φ_pre := _) (φ_post := _) hcall_at hcrl_1
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (by simp only [arm64_norm, *]) (ret_pc := (blkPl_124).base + 2400#64) (by simp only [arm64_norm, *])
    (by dsimp only [SpqrV1.ct2SampledSendCt2ChunkPlacedSpec]; ac_rfl) (by simp only [arm64_norm, *])
    (by rw [h_ep]; ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
    (by intro sf; dsimp only [SpqrV1.ct2SampledSendCt2ChunkPlacedSpec]; ac_rfl) ?_
  intro sm hpc_sm hrun_sm hsp_sm htr_sm hcrl_sm hx19_sm hx20_sm _ hx22_sm _ _ hx25_sm hx26_sm _ hx28_sm hvregs_sm
  simp only [arm64_norm, *] at htr_sm hx19_sm hx20_sm hx22_sm hx25_sm hx26_sm hx28_sm hvregs_sm
  apply of_sepWP_lscro (mid := (blkPl_124).base + 3068#64) hcrl_sm; wp_steps
  rw [ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 456) (k := 464) (b' := (sp + 0x590#64) + 456#64) rfl rfl (by decide)]
  refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedCt2SampledAt A outSt)
    (sp + 0x590#64) (sp + 0x1260#64) (s0 := s0) (sp_call := sp)
    (Frame := stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      ((sp + 0x950#64) ↦₆₄ 12#64) ∗ memRegion (sp + 0x958#64) 456 ∗
      memRegion ((sp + 0x958#64) + 456#64) 464 ∗ chunkAt ((sp + 0x1260#64) + 456#64) chunk ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion ((sp + 0x590#64) + 456#64) 464 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_124).base + 2420#64) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf
  obtain ⟨cw0, cw1, cw2, cw3, hchunk⟩ := chunkAt_extract_words chunk
  have h1428 : (sp + 0x1260#64) + 456#64 = sp + 0x1428#64 := by rw [BitVec.add_assoc]; rfl
  have hchunk_src := chunkAt_sp_add_eq sp 0x1428#64 0x1430#64 0x1438#64 0x1440#64 0x1448#64 chunk cw0 cw1 cw2 cw3 hchunk
  have hchunk_dst := chunkAt_sp_add_eq sp 0x550#64 0x558#64 0x560#64 0x568#64 0x570#64 chunk cw0 cw1 cw2 cw3 hchunk
  rw [h1428, hchunk_src, memRegion_38_eq_chunk_slot sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; iterate 5 (apply SepWP.exists_elim; intro _)
  wp_steps
  refine finish_sepWP_lscro (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (fun hcrl_f => hnext _ hcrl_f ⟨by simp only [spqrSendPlacedEntry, arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩) ?_
  exact leaf_arm_post_entails_placed A sp 12#64 _ _ _ 456 _
    (chunkedCt2SampledAt A (sp + 0x590#64) outSt) chunk (.ct2 chunk) (.ct2Sampled outSt) Frame
    (by decide) (by simp only [arm64_norm]; rfl)
    (by dsimp only [spqrSendPayloadSlotAt]; exact Entails.pure_right (by simp only [arm64_norm]) (Entails.refl _))
    rfl (by rw [h1428, hchunk_src, hchunk_dst]; ac_rfl)

/-- Relocatable leaf-call arm 6: `.ekReceivedCt1Sampled s` (`+2460 -> +3068`). -/
theorem step_send_arm_ekReceivedCt1Sampled_placed {F : ShaCompress}
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    (hcall : EkReceivedCt1SampledSendCt1ChunkPlacedOkX A F ext) {s0 s : State} (sp : BitVec 64)
    (st outSt : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsend : st.send_ct1_chunk = .ok (outSt, chunk))
    {ret : BitVec 64} {P Frame Fr : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 2460#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      chunkedStatesAt A (sp + 0x950#64) (.ekReceivedCt1Sampled st) ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 0x1260#64) (528 + chunkSize)) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ct1 chunk } (.ekReceivedCt1Sampled outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (528 + chunkSize) ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1 chunk) ∗
          spqrSendKeySlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A (sp + 0x590#64) (.ekReceivedCt1Sampled outSt)) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (spqrSendPlacedProg ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hcall_at : subroutine_ok ((blkPC_124).rebase (blkPl_124).base (Rust.withPanics ext))
      (lsmpl.base 344) (withLsCodeRoLoaded lsmpl (SpqrV1.ekReceivedCt1SampledSendCt1ChunkPlacedSpec A F)) := hcall
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x950#64) (.ekReceivedCt1Sampled st),
      show (sp + 0x950#64) + 8#64 = sp + 0x958#64 by rw [BitVec.add_assoc]; rfl]
  dsimp only [chunkedStatesWord0, chunkedStatesTail920At]
  obtain ⟨R_ep, h_ep⟩ := expose_epoch_ekReceivedCt1Sampled A sp st; rw [h_ep]
  apply of_sepWP_lscro (mid := lsmpl.base 344) hcrl; wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hcrl_1
  refine call_lscro_calleeStack (x := ({
      outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } : EkReceivedCt1SampledSendCt1ChunkGhost F))
    (s0 := s0) sp (polyNextChunkStack + 960) (by decide)
    (T_pre := memRegion (sp + 0x1260#64) (528 + chunkSize) ∗ chunkedEkReceivedCt1SampledAt A (sp + 0x958#64) st ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
    (T_post := fun _ => chunkedEkReceivedCt1SampledAt A (sp + 0x1260#64) outSt ∗
      chunkAt ((sp + 0x1260#64) + 528#64) chunk ∗ memRegion (sp + 0x958#64) 528 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
    (F := ((sp + 0x950#64) ↦₆₄ 10#64) ∗ memRegion ((sp + 0x958#64) + 528#64) 392 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗ Frame)
    (φ_pre := _) (φ_post := _) hcall_at hcrl_1
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (by simp only [arm64_norm, *]) (ret_pc := (blkPl_124).base + 2480#64) (by simp only [arm64_norm, *])
    (by dsimp only [SpqrV1.ekReceivedCt1SampledSendCt1ChunkPlacedSpec]; ac_rfl) (by simp only [arm64_norm, *])
    (by rw [h_ep]; ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
    (by intro sf; dsimp only [SpqrV1.ekReceivedCt1SampledSendCt1ChunkPlacedSpec]; ac_rfl) ?_
  intro sm hpc_sm hrun_sm hsp_sm htr_sm hcrl_sm hx19_sm hx20_sm _ hx22_sm _ _ hx25_sm hx26_sm _ hx28_sm hvregs_sm
  simp only [arm64_norm, *] at htr_sm hx19_sm hx20_sm hx22_sm hx25_sm hx26_sm hx28_sm hvregs_sm
  apply of_sepWP_lscro (mid := (blkPl_124).base + 3068#64) hcrl_sm; wp_steps
  rw [ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 528) (k := 392) (b' := (sp + 0x590#64) + 528#64) rfl rfl (by decide)]
  refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedEkReceivedCt1SampledAt A outSt)
    (sp + 0x590#64) (sp + 0x1260#64) (s0 := s0) (sp_call := sp)
    (Frame := stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      ((sp + 0x950#64) ↦₆₄ 10#64) ∗ memRegion (sp + 0x958#64) 528 ∗
      memRegion ((sp + 0x958#64) + 528#64) 392 ∗ chunkAt ((sp + 0x1260#64) + 528#64) chunk ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion ((sp + 0x590#64) + 528#64) 392 ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_124).base + 2500#64) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hx19_sf hx20_sf _ hx22_sf _ _ hx25_sf hx26_sf _ hx28_sf hvregs_sf
  simp only [arm64_norm, *] at hx19_sf hx20_sf hx22_sf hx25_sf hx26_sf hx28_sf hvregs_sf
  obtain ⟨cw0, cw1, cw2, cw3, hchunk⟩ := chunkAt_extract_words chunk
  have h1470 : (sp + 0x1260#64) + 528#64 = sp + 0x1470#64 := by rw [BitVec.add_assoc]; rfl
  have hchunk_src := chunkAt_sp_add_eq sp 0x1470#64 0x1478#64 0x1480#64 0x1488#64 0x1490#64 chunk cw0 cw1 cw2 cw3 hchunk
  have hchunk_dst := chunkAt_sp_add_eq sp 0x550#64 0x558#64 0x560#64 0x568#64 0x570#64 chunk cw0 cw1 cw2 cw3 hchunk
  rw [h1470, hchunk_src, memRegion_38_eq_chunk_slot sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; iterate 5 (apply SepWP.exists_elim; intro _)
  wp_steps
  refine finish_sepWP_lscro (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (fun hcrl_f => hnext _ hcrl_f ⟨by simp only [spqrSendPlacedEntry, arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, chunkedStatesWord0, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *]⟩) ?_
  exact leaf_arm_post_entails_placed A sp 10#64 _ _ _ 528 _
    (chunkedEkReceivedCt1SampledAt A (sp + 0x590#64) outSt) chunk (.ct1 chunk)
    (.ekReceivedCt1Sampled outSt) Frame (by decide) (by simp only [arm64_norm]; rfl)
    (by dsimp only [spqrSendPayloadSlotAt]; exact Entails.pure_right (by simp only [arm64_norm]) (Entails.refl _))
    rfl (by rw [h1470, hchunk_src, hchunk_dst]; ac_rfl)

end CryptoVerification.SpqrV1.Top.Send
