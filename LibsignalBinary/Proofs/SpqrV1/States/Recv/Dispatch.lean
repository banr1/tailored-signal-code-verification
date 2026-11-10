/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv`: Prologue, Jump-Table Dispatch, and Shared Epilogues

Verifies the `4,240`-byte frame prologue (`+0 -> +36`), `.rodata` jump-table dispatch (`+36 -> arm`),
5 tail-call dealloc/drop epilogues, direct epilogue (`+19324`), and shared `Ok(V1Recv)` store epilogue (`+18940..+19324`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv")
  (ls_stub% "memcpy")

@[local arm64_norm, local wp_norm]
theorem sp_sub_4240_add_4144 (sp : BitVec 64) : (sp - 4240#64) + 4144#64 = sp - 96#64 := by bv_omega

attribute [local arm64_norm, local wp_norm]
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48

theorem seq_clean {prog : Program} {mid target_pc : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target_pc sm P_mid post) :
    SepWP prog target_pc s P post :=
  SepWP.seq h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hQ)

theorem align_pre {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {Q : State → Prop}
    (h : P ⊢ P')
    (hwp : SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ P') ∧ Q sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨h1, h2⟩ => ⟨Entails.trans h1 h, h2⟩

theorem sepWPp_seq_clean {prog : Program} {mid target_pc : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_mid : State → Prop} {Q Q_panic : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → Q_mid sm →
      SepWPp prog target_pc sm P_mid Q Q_panic) :
    SepWPp prog target_pc s P Q Q_panic :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm Pm hpcm hrunm ⟨hPm, hQm⟩ =>
    SepWPp.weaken_pre hPm (h2 sm hpcm hrunm hQm))

/-! ## Callee Stack Bounds (`statesRecvStackX ≥ statesRecvFrame + calleeStack`) & Stack Splits -/

theorem statesRecvStackX_ge_allocHookStack :
    statesRecvFrame + allocHookStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_extHookStack :
    statesRecvFrame + extHookStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_dropStackPoly64 :
    statesRecvFrame + dropStackPoly64 ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_dropGluePoly16Stack :
    statesRecvFrame + dropGluePoly16Stack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_dropStack32 :
    statesRecvFrame + dropStack32 ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_dropStack48 :
    statesRecvFrame + dropStack48 ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_dropStack80 :
    statesRecvFrame + dropStack80 ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_noHeaderReceivedRecvHdrChunkStackX :
    statesRecvFrame + noHeaderReceivedRecvHdrChunkStackX ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_keysSampledRecvCt1ChunkStack :
    statesRecvFrame + keysSampledRecvCt1ChunkStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_headerSentRecvCt1ChunkStack :
    statesRecvFrame + headerSentRecvCt1ChunkStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_ct1ReceivedRecvCt2ChunkStack :
    statesRecvFrame + ct1ReceivedRecvCt2ChunkStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_ct1AcknowledgedRecvEkChunkStack :
    statesRecvFrame + ct1AcknowledgedRecvEkChunkStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_ekReceivedCt1SampledRecvCt1AckStack :
    statesRecvFrame + ekReceivedCt1SampledRecvCt1AckStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_recvCt2ChunkStackX :
    statesRecvFrame + RecvCt2Chunk.recvCt2ChunkStackX ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_addChunkStackX :
    statesRecvFrame + SpqrV1.Poly.AddChunk.addChunkStackX ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_polyDecodedMessageStackX :
    statesRecvFrame + RecvCt2Chunk.polyDecodedMessageStackX ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_polyDecoderDecodedMessageStack :
    statesRecvFrame + polyDecoderDecodedMessageStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_unchunkedRecvEkStack :
    statesRecvFrame + unchunkedRecvEkStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_unchunkedSendCt2Stack :
    statesRecvFrame + unchunkedSendCt2Stack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_sendCt2EncoderStack :
    statesRecvFrame + sendCt2EncoderStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_encodeBytesStackX :
    statesRecvFrame + SpqrV1.Poly.EncodeBytes.encodeBytesStackX ≤ statesRecvStackX := by decide

theorem stackAt_statesRecvCallee_eq_allocHook (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15456 ∗ stackAt fsp allocHookStack :=
  stackAt_split_bottom fsp allocHookStack 15456 (by decide)

theorem stackAt_statesRecvCallee_eq_extHook (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 3168 ∗ stackAt fsp extHookStack :=
  stackAt_split_bottom fsp extHookStack 3168 (by decide)

theorem stackAt_statesRecvCallee_eq_dropStack32 (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15424 ∗ stackAt fsp dropStack32 :=
  stackAt_split_bottom fsp dropStack32 15424 (by decide)

theorem stackAt_statesRecvCallee_eq_dropStack48 (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15408 ∗ stackAt fsp dropStack48 :=
  stackAt_split_bottom fsp dropStack48 15408 (by decide)

theorem stackAt_statesRecvCallee_eq_dropStackPoly64 (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15392 ∗ stackAt fsp dropStackPoly64 :=
  stackAt_split_bottom fsp dropStackPoly64 15392 (by decide)

theorem stackAt_statesRecvCallee_eq_noHeaderReceivedRecvHdrChunk (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 848 ∗ stackAt fsp noHeaderReceivedRecvHdrChunkStackX :=
  stackAt_split_bottom fsp noHeaderReceivedRecvHdrChunkStackX 848 (by decide)

theorem stackAt_statesRecvCallee_eq_keysSampledRecvCt1Chunk (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 1632 ∗ stackAt fsp keysSampledRecvCt1ChunkStack :=
  stackAt_split_bottom fsp keysSampledRecvCt1ChunkStack 1632 (by decide)

theorem stackAt_statesRecvCallee_eq_headerSentRecvCt1Chunk (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 928 ∗ stackAt fsp headerSentRecvCt1ChunkStack :=
  stackAt_split_bottom fsp headerSentRecvCt1ChunkStack 928 (by decide)

theorem stackAt_statesRecvCallee_eq_ct1ReceivedRecvCt2Chunk (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2576 ∗ stackAt fsp ct1ReceivedRecvCt2ChunkStack :=
  stackAt_split_bottom fsp ct1ReceivedRecvCt2ChunkStack 2576 (by decide)

theorem stackAt_statesRecvCallee_eq_ct1AcknowledgedRecvEkChunk (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 336 ∗ stackAt fsp ct1AcknowledgedRecvEkChunkStack :=
  stackAt_split_bottom fsp ct1AcknowledgedRecvEkChunkStack 336 (by decide)

theorem stackAt_statesRecvCallee_eq_ekReceivedCt1SampledRecvCt1Ack (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 1920 ∗ stackAt fsp ekReceivedCt1SampledRecvCt1AckStack :=
  stackAt_split_bottom fsp ekReceivedCt1SampledRecvCt1AckStack 1920 (by decide)

theorem stackAt_statesRecvCallee_eq_addChunk (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 3072 ∗ stackAt fsp SpqrV1.Poly.AddChunk.addChunkStackX :=
  stackAt_split_bottom fsp SpqrV1.Poly.AddChunk.addChunkStackX 3072 (by decide)

theorem stackAt_statesRecvCallee_eq_polyDecodedMessage (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2496 ∗ stackAt fsp RecvCt2Chunk.polyDecodedMessageStackX :=
  stackAt_split_bottom fsp RecvCt2Chunk.polyDecodedMessageStackX 2496 (by decide)

theorem stackAt_statesRecvCallee_eq_unchunkedRecvEk (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2960 ∗ stackAt fsp unchunkedRecvEkStack :=
  stackAt_split_bottom fsp unchunkedRecvEkStack 2960 (by decide)

theorem stackAt_statesRecvCallee_eq_unchunkedSendCt2 (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2832 ∗ stackAt fsp unchunkedSendCt2Stack :=
  stackAt_split_bottom fsp unchunkedSendCt2Stack 2832 (by decide)

theorem stackAt_statesRecvCallee_eq_sendCt2Encoder (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2096 ∗ stackAt fsp sendCt2EncoderStack :=
  stackAt_split_bottom fsp sendCt2EncoderStack 2096 (by decide)

theorem stackAt_statesRecvCallee_eq_encodeBytes (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2608 ∗ stackAt fsp SpqrV1.Poly.EncodeBytes.encodeBytesStackX :=
  stackAt_split_bottom fsp SpqrV1.Poly.EncodeBytes.encodeBytesStackX 2608 (by decide)

/-! ## Prologue (`+0 -> +36`, `0x55454 -> 0x55478`) -/

/-- Prologue of `States::recv` (`+0 -> +36`, `0x55454 -> 0x55478`):
    splits `stackAt s0.sp statesRecvStackX` into callee stack `stackAt (s0.sp - 4240#64) statesRecvCalleeStackX`,
    local frame `memRegion (s0.sp - 4240#64) 4144` (with `[s0.sp - 4192#64] ↦₆₄ 0#64`),
    and `statesRecvSavedCells s0`. -/
theorem states_recv_prologue
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc0 : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName)
    (hrun0 : s0.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 36#64)
      s0
      (stackAt s0.sp statesRecvStackX ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 ∗
          Rest) ∧
        s1.sp = s0.sp - 4240#64 ∧
        s1.readReg64 .x0 = s0.readReg64 .x0 ∧
        s1.readReg64 .x1 = s0.readReg64 .x1 ∧
        s1.readReg64 .x2 = s0.readReg64 .x2 ∧
        s1.readReg64 .x3 = s0.readReg64 .x3 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        TraceCalleeSaved s1 s0) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hsp4192_align : ((s0.sp - 4192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4192#64 hsp0_align (by decide)
  states_recv_fetches_range b (Rust.withPanics ext) 0 36
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc0 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  rw [stackAt_statesRecv_split_96 s0.sp, stackAt_statesRecv_split_fsp s0.sp]
  nth_rw 1 [memRegion_4144_split_cell48 (s0.sp - 4240#64)]
  cells_unfold
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sp_sub_4240_add_48]
  apply ProofLib.SepWP.exists_left; intro v48
  apply ProofLib.SepWP.exists_left; intro v_fp
  apply ProofLib.SepWP.exists_left; intro v_lr
  apply ProofLib.SepWP.exists_left; intro v_x28
  apply ProofLib.SepWP.exists_left; intro v_x27
  apply ProofLib.SepWP.exists_left; intro v_x26
  apply ProofLib.SepWP.exists_left; intro v_x25
  apply ProofLib.SepWP.exists_left; intro v_x24
  apply ProofLib.SepWP.exists_left; intro v_x23
  apply ProofLib.SepWP.exists_left; intro v_x22
  apply ProofLib.SepWP.exists_left; intro v_x21
  apply ProofLib.SepWP.exists_left; intro v_x20
  apply ProofLib.SepWP.exists_left; intro v_x19
  wp_steps
  have hjoin4144 := cell48_4088_entails_memRegion_4144 (s0.sp - 4240#64) 0#64
  rw [sp_sub_4240_add_48] at hjoin4144
  have h4184 : (s0.sp - 4240#64) + 56#64 = s0.sp - 4184#64 := by bv_omega
  rw [h4184] at hjoin4144 ⊢
  refine SepWP.focus_weaken hjoin4144 (by sep_focus) ?_
  refine align_pre ?_ ?_
  · simp only [statesRecvSavedCells, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
      Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
    exact Entails.of_eq (by ac_rfl)
  · wp_done

/-- Extended (`+ extHookStack = + 16384`B) prologue of `States::recv` (`+0 -> +36`, `0x55454 -> 0x55478`). -/
theorem states_recv_prologue_ext
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc0 : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName)
    (hrun0 : s0.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 36#64)
      s0
      (stackAt s0.sp statesRecvStackXExt ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
          memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 ∗
          Rest) ∧
        s1.sp = s0.sp - 4240#64 ∧
        s1.readReg64 .x0 = s0.readReg64 .x0 ∧
        s1.readReg64 .x1 = s0.readReg64 .x1 ∧
        s1.readReg64 .x2 = s0.readReg64 .x2 ∧
        s1.readReg64 .x3 = s0.readReg64 .x3 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        TraceCalleeSaved s1 s0) := by
  rw [stackAt_statesRecvStackXExt_eq_X s0.sp]
  refine SepWP.weaken_pre
    (Entails.of_eq (show (memRegion (s0.sp - 40176#64) 16384 ∗ stackAt s0.sp statesRecvStackX) ∗ Rest =
      stackAt s0.sp statesRecvStackX ∗ (memRegion (s0.sp - 40176#64) 16384 ∗ Rest) by ac_rfl))
    (SepWP.mono
      (states_recv_prologue s0 (memRegion (s0.sp - 40176#64) 16384 ∗ Rest) hsp0_align hpc0 hrun0)
      fun s1 P1 _ _ ⟨hP1, hrest⟩ => ⟨?_, hrest⟩)
  rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]
  exact Entails.trans hP1 (Entails.of_eq (by ac_rfl))

/-! ## Shared Direct Epilogue (`+19324 -> s0.x30`) and Tail-Call Epilogues -/

/-- Shared direct epilogue at `+19324` (`0x59fd0 -> 0x59ff0`):
    restores `sp = s0.sp` and `x19..x30` from `statesRecvSavedCells s0`, folds the stack back into
    `stackAt s0.sp statesRecvStackX`, and returns to `s0.readReg64 .x30`. -/
theorem states_recv_epilogue_19324
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19324#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  states_recv_fetches_range b (Rust.withPanics ext) 19324 36
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  unfold statesRecvSavedCells
  wp_steps
  refine align_pre ?_ ?_
  · have hrest := stack_restore_statesRecv s0
    unfold statesRecvSavedCells at hrest
    refine Entails.trans
      (Entails.of_eq (show _ =
        Rest ∗
        (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
         memRegion (s0.sp - 4240#64) 4144 ∗
         (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) by ac_rfl))
      (sepConj_mono_right hrest)
  · wp_done

theorem stackAt_statesRecvStackX_eq_allocHook (sp : BitVec 64) :
    stackAt sp statesRecvStackX =
      memRegion (sp - 23792#64) 19696 ∗ stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack 19696 (by decide)

theorem stackAt_statesRecvStackX_eq_dropStack32 (sp : BitVec 64) :
    stackAt sp statesRecvStackX =
      memRegion (sp - 23792#64) 19664 ∗ stackAt sp dropStack32 :=
  stackAt_split_bottom sp dropStack32 19664 (by decide)

theorem stackAt_statesRecvStackX_eq_dropStackPoly64 (sp : BitVec 64) :
    stackAt sp statesRecvStackX =
      memRegion (sp - 23792#64) 19632 ∗ stackAt sp dropStackPoly64 :=
  stackAt_split_bottom sp dropStackPoly64 19632 (by decide)

theorem stackAt_statesRecvStackX_eq_dropGluePoly16 (sp : BitVec 64) :
    stackAt sp statesRecvStackX =
      memRegion (sp - 23792#64) 19664 ∗ stackAt sp dropGluePoly16Stack :=
  stackAt_split_bottom sp dropGluePoly16Stack 19664 (by decide)

/-- Tail-call epilogue at `+192` (`0x55514..0x55534 -> b 0x78a28`):
    restores `sp = s0.sp` and `x19..x30`, tail-calls `__rust_dealloc(ptr, cap, 1)`,
    and returns to `s0.readReg64 .x30`. -/
theorem states_recv_tail_dealloc_192
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (ptr cap : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 192#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = ptr)
    (hx1_1 : s1.readReg64 .x1 = cap)
    (hx2_1 : s1.readReg64 .x2 = 1#64)
    (hcap : cap.toNat ≠ 0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        A.live ptr cap.toNat 1 ∗
        memRegion ptr cap.toNat ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ A.pool ∗ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hdealloc := hA.dealloc_ok_at statesRecvName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "__rustc::__rust_dealloc"))
  simp only [rustDeallocSpec, allocHookStack] at hdealloc
  states_recv_fetches_range b (Rust.withPanics ext) 192 36
  dsimp only [contractProg, tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc1 hdealloc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  unfold statesRecvSavedCells
  wp_steps
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.focus_weaken hrest (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_allocHook s0.sp)) (by sep_focus) ?_
  wp_call hdealloc (ptr, cap.toNat, 1)
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_allocHook s0.sp).symm) (by sep_focus) ?_
  refine align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

/-- Tail-call epilogue at `+552` (`0x5567c..0x5569c -> b 0x4c92c`):
    restores `sp = s0.sp` and `x19..x30`, tail-calls `drop_glue::<EkSentCt1Received>`,
    and returns to `s0.readReg64 .x30`. -/
theorem states_recv_tail_drop_ekSentCt1Received_552
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (a : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 552#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = a)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        chunkedEkSentCt1ReceivedAt A a st ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ memRegion a chunkedEkSentCt1ReceivedSize ∗ A.pool ∗ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hdrop : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18446744073709515992#64)
      (dropChunkedEkSentCt1ReceivedSpec A F) := by
    have hrel : (tripleRatchetProgAtExt b ext).fnAddr statesRecvName =
        (tripleRatchetProgAtExt b ext).fnAddr dropChunkedEkSentCt1ReceivedName + BitVec.ofNat 64 35624 :=
      Program.fnAddr_rel (k := 35624) (b := b) (X := Rust.withPanics ext)
        CryptoVerification.libsignalSessionCode_fnOff_0x47534
        CryptoVerification.libsignalSessionCode_fnOff_0x5005c (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_chunked_ek_sent_ct1_received_ok_ext hA.dealloc)
    rw [hrel, BitVec.add_assoc]; simp
  simp only [dropChunkedEkSentCt1ReceivedSpec] at hdrop
  states_recv_fetches_range b (Rust.withPanics ext) 552 36
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc1 hdrop ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  unfold statesRecvSavedCells
  wp_steps
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.focus_weaken hrest (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropStack32 s0.sp)) (by sep_focus) ?_
  wp_call hdrop ⟨a, st⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropStack32 s0.sp).symm) (by sep_focus) ?_
  refine align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

/-- Tail-call epilogue at `+1168` (`0x558e4..0x55904 -> b 0x4c858`):
    restores `sp = s0.sp` and `x19..x30`, tail-calls `drop_glue::<HeaderSent>`,
    and returns to `s0.readReg64 .x30`. -/
theorem states_recv_tail_drop_headerSent_1168
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (a : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1168#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = a)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        chunkedHeaderSentAt A a st ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ memRegion a chunkedHeaderSentSize ∗ A.pool ∗ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hdrop : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18446744073709515780#64)
      (dropChunkedHeaderSentSpec A F) := by
    have hrel : (tripleRatchetProgAtExt b ext).fnAddr statesRecvName =
        (tripleRatchetProgAtExt b ext).fnAddr dropChunkedHeaderSentName + BitVec.ofNat 64 35836 :=
      Program.fnAddr_rel (k := 35836) (b := b) (X := Rust.withPanics ext)
        CryptoVerification.libsignalSessionCode_fnOff_0x47460
        CryptoVerification.libsignalSessionCode_fnOff_0x5005c (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_chunked_header_sent_ok_ext hA.dealloc)
    rw [hrel, BitVec.add_assoc]; simp
  simp only [dropChunkedHeaderSentSpec] at hdrop
  states_recv_fetches_range b (Rust.withPanics ext) 1168 36
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc1 hdrop ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  unfold statesRecvSavedCells
  wp_steps
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.focus_weaken hrest (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropStackPoly64 s0.sp)) (by sep_focus) ?_
  wp_call hdrop ⟨a, st⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropStackPoly64 s0.sp).symm) (by sep_focus) ?_
  refine align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

/-- Tail-call epilogue at `+1760` (`0x55b34..0x55b54 -> b 0x4bd18`):
    restores `sp = s0.sp` and `x19..x30`, tail-calls `drop_glue::<[SortedSet<Pt>; 16]>`,
    and returns to `s0.readReg64 .x30`. -/
theorem states_recv_tail_drop_sortedSetPt16_1760
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (arrA : BitVec 64) (vecs : List (List Pt))
    (hvecs : vecs.length = NUM_POLYS)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1760#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = arrA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        vecPtListOf A arrA vecs ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ memRegion arrA polyArrayBytes ∗ A.pool ∗ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hdrop : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18446744073709512900#64)
      (dropGlueSortedSetPt16Spec A) := by
    have hrel : (tripleRatchetProgAtExt b ext).fnAddr statesRecvName =
        (tripleRatchetProgAtExt b ext).fnAddr dropSortedSetPt16Name + BitVec.ofNat 64 38716 :=
      Program.fnAddr_rel (k := 38716) (b := b) (X := Rust.withPanics ext)
        CryptoVerification.libsignalSessionCode_fnOff_0x46920
        CryptoVerification.libsignalSessionCode_fnOff_0x5005c (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_sorted_set_pt16_ok_ext hA.dealloc)
    rw [hrel, BitVec.add_assoc]; simp
  simp only [dropGlueSortedSetPt16Spec] at hdrop
  states_recv_fetches_range b (Rust.withPanics ext) 1760 36
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc1 hdrop ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  unfold statesRecvSavedCells
  wp_steps
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.focus_weaken hrest (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropGluePoly16 s0.sp)) (by sep_focus) ?_
  wp_call hdrop ⟨arrA, vecs⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropGluePoly16 s0.sp).symm) (by sep_focus) ?_
  refine align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

/-- Tail-call epilogue at `+10952` (`0x57f1c..0x57f3c -> b 0x4c78c`):
    restores `sp = s0.sp` and `x19..x30`, tail-calls `drop_glue::<Ct2Sampled>`,
    and returns to `s0.readReg64 .x30`. -/
theorem states_recv_tail_drop_ct2Sampled_10952
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (a : BitVec 64)
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 10952#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = a)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        chunkedCt2SampledAt A a st ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ memRegion a chunkedCt2SampledSize ∗ A.pool ∗ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hdrop : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18446744073709515576#64)
      (dropChunkedCt2SampledSpec A F) := by
    have hrel : (tripleRatchetProgAtExt b ext).fnAddr statesRecvName =
        (tripleRatchetProgAtExt b ext).fnAddr dropChunkedCt2SampledName + BitVec.ofNat 64 36040 :=
      Program.fnAddr_rel (k := 36040) (b := b) (X := Rust.withPanics ext)
        CryptoVerification.libsignalSessionCode_fnOff_0x47394
        CryptoVerification.libsignalSessionCode_fnOff_0x5005c (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_chunked_ct2_sampled_ok_ext hA.dealloc)
    rw [hrel, BitVec.add_assoc]; simp
  simp only [dropChunkedCt2SampledSpec] at hdrop
  states_recv_fetches_range b (Rust.withPanics ext) 10952 36
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc1 hdrop ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  unfold statesRecvSavedCells
  wp_steps
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.focus_weaken hrest (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropStack32 s0.sp)) (by sep_focus) ?_
  wp_call hdrop ⟨a, st⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropStack32 s0.sp).symm) (by sep_focus) ?_
  refine align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

/-! ## Jump-Table Dispatch (`+36 -> arm_entry`, `0x55478 -> 0x554b0`) -/

/-- Jump-table target offset from `entry` for each `States` discriminant `tag`. -/
def statesRecvArmOffset (tag : BitVec 64) : BitVec 64 :=
  if tag == 2#64 then 96#64         -- idx 0 -> 0x554b4 (+96)
  else if tag == 3#64 then 1796#64  -- idx 1 -> 0x55b58 (+1796)
  else if tag == 4#64 then 780#64   -- idx 2 -> 0x55760 (+780)
  else if tag == 5#64 then 1204#64  -- idx 3 -> 0x55908 (+1204)
  else if tag == 6#64 then 228#64   -- idx 4 -> 0x55538 (+228)
  else if tag == 7#64 then 2132#64  -- idx 5 -> 0x55ca8 (+2132)
  else if tag == 8#64 then 2268#64  -- idx 6 -> 0x55d30 (+2268)
  else if tag == 10#64 then 3392#64 -- idx 8 -> 0x56194 (+3392)
  else if tag == 11#64 then 588#64  -- idx 9 -> 0x556a0 (+588)
  else if tag == 12#64 then 2396#64 -- idx 10 -> 0x55db0 (+2396)
  else 1528#64                      -- idx 7 (tag ∈ {0, 1, 9}) -> 0x55a4c (+1528)

/-- Jump-table index `x8` computed by `sub x8, x12, #2; cmp x12, #1; csel x8, x8, x9, hi` (`x9 = 7`). -/
def statesRecvJumpIdx (tag : BitVec 64) : BitVec 64 :=
  if tag == 2#64 then 0#64
  else if tag == 3#64 then 1#64
  else if tag == 4#64 then 2#64
  else if tag == 5#64 then 3#64
  else if tag == 6#64 then 4#64
  else if tag == 7#64 then 5#64
  else if tag == 8#64 then 6#64
  else if tag == 10#64 then 8#64
  else if tag == 11#64 then 9#64
  else if tag == 12#64 then 10#64
  else 7#64

/-- Valid `States` discriminant predicate (`tag ∈ {0..12}`). -/
def ValidStatesTag (tag : BitVec 64) : Prop :=
  tag = 0#64 ∨ tag = 1#64 ∨ tag = 2#64 ∨ tag = 3#64 ∨ tag = 4#64 ∨ tag = 5#64 ∨
  tag = 6#64 ∨ tag = 7#64 ∨ tag = 8#64 ∨ tag = 9#64 ∨ tag = 10#64 ∨ tag = 11#64 ∨ tag = 12#64

set_option maxHeartbeats 1200000 in
/-- Jump-table dispatch (`+36 -> +statesRecvArmOffset tag`, `0x55478 -> 0x554b0 -> arm_entry`):
    given `st_ptr ↦₆₄ tag` with `ValidStatesTag tag` and `statesRecvRoAt b`,
    steps to `entry + statesRecvArmOffset tag` while setting:
    - `x12 = tag`, `x8 = statesRecvJumpIdx tag`
    - `x19 = s1.x0` (`out`)
    - `x21 = fsp + 3856#64` (`#0xf10`)
    - `x24 = s1.x2` (`msg_ptr`)
    - `x28 = fsp + 3272#64` (`#0xcc8`)
    and preserving `sp = fsp`, `x0`, `x1`, `x2`, `x3`, `x29`, `trace`. -/
theorem states_recv_dispatch
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (s1 : State) (fsp st_ptr tag : BitVec 64) (Rest : SepProp)
    (htag : ValidStatesTag tag)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx1_1 : s1.readReg64 .x1 = st_ptr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + statesRecvArmOffset tag)
      s1
      ((st_ptr ↦₆₄ tag) ∗ statesRecvRoAt b ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ (st_ptr ↦₆₄ tag) ∗ statesRecvRoAt b ∗ Rest) ∧
        s2.sp = fsp ∧
        s2.readReg64 .x0 = s1.readReg64 .x0 ∧
        s2.readReg64 .x1 = st_ptr ∧
        s2.readReg64 .x2 = s1.readReg64 .x2 ∧
        s2.readReg64 .x3 = s1.readReg64 .x3 ∧
        s2.readReg64 .x8 = statesRecvJumpIdx tag ∧
        s2.readReg64 .x12 = tag ∧
        s2.readReg64 .x19 = s1.readReg64 .x0 ∧
        s2.readReg64 .x21 = fsp + 3856#64 ∧
        s2.readReg64 .x24 = s1.readReg64 .x2 ∧
        s2.readReg64 .x28 = fsp + 3272#64 ∧
        s2.readReg64 .x29 = s1.readReg64 .x29 ∧
        TraceCalleeSaved s2 s1) := by
  subst hsp1 hx1_1
  have hadrp := fnAddr_adrp_5549c (b := b) (H := Rust.withPanics ext) hb
  states_recv_fetches_range b (Rust.withPanics ext) 36 60
  dsimp only [tripleRatchetProgAtExt, statesRecvName, statesRecvRoAt,
    statesRecvJumpTableAt, BitVec.ofNat_eq_ofNat] at hpc1 hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  rcases htag with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · dsimp only [statesRecvArmOffset, statesRecvJumpIdx]
    wp_steps
    wp_done

/-! ## Shared `Ok(V1Recv)` Store Epilogue (`+18940 / +18996 -> +19324`, `0x59e50 / 0x59e88 -> 0x59fd0`) -/

@[local arm64_norm, local wp_norm]
theorem out_488_add_8 (out : BitVec 64) : out + 488#64 + 8#64 = out + 496#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_888_add_8 (out : BitVec 64) : out + 888#64 + 8#64 = out + 896#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_888_add_16 (out : BitVec 64) : out + 888#64 + 16#64 = out + 904#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_904_add_8 (out : BitVec 64) : out + 904#64 + 8#64 = out + 912#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem bv376_toNat : (376#64 : BitVec 64).toNat = 376 := rfl

theorem epilogue_step_18940_18996
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64)
    (w8 w56 w64 w96 w128 w136 w152 w160 w168 w176 w184 w192 w216 u368 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18940#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64)
      s
      (((fsp + 8#64) ↦₆₄ w8) ∗
       ((fsp + 56#64) ↦₆₄ w56) ∗ ((fsp + 64#64) ↦₆₄ w64) ∗
       ((fsp + 96#64) ↦₆₄ w96) ∗
       ((fsp + 128#64) ↦₆₄ w128) ∗ ((fsp + 136#64) ↦₆₄ w136) ∗
       ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 160#64) ↦₆₄ w160) ∗
       ((fsp + 168#64) ↦₆₄ w168) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗
       ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 192#64) ↦₆₄ w192) ∗
       ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 368#64) ↦₆₄ u368) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 8#64) ↦₆₄ w8) ∗
          ((fsp + 56#64) ↦₆₄ w56) ∗ ((fsp + 64#64) ↦₆₄ w64) ∗
          ((fsp + 96#64) ↦₆₄ w96) ∗
          ((fsp + 128#64) ↦₆₄ w128) ∗ ((fsp + 136#64) ↦₆₄ w136) ∗
          ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 160#64) ↦₆₄ w160) ∗
          ((fsp + 168#64) ↦₆₄ w168) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗
          ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 192#64) ↦₆₄ w192) ∗
          ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 368#64) ↦₆₄ s.readReg64 .x0) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = s.readReg64 .x11 ∧
        sm.readReg64 .x1 = w136 ∧
        sm.readReg64 .x2 = s.readReg64 .x2 ∧
        sm.readReg64 .x3 = s.readReg64 .x3 ∧
        sm.readReg64 .x4 = w184 ∧
        sm.readReg64 .x5 = w216 ∧
        sm.readReg64 .x6 = w56 ∧
        sm.readReg64 .x7 = w64 ∧
        sm.readReg64 .x8 = s.readReg64 .x14 ∧
        sm.readReg64 .x9 = w192 ∧
        sm.readReg64 .x10 = s.readReg64 .x10 ∧
        sm.readReg64 .x11 = s.readReg64 .x20 ∧
        sm.readReg64 .x12 = s.readReg64 .x12 ∧
        sm.readReg64 .x13 = w8 ∧
        sm.readReg64 .x14 = s.readReg64 .x17 ∧
        sm.readReg64 .x15 = s.readReg64 .x15 ∧
        sm.readReg64 .x16 = w96 ∧
        sm.readReg64 .x17 = s.readReg64 .x27 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x22 = w176 ∧
        sm.readReg64 .x23 = w152 ∧
        sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = w168 ∧
        sm.readReg64 .x27 = w160 ∧
        sm.readReg64 .x28 = w128 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = s.readReg64 .x30 ∧
        TraceCalleeSaved sm s) := by
  subst hsp
  states_recv_fetches_range b (Rust.withPanics ext) 18940 56
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- `out` cells written in Step A (`+18996 -> +19128`, 33 instructions). -/
def epilogueRecvOutPartA (out : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 : BitVec 64)
    (w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w392 w400 w424 w432 : BitVec 64) : SepProp :=
  (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w8) ∗ ((out + 16#64) ↦₆₄ w16) ∗ ((out + 24#64) ↦₆₄ w24) ∗
  ((out + 32#64) ↦₆₄ w32) ∗ ((out + 40#64) ↦₆₄ w40) ∗ ((out + 48#64) ↦₆₄ w48) ∗ ((out + 56#64) ↦₆₄ w56) ∗
  ((out + 64#64) ↦₆₄ w64) ∗ ((out + 72#64) ↦₆₄ w72) ∗ ((out + 80#64) ↦₆₄ w80) ∗ ((out + 88#64) ↦₆₄ w88) ∗
  ((out + 96#64) ↦₆₄ w96) ∗ ((out + 104#64) ↦₆₄ w104) ∗ ((out + 112#64) ↦₆₄ w112) ∗
  ((out + 264#64) ↦₆₄ w264) ∗ ((out + 272#64) ↦₆₄ w272) ∗ ((out + 280#64) ↦₆₄ w280) ∗ ((out + 288#64) ↦₆₄ w288) ∗
  ((out + 296#64) ↦₆₄ w296) ∗ ((out + 304#64) ↦₆₄ w304) ∗ ((out + 312#64) ↦₆₄ w312) ∗ ((out + 320#64) ↦₆₄ w320) ∗
  ((out + 328#64) ↦₆₄ w328) ∗ ((out + 336#64) ↦₆₄ w336) ∗ ((out + 344#64) ↦₆₄ w344) ∗ ((out + 352#64) ↦₆₄ w352) ∗
  ((out + 392#64) ↦₆₄ w392) ∗ ((out + 400#64) ↦₆₄ w400) ∗ ((out + 424#64) ↦₆₄ w424) ∗ ((out + 432#64) ↦₆₄ w432)

/-- Stack cells read in Step A (`+18996 -> +19128`). -/
def epilogueRecvStackPartA (fsp : BitVec 64)
    (w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 : BitVec 64)
    (q960 : BitVec 128) : SepProp :=
  ((fsp + 224#64) ↦₆₄ w224) ∗
  ((fsp + 288#64) ↦₆₄ w288) ∗ ((fsp + 296#64) ↦₆₄ w296) ∗
  ((fsp + 336#64) ↦₆₄ w336) ∗ ((fsp + 352#64) ↦₆₄ w352) ∗
  ((fsp + 368#64) ↦₆₄ w368) ∗ ((fsp + 376#64) ↦₆₄ w376) ∗ ((fsp + 384#64) ↦₆₄ w384) ∗
  ((fsp + 408#64) ↦₆₄ w408) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗ ((fsp + 456#64) ↦₆₄ w456) ∗
  ((fsp + 496#64) ↦₆₄ w496) ∗ ((fsp + 504#64) ↦₆₄ w504) ∗
  ((fsp + 960#64) ↦₁₂₈ q960)

set_option maxHeartbeats 1200000 in
theorem epilogue_step_18996_19128
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 : BitVec 64)
    (u264 u272 u280 u288 u296 u304 u312 u320 u328 u336 u344 u352 u392 u400 u424 u432 : BitVec 64)
    (w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 : BitVec 64)
    (q960 : BitVec 128)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19128#64)
      s
      (epilogueRecvOutPartA out u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112
         u264 u272 u280 u288 u296 u304 u312 u320 u328 u336 u344 u352 u392 u400 u424 u432 ∗
       epilogueRecvStackPartA fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 q960 ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          epilogueRecvOutPartA out
            w224 (s.readReg64 .x1) (s.readReg64 .x8) w496
            w456 w376 w368 w504
            w288 w432 w408 w352
            w384 w336 w296
            (s.readReg64 .x25) (s.readReg64 .x12) (s.readReg64 .x11) (s.readReg64 .x10)
            (s.readReg64 .x15) (s.readReg64 .x28) (s.readReg64 .x7) (s.readReg64 .x0)
            (s.readReg64 .x6) (s.readReg64 .x30) (s.readReg64 .x21) (s.readReg64 .x9)
            (s.readReg64 .x5) (s.readReg64 .x4) (s.readReg64 .x13) (s.readReg64 .x14) ∗
          epilogueRecvStackPartA fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 q960 ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out + 512#64 ∧
        sm.readReg64 .x1 = fsp + 576#64 ∧
        sm.readReg64 .x2 = s.readReg64 .x2 ∧
        sm.readReg64 .x3 = s.readReg64 .x3 ∧
        sm.readReg64 .x16 = s.readReg64 .x16 ∧
        sm.readReg64 .x17 = s.readReg64 .x17 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x23 = s.readReg64 .x23 ∧
        sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readVReg128 0#5 = q960 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx19
  states_recv_fetches_range b (Rust.withPanics ext) 18996 132
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_simp_pre [epilogueRecvOutPartA, epilogueRecvStackPartA, pointsTo128, sepConj_assoc]
  wp_steps
  simp only [epilogueRecvOutPartA, epilogueRecvStackPartA, pointsTo128, sepConj_assoc]
  wp_done

/-- `out` cells written in Step B (`+19128 -> +19280`, 38 instructions). -/
def epilogueRecvOutPartB (out : BitVec 64)
    (w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 : BitVec 64)
    (w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480 : BitVec 64)
    (q488 : BitVec 128) (w504 : BitVec 64) : SepProp :=
  ((out + 120#64) ↦₆₄ w120) ∗ ((out + 128#64) ↦₆₄ w128) ∗ ((out + 136#64) ↦₆₄ w136) ∗ ((out + 144#64) ↦₆₄ w144) ∗
  ((out + 152#64) ↦₆₄ w152) ∗ ((out + 160#64) ↦₆₄ w160) ∗ ((out + 168#64) ↦₆₄ w168) ∗ ((out + 176#64) ↦₆₄ w176) ∗
  ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗ ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
  ((out + 216#64) ↦₆₄ w216) ∗ ((out + 224#64) ↦₆₄ w224) ∗ ((out + 232#64) ↦₆₄ w232) ∗ ((out + 240#64) ↦₆₄ w240) ∗
  ((out + 248#64) ↦₆₄ w248) ∗ ((out + 256#64) ↦₆₄ w256) ∗
  ((out + 360#64) ↦₆₄ w360) ∗ ((out + 368#64) ↦₆₄ w368) ∗ ((out + 376#64) ↦₆₄ w376) ∗ ((out + 384#64) ↦₆₄ w384) ∗
  ((out + 408#64) ↦₆₄ w408) ∗ ((out + 416#64) ↦₆₄ w416) ∗
  ((out + 440#64) ↦₆₄ w440) ∗ ((out + 448#64) ↦₆₄ w448) ∗ ((out + 456#64) ↦₆₄ w456) ∗ ((out + 464#64) ↦₆₄ w464) ∗
  ((out + 472#64) ↦₆₄ w472) ∗ ((out + 480#64) ↦₆₄ w480) ∗
  ((out + 488#64) ↦₁₂₈ q488) ∗ ((out + 504#64) ↦₆₄ w504)

/-- Stack cells read in Step B (`+19128 -> +19280`). -/
def epilogueRecvStackPartB (fsp : BitVec 64)
    (w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 : BitVec 64) : SepProp :=
  ((fsp + 248#64) ↦₆₄ w248) ∗ ((fsp + 256#64) ↦₆₄ w256) ∗
  ((fsp + 264#64) ↦₆₄ w264) ∗ ((fsp + 272#64) ↦₆₄ w272) ∗ ((fsp + 280#64) ↦₆₄ w280) ∗
  ((fsp + 304#64) ↦₆₄ w304) ∗ ((fsp + 312#64) ↦₆₄ w312) ∗ ((fsp + 320#64) ↦₆₄ w320) ∗ ((fsp + 328#64) ↦₆₄ w328) ∗
  ((fsp + 344#64) ↦₆₄ w344) ∗ ((fsp + 360#64) ↦₆₄ w360) ∗
  ((fsp + 392#64) ↦₆₄ w392) ∗ ((fsp + 400#64) ↦₆₄ w400) ∗
  ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗
  ((fsp + 440#64) ↦₆₄ w440) ∗ ((fsp + 448#64) ↦₆₄ w448) ∗
  ((fsp + 464#64) ↦₆₄ w464) ∗ ((fsp + 472#64) ↦₆₄ w472) ∗
  ((fsp + 480#64) ↦₆₄ w480) ∗ ((fsp + 488#64) ↦₆₄ w488)

set_option maxHeartbeats 1600000 in
theorem epilogue_step_19128_19280
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256 : BitVec 64)
    (u360 u368 u376 u384 u408 u416 u440 u448 u456 u464 u472 u480 : BitVec 64)
    (uq488 : BitVec 128) (u504 : BitVec 64)
    (w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19128#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 512#64)
    (hx1 : s.readReg64 .x1 = fsp + 576#64)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19280#64)
      s
      (epilogueRecvOutPartB out u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256
         u360 u368 u376 u384 u408 u416 u440 u448 u456 u464 u472 u480 uq488 u504 ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          epilogueRecvOutPartB out
            w424 (s.readReg64 .x23) (s.readReg64 .x27) w440
            w264 w344 w392 w272
            w360 w400 w464 w304
            w328 w280 w320 (s.readReg64 .x3)
            w312 (s.readReg64 .x24)
            w416 (s.readReg64 .x17) w472 (s.readReg64 .x26)
            w448 (s.readReg64 .x22)
            w480 (s.readReg64 .x16) w488 (s.readReg64 .x2)
            w248 (s.readReg64 .x20)
            (s.readVReg128 0#5) w256 ∗
          epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out + 512#64 ∧
        sm.readReg64 .x1 = fsp + 576#64 ∧
        sm.readReg64 .x2 = 376#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx19
  states_recv_fetches_range b (Rust.withPanics ext) 19128 152
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_simp_pre [epilogueRecvOutPartB, epilogueRecvStackPartB, pointsTo128, sepConj_assoc]
  wp_steps
  simp only [epilogueRecvOutPartB, epilogueRecvStackPartB, pointsTo128, sepConj_assoc]
  wp_done

theorem epilogue_step_19280_19324
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s : State) (fsp out : BitVec 64)
    (bs576 : List (BitVec 8)) (hbs576 : bs576.length = 376)
    (uq888 uq904 uq944 q512 q528 q544 : BitVec 128)
    (u920 u928 u936 w232 w560 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19280#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 512#64)
    (hx1 : s.readReg64 .x1 = fsp + 576#64)
    (hx2 : s.readReg64 .x2 = 376#64)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19324#64)
      s
      (stackAt fsp allocHookStack ∗
       memRegion (out + 512#64) 376 ∗
       ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
       ((out + 920#64) ↦₆₄ u920) ∗ ((out + 928#64) ↦₆₄ u928) ∗
       ((out + 936#64) ↦₆₄ u936) ∗ ((out + 944#64) ↦₁₂₈ uq944) ∗
       ((fsp + 232#64) ↦₆₄ w232) ∗
       ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗
       ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
       ((fsp + 576#64) ↦ₛ bs576) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp allocHookStack ∗
          ((out + 512#64) ↦ₛ bs576) ∗
          ((out + 888#64) ↦₁₂₈ q528) ∗ ((out + 904#64) ↦₁₂₈ q544) ∗
          ((out + 920#64) ↦₆₄ w560) ∗ ((out + 928#64) ↦₆₄ w232) ∗
          ((out + 936#64) ↦₆₄ s.readReg64 .x20) ∗ ((out + 944#64) ↦₁₂₈ q512) ∗
          ((fsp + 232#64) ↦₆₄ w232) ∗
          ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗
          ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
          ((fsp + 576#64) ↦ₛ bs576) ∗
          Frame) ∧
        sm.sp = fsp ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx19
  have hmemcpy := hA.session_memcpy_ok_at statesRecvName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
  simp only [sessionMemcpySpec, allocHookStack] at hmemcpy ⊢
  rw [← hbs576]
  states_recv_fetches_range b (Rust.withPanics ext) 19280 44
  dsimp only [contractProg, tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_simp_pre [pointsTo128, sepConj_assoc]
  wp_steps
  wp_call hmemcpy (s.readReg64 .x19 + 512#64, s.sp + 576#64, bs576)
  wp_steps
  simp only [pointsTo128, sepConj_assoc]
  wp_done

end CryptoVerification.SpqrV1.States.Recv
