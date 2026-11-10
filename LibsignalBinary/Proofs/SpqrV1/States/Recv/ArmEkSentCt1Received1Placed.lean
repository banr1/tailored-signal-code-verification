/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonPlaced
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ekSentCt1Received` Arm, Part 1 (Relocatable)

Relocatable `[LibsignalPlacement]` proofs for the `>`, `<`, `= ∧ ¬ .ct2`, and post-call `.error`
paths and `<EkSentCt1Received>::recv_ct2_chunk` call rule of `.ekSentCt1Received` (`+228`,
Block `332`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_96_add_8_recv sp_sub_80_add_8_recv sp_sub_64_add_8_recv sp_sub_48_add_8_recv
  sp_sub_32_add_8_recv sp_sub_16_add_8_recv sp_sub_96_add_96_recv
  sp_sub_4240_add_4144_hs bv376_toNat_hs
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. `.ekSentCt1Received` (`+228`, Block `332`): `msg.epoch > st.uc.epoch` -/

/-- Relocatable `msg.epoch > st.uc.epoch` tail-call block `0x55664..0x5569c`
    (`+528 -> s0.x30`, Block `332`) for `.ekSentCt1Received`:
    writes `Err(EpochOutOfRange(msg.epoch))` to `outA`, restores `sp = s0.sp` and `x19..x30`,
    and tail-calls Block `278` (`drop_chunked_ek_sent_ct1_received_cl_on`) on `selfA + 8#64`. -/
theorem ekSentCt1Received_gt_55664_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s0 s : State) (outA selfA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (ep : BitVec 64) (P_rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 528#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx8 : s.readReg64 .x8 = selfA + 8#64)
    (hx19 : s.readReg64 .x19 = outA)
    (hx25 : s.readReg64 .x25 = ep)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        (selfA ↦₆₄ 6#64) ∗
        chunkedEkSentCt1ReceivedAt A (selfA + 8#64) st ∗
        memRegion (selfA + 512#64) 416 ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange ep))) ∗
          memRegion selfA chunkedStatesSize ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hdrop_cl : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 278)
      (withLsCodeLoaded lsmpl (dropChunkedEkSentCt1ReceivedSpec A F)) :=
    drop_chunked_ek_sent_ct1_received_cl_on hdealloc
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp_align (by decide)
  rw [lsmpl_base_332_eq] at hpc
  dsimp only [lsProg_332, dropChunkedEkSentCt1ReceivedSpec, chunkedEkSentCt1ReceivedSize,
    BitVec.ofNat_eq_ofNat] at hdrop_cl hpc ⊢
  refine CryptoVerification.sepWP_seq_lscl hcl (mid := lsmpl.base 278) ?_
  rw [memRegion_out_960_split_err outA]
  wp_pull_exists; rename_i v0 b8 v16
  unfold statesRecvSavedCells
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hsp96_align ⊢
  wp_steps
  subst hsp0
  refine SepWP.done rfl hrun (fun hcl1 => ?_)
  have hdrop_raw := subroutine_ok_withMemEq_of_withLsCodeLoaded hdrop_cl hcl1
  dsimp only [withMemEq] at hdrop_raw
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.focus_weaken hrest (by sep_focus) ?_
  have hsplit_sp := stackAt_statesRecvStackX_split_dropStack32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit_sp) (by sep_focus) ?_
  wp_call hdrop_raw ⟨selfA + 8#64, st⟩
  refine SepWP.focus_weaken (Entails.of_eq hsplit_sp.symm) (by sep_focus) ?_
  refine SepWP.fold
    (F := P_rest ∗ A.pool ∗ stackAt s0.sp statesRecvStackX)
    (sepConj_mono
      (err_epochOutOfRange_entails_resultV1RecvAt A (F := F) outA ep)
      (self_504_416_entails_memRegion_928 selfA 6#64))
    (by ac_rfl) ?_
  wp_done

/-- Relocatable `.ekSentCt1Received` arm when `msg.epoch > st.uc.epoch`
    (`+228 -> s0.x30`, `0x55538..0x5569c -> b 0x4c92c`, Block `332`). -/
theorem ekSentCt1Received_arm_gt_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hgt : msg.epoch > st.uc.epoch)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg.epoch))) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hgt_nat : msg.epoch.toNat > st.uc.epoch.toNat := BitVec.lt_def.mp hgt
  have hcond1 := epoch_cmp_ct1r_eq_of_gt hgt_nat
  have hcond2 := epoch_cmp_ct1r_bne_1_of_gt hgt_nat
  have htail := @ekSentCt1Received_gt_55664_placed _ A F ext hdealloc s0
  rw [lsmpl_base_332_eq] at hpc htail
  dsimp only [lsProg_332, chunkedStatesAt, messageAt, BitVec.ofNat_eq_ofNat] at hpc htail ⊢
  refine CryptoVerification.sepWP_seq_lscl hcl (mid := (blkPl_332).base + 528#64) ?_
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedEkSentCt1ReceivedAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw12 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    rw [hw12]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps
  subst hsp0
  refine SepWP.done rfl hrun (fun hcl1 => ?_)
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, w.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7,
             sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w.b5.w7, w.b5.w5, sp.b1.w2, sp.b1.w3, sp.b1.w4, sp.b1.w5, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, sp.b2.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, sp.b2.w7,
             sp.b2.w8, sp.b2.w9⟩
      b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
             sp.b3.w8, w.b2.w8⟩
      b4 := ⟨w.b2.w6, st.uc.epoch, w.b1.w9, w.b1.w0, w.b2.w2, sp.b4.w5, w.b0.w4, w.b1.w1,
             w.b2.w0, w.b2.w3⟩
      b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, sp.b5.w5, w.b0.w3, w.b2.w4,
             w.b4.w6, w.b5.w4⟩
      w60 := w.b5.w6
      w61 := w.b0.w2
      w62 := w.b0.w6
      q200 := sp.q200
      q210 := sp.q210
      q220 := sp.q220
      w230 := sp.w230
      q3c0 := sp.q3c0 }
  have hfold_frame :
      (words63At (selfA + 8#64) w ∗
       relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w))) ∗
      (sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
       memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
       memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
       memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
       sendEkUnusedAt (s0.sp - 4240#64)) ⊢
        chunkedEkSentCt1ReceivedAt A (selfA + 8#64) st ∗
        memRegion (s0.sp - 4240#64) 4144 :=
    sepConj_mono (recompose63 (selfA + 8#64) w)
      (sendEkFrame_entails_memRegion_4144 (s0.sp - 4240#64) sp1)
  refine SepWP.fold
    (F := P_rest ∗
      memRegion outA v1RecvSize ∗
      (selfA ↦₆₄ 6#64) ∗
      memRegion (selfA + 512#64) 416 ∗
      ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
      A.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      statesRecvSavedCells s0)
    hfold_frame ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    rw [hw12]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  · rw [show (chunkedEkSentCt1ReceivedAt A (selfA + 8#64) st ∗ memRegion (s0.sp - 4240#64) 4144) ∗
        (P_rest ∗
          memRegion outA v1RecvSize ∗
          (selfA ↦₆₄ 6#64) ∗
          memRegion (selfA + 512#64) 416 ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          statesRecvSavedCells s0) =
        (P_rest ∗ ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload)) ∗
        memRegion outA v1RecvSize ∗
        (selfA ↦₆₄ 6#64) ∗
        chunkedEkSentCt1ReceivedAt A (selfA + 8#64) st ∗
        memRegion (selfA + 512#64) 416 ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (htail _ outA selfA st msg.epoch
        (P_rest ∗ ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload))
        hcl1 rfl hrun hsp hsp_align
        (by simp only [Reg.x8, arm64_norm, hx1])
        (by simp only [Reg.x19, arm64_norm, hx19])
        (by simp only [Reg.x25, arm64_norm, hx24])
        htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    exact Entails.trans hPf (Entails.of_eq (by ac_rfl))

/-! ## 2. `.ekSentCt1Received` (`+228`, Block `332`): `msg.epoch < st.uc.epoch` -/

set_option maxHeartbeats 1200000 in
/-- Relocatable `.ekSentCt1Received` arm when `msg.epoch < st.uc.epoch`
    (`+228 -> s0.x30`, `0x55538..0x55660 -> 0x57508..0x575c8 -> 0x57ffc..0x5800c -> 0x59e88..0x59ff0`). -/
theorem ekSentCt1Received_arm_lt_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hlt : msg.epoch < st.uc.epoch)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekSentCt1Received st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hlt_nat : msg.epoch.toNat < st.uc.epoch.toNat := BitVec.lt_def.mp hlt
  have hcond1 := epoch_cmp_ct1r_eq_of_lt hlt_nat
  have hcond2 := epoch_cmp_ct1r_bne_1_of_lt hlt_nat
  have hwb := @states_recv_writeback_59e88_sat _ ext hmemcpy_sat (F_tail := fun a => memRegion a 376)
    (Relocatable.of_memRegion 376) s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, chunkedStatesAt, messageAt, BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  refine CryptoVerification.sepWP_seq_lscl hcl (mid := (blkPl_332).base + 18996#64) ?_
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedEkSentCt1ReceivedAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw12 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    rw [hw12]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 256
  subst hsp0
  refine SepWP.done rfl hrun (fun hcl1 => ?_)
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, w.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7,
             sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w.b5.w7, w.b5.w5, sp.b1.w2, sp.b1.w3, sp.b1.w4, sp.b1.w5, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, 6#64,
             noneCap, sp.b2.w9⟩
      b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
             w.b3.w0, w.b2.w8⟩
      b4 := ⟨w.b2.w6, st.uc.epoch, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, w.b0.w4, w.b1.w1,
             w.b2.w0, w.b2.w3⟩
      b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, w.b5.w0, w.b0.w3, w.b2.w4,
             w.b4.w6, w.b5.w4⟩
      w60 := w.b5.w6
      w61 := w.b0.w2
      w62 := w.b0.w6
      q200 := sp.q200
      q210 := sp.q210
      q220 := sp.q220
      w230 := sp.w230
      q3c0 := w.q60 }
  have hfold_self :
      ((selfA ↦₆₄ 6#64) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion selfA chunkedStatesSize ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono_left (words63At_self_entails_memRegion_928 selfA 6#64 w)
  refine SepWP.fold
    (F := P_rest ∗
      relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
      ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
      A.pool ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗
      statesRecvSavedCells s0)
    hfold_self ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    rw [hw12]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [show (memRegion selfA chunkedStatesSize ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0) =
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool) ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool)
        rfl hrun hsp hsp_align (by simp only [Reg.x19, arm64_norm, hx19]) htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_ekSentCt1Received_entails_resultV1RecvAt A (F := F) outA st w
      w.b5.w9 sp.q200
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_left hrec))
    dsimp only [writebackWords63, words63At, words10At, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4,
      Reg.x5, Reg.x6, Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15,
      Reg.x16, Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x30]
    rw [hw12]
    simp only [arm64_norm]
    ac_rfl

/-! ## 3. `.ekSentCt1Received` (`+228`, Block `332`): `msg.epoch = st.uc.epoch` & `msg.payload ≠ .ct2 _` -/

set_option maxHeartbeats 1200000 in
/-- Relocatable `.ekSentCt1Received` arm when `msg.epoch = st.uc.epoch` and `msg.payload ≠ .ct2 _`
    (`+228 -> s0.x30`, `0x55538..0x55658 -> 0x56544..0x5654c -> 0x57f40..0x5800c -> 0x59e88..0x59ff0`). -/
theorem ekSentCt1Received_arm_eq_other_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (heq : msg.epoch = st.uc.epoch)
    (hct2 : ∀ c, msg.payload ≠ .ct2 c)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekSentCt1Received st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hcond1 := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hcond_tag1 := messagePayloadTag_eq_6_of_not_ct2 hct2
  have hcond_tag2 := messagePayloadTag_bne_6_of_not_ct2 hct2
  have hwb := @states_recv_writeback_59e88_sat _ ext hmemcpy_sat (F_tail := fun a => memRegion a 376)
    (Relocatable.of_memRegion 376) s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, chunkedStatesAt, messageAt, BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  refine CryptoVerification.sepWP_seq_lscl hcl (mid := (blkPl_332).base + 18996#64) ?_
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedEkSentCt1ReceivedAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw12 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    rw [hw12, heq, messagePayloadAt_eq_tag_tail msgA msg.payload]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 256
  subst hsp0
  refine SepWP.done rfl hrun (fun hcl1 => ?_)
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, w.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7,
             sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w.b5.w7, w.b5.w5, sp.b1.w2, sp.b1.w3, sp.b1.w4, sp.b1.w5, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, 6#64,
             noneCap, w.b4.w2⟩
      b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
             w.b3.w0, w.b2.w8⟩
      b4 := ⟨w.b2.w6, st.uc.epoch, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, w.b0.w4, w.b1.w1,
             w.b2.w0, w.b2.w3⟩
      b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, w.b5.w0, w.b0.w3, w.b2.w4,
             w.b4.w6, w.b5.w4⟩
      w60 := w.b5.w6
      w61 := w.b0.w2
      w62 := w.b0.w6
      q200 := sp.q200
      q210 := sp.q210
      q220 := sp.q220
      w230 := sp.w230
      q3c0 := w.q60 }
  have hfold_self :
      ((selfA ↦₆₄ 6#64) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416) ∗
      (((msgA + 8#64) ↦₈ messagePayloadTag msg.payload) ∗ messagePayloadTailAt msgA msg.payload) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion selfA chunkedStatesSize ∗
        messagePayloadAt spqrPolyApi msgA msg.payload ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono (words63At_self_entails_memRegion_928 selfA 6#64 w)
      (sepConj_mono_left (Entails.of_eq (messagePayloadAt_eq_tag_tail msgA msg.payload).symm))
  refine SepWP.fold
    (F := P_rest ∗
      relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
      (msgA ↦₆₄ msg.epoch) ∗
      A.pool ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗
      statesRecvSavedCells s0)
    hfold_self ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    rw [hw12, heq]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [show (memRegion selfA chunkedStatesSize ∗
          messagePayloadAt spqrPolyApi msgA msg.payload ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          (msgA ↦₆₄ msg.epoch) ∗
          A.pool ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0) =
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool) ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool)
        rfl hrun hsp hsp_align (by simp only [Reg.x19, arm64_norm, hx19]) htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_ekSentCt1Received_entails_resultV1RecvAt A (F := F) outA st w
      w.b5.w9 sp.q200
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_left hrec))
    dsimp only [writebackWords63, words63At, words10At, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4,
      Reg.x5, Reg.x6, Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15,
      Reg.x16, Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x30]
    rw [hw12]
    simp only [arm64_norm]
    ac_rfl

/-! ## 4. Post-Call `.error (.err .macVerifyFailed)` Path (`+4384 -> s0.x30`) and Call Rule -/

/-- Relocatable post-call block `0x56574..0x565a4 -> 0x59fd0..0x59ff0` (`+4384 -> s0.x30`, Block `332`)
    when `recv_ct2_chunk` returns `.error (.err .macVerifyFailed)`. -/
theorem ekSentCt1Received_post_call_err_56574_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s : State) (outA : BitVec 64)
    (sp : SendEkSpills) (P_rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 4384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        ekSentCt1ReceivedRecvChunkResultAt A (F := F) ((s0.sp - 4240#64) + 976#64)
          (.error (.err .macVerifyFailed)) ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.error (.err .macVerifyFailed)) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hep := @states_recv_epilogue_59fd0_placed _ ext s0
  rw [lsmpl_base_332_eq] at hpc hep
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hep ⊢
  refine CryptoVerification.sepWP_seq_lscl hcl (mid := (blkPl_332).base + 19324#64) ?_
  refine SepWP.fold (err_result_976_extract A (F := F) (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i w1 w2 w3
  refine SepWP.fold (memRegion_960_split_err4 outA) (by sep_focus) ?_
  wp_pull_exists; rename_i v0 v8 v16 v24
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  subst hx19
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, none2Cap, Reg.x19]
    simp only [BitVec.add_assoc, arm64_norm]
  wp_steps
  subst hsp0
  refine SepWP.done rfl hrun (fun _ => ?_)
  let sp_err : SendEkSpills := { sp with w61 := w3 }
  have h880_976 := err_result_976_fold_880 (s0.sp - 4240#64) w1 w2 w3
  have h880_1856 :
      memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
      memRegion ((s0.sp - 4240#64) + 2360#64) 376 ⊢
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 := by
    rw [ProofLib.memRegion_split' (b := (s0.sp - 4240#64) + 1856#64) (n := 504) (k := 376)
      (b' := (s0.sp - 4240#64) + 2360#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hout := err4_entails_resultV1RecvAt_macVerifyFailed A (F := F) (s.readReg64 .x19) w1 w2 w3
  have hfold_all :
      (((s.readReg64 .x19) ↦₆₄ noneCap) ∗ (((s.readReg64 .x19) + 8#64) ↦₆₄ w1) ∗
       errMacVerifyTag8Split.heap (unpack64 w1) ∗
       (((s.readReg64 .x19) + 16#64) ↦₆₄ w2) ∗ (((s.readReg64 .x19) + 24#64) ↦₆₄ w3) ∗
       memRegion ((s.readReg64 .x19) + 32#64) 928) ∗
      (sendEkSpillsAt (s0.sp - 4240#64) sp_err ∗
       memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
       (((s0.sp - 4240#64 + 976#64) ↦₆₄ none2Cap) ∗
        ((s0.sp - 4240#64 + 984#64) ↦₆₄ w1) ∗
        ((s0.sp - 4240#64 + 992#64) ↦₆₄ w2) ∗
        ((s0.sp - 4240#64 + 1000#64) ↦₆₄ w3) ∗
        memRegion ((s0.sp - 4240#64) + 1008#64) 472 ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376) ∗
       (memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376) ∗
       sendEkUnusedAt (s0.sp - 4240#64)) ⊢
        resultV1RecvAt A (F := F) (s.readReg64 .x19) (.error (.err .macVerifyFailed)) ∗
        memRegion (s0.sp - 4240#64) 4144 :=
    sepConj_mono hout
      (Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono h880_976 (sepConj_mono_left h880_1856))))
        (sendEkFrame_entails_memRegion_4144 (s0.sp - 4240#64) sp_err))
  refine SepWP.fold
    (F := P_rest ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      statesRecvSavedCells s0)
    hfold_all ?_ ?_
  · dsimp only [sendEkSpillsAt, sp_err, none2Cap, noneCap, Reg.x19]
    simp only [BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [show (resultV1RecvAt A (F := F) (s.readReg64 .x19) (.error (.err .macVerifyFailed)) ∗
          memRegion (s0.sp - 4240#64) 4144) ∗
        (P_rest ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          statesRecvSavedCells s0) =
        (P_rest ∗ resultV1RecvAt A (F := F) (s.readReg64 .x19) (.error (.err .macVerifyFailed))) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (hep _ (P_rest ∗ resultV1RecvAt A (F := F) (s.readReg64 .x19) (.error (.err .macVerifyFailed)))
        rfl hrun hsp hsp_align htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    exact Entails.trans hPf (Entails.of_eq (by ac_rfl))

/-- Relocatable framed call rule for `withLsCodeRoLoaded lsmpl (recvCt2ChunkPlacedSpec K F A)` (Block `350`). -/
theorem call_ekSentCt1ReceivedRecvCt2Chunk_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (recvCt2ChunkPlacedSpec K F A)))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (hsort : PolyDecoderStrictSorted st.receiving_ct2)
    (hroot : st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post Q_panic : State → SepProp → Prop}
    (hcro_s : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.uc.epoch)
    (hx3 : s.readReg64 Reg.x3 = chunkA)
    (hsplit : P = (memRegion outA chunkedEkSentCt1ReceivedSize ∗
      ekSentCt1ReceivedAt A stA st ∗ chunkAt chunkA chunk ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool ∗ stackAt sp_call recvCt2ChunkStackX) ∗ Frame)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜((st.recv_ct2_chunk K st.uc.epoch chunk).isPanic = true ∨
            allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) →
      Q_panic sf P_f)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((ekSentCt1ReceivedRecvChunkResultAt A (F := F) outA (st.recv_ct2_chunk K st.uc.epoch chunk) ∗
          memRegion stA chunkedEkSentCt1ReceivedSize ∗ chunkAt chunkA chunk ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool ∗ stackAt sp_call recvCt2ChunkStackX) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Q_panic) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨outA, stA, st, st.uc.epoch, chunkA, chunk⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ => hpanic sf _ fun hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro_s, ?_⟩
    dsimp only [recvCt2ChunkPlacedSpec]
    rw [hsp]
    simp only [sepConj_assoc] at hm ⊢
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hsort, hroot⟩, hm⟩
  · dsimp only [withLsCodeRoLoaded, recvCt2ChunkPlacedSpec] at hmem
    refine allowPanic_frame (fun ⟨hdisj, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at hdisj ⊢
    rw [htrace.1] at hdisj htr_sub
    exact ⟨hdisj, htr_sub⟩
  · dsimp only [withLsCodeRoLoaded, recvCt2ChunkPlacedSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (ekSentCt1ReceivedRecvChunkResultAt A (F := F) outA (st.recv_ct2_chunk K st.uc.epoch chunk) ∗
          memRegion stA chunkedEkSentCt1ReceivedSize ∗ chunkAt chunkA chunk ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool ∗ stackAt sp_call recvCt2ChunkStackX) ∗ Frame =
        (ekSentCt1ReceivedRecvChunkResultAt A (F := F) outA (st.recv_ct2_chunk K st.uc.epoch chunk) ∗
          (memRegion stA chunkedEkSentCt1ReceivedSize ∗
            (chunkAt chunkA chunk ∗ (tokenInitPlacedAt ∗ (reduceTablePlacedAt ∗
              (A.pool ∗ stackAt sp_call recvCt2ChunkStackX)))))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

end LibsignalBinary.Proofs.SpqrV1.States.Recv

namespace CryptoVerification.SpqrV1.States.Recv

export LibsignalBinary.Proofs.SpqrV1.States.Recv (
  ekSentCt1Received_gt_55664_placed
  ekSentCt1Received_arm_gt_placed
  ekSentCt1Received_arm_lt_placed
  ekSentCt1Received_arm_eq_other_placed
  ekSentCt1Received_post_call_err_56574_placed
  call_ekSentCt1ReceivedRecvCt2Chunk_placed
)

end CryptoVerification.SpqrV1.States.Recv
