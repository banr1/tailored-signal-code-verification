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
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonPlaced
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ct1Received` Arm, Part 1 (Relocatable)

Relocatable `[LibsignalPlacement]` post-call writeback helpers and the `msg.epoch > st.uc.epoch`
and `msg.epoch < st.uc.epoch` paths of `.ct1Received` (`lsmpl.base 332 + 1204#64`).
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
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. `.ct1Received` (`+1204`, Block `332`) Relocatable Helper Blocks -/

/-- Relocatable `msg.epoch > st.uc.epoch` error block `0x55c8c..0x55ca4` (`+2104 -> +19356`, Block `332`)
    for `.ct1Received`:
    writes `Err(EpochOutOfRange(msg.epoch))` to `outA`, calls Block `277` (`drop_chunked_ct1_received_cl_on`)
    on `selfA + 8#64`, and branches to `+19324` (`states_recv_epilogue_59fd0_placed`). -/
theorem ct1Received_gt_55c8c_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s0 s : State) (outA selfA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (ep : BitVec 64) (P_rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 2104#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = selfA + 8#64)
    (hx19 : s.readReg64 .x19 = outA)
    (hx25 : s.readReg64 .x25 = ep)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        (selfA ↦₆₄ 5#64) ∗
        chunkedCt1ReceivedAt A (selfA + 8#64) st ∗
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
  have hdrop_cl : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 277)
      (withLsCodeLoaded lsmpl (dropChunkedCt1ReceivedSpec A F)) :=
    drop_chunked_ct1_received_cl_on hdealloc
  have hepilogue := @states_recv_epilogue_59fd0_placed _ ext s0
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  rw [lsmpl_base_332_eq] at hpc hepilogue
  dsimp only [lsProg_332, dropChunkedCt1ReceivedSpec, chunkedCt1ReceivedSize,
    BitVec.ofNat_eq_ofNat] at hdrop_cl hepilogue hpc ⊢
  refine CryptoVerification.sepWP_seq_lscl hcl (mid := lsmpl.base 277) ?_
  rw [memRegion_out_960_split_err outA]
  wp_pull_exists; rename_i v0 b8 v16
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_steps
  subst hsp0
  refine SepWP.done rfl hrun (fun hcl1 => ?_)
  have hdrop_raw := subroutine_ok_withMemEq_of_withLsCodeLoaded hdrop_cl hcl1
  dsimp only [withMemEq] at hdrop_raw
  have hsplit_sp := stackAt_statesRecvCallee_split_dropStack32 (s0.sp - 4240#64)
  refine SepWP.focus_weaken (Entails.of_eq hsplit_sp) (by sep_focus) ?_
  wp_call hdrop_raw ⟨selfA + 8#64, st⟩
  wp_conv_pre => rw [hsp]
  refine SepWP.focus_weaken (Entails.of_eq hsplit_sp.symm) (by sep_focus) ?_
  refine sepWP_seq_cut ((blkPl_332).base + 19324#64) ?_
  wp_steps
  refine SepWP.done rfl (by assumption) ?_
  refine SepWP.fold
    (F := P_rest ∗ A.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0)
    (sepConj_mono
      (err_epochOutOfRange_entails_resultV1RecvAt A (F := F) outA ep)
      (self_504_416_entails_memRegion_928 selfA 5#64))
    (by ac_rfl) ?_
  rw [show (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange ep))) ∗
        memRegion selfA chunkedStatesSize) ∗
      (P_rest ∗ A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0) =
      (P_rest ∗ resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange ep))) ∗
        memRegion selfA chunkedStatesSize ∗ A.pool) ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0 by ac_rfl]
  refine SepWP.mono
    (hepilogue _
      (P_rest ∗ resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange ep))) ∗
        memRegion selfA chunkedStatesSize ∗ A.pool)
      ?_ ?_ ?_ hsp_align ?_)
    (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)
  · rfl
  · assumption
  · exact (by assumption : _ = s.sp).trans hsp
  · exact ⟨(by assumption : _ = s.trace).trans htr.1,
      (by assumption : _ = calleeSavedVRegs _).trans (by simpa only [arm64_norm] using htr.2)⟩

set_option maxHeartbeats 1200000 in
/-- Relocatable post-call writeback block `0x56d78..0x56ef4 -> 0x56fa4..0x56fdc -> 0x59e88..0x59ff0`
    (`+6436 -> +19356`, Block `332`) after `<Ct1Received>::recv_ct2_chunk` returns `outSt` at `fsp + 976#64`. -/
theorem ct1Received_post_call_56d78_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 6436#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        chunkedEkSentCt1ReceivedAt A ((s0.sp - 4240#64) + 976#64) outSt ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekSentCt1Received outSt }) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hwb := @states_recv_writeback_59e88_placed _ ext hmemcpy (F_tail := fun a => memRegion a 376)
    (Relocatable.of_memRegion 376) s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hwb hpc ⊢
  refine SepWP.fold (chunkedEkSentCt1ReceivedAt_extract63 A ((s0.sp - 4240#64) + 976#64) outSt)
    (by sep_focus) ?_
  wp_pull_exists; rename_i w_out
  refine SepWP.pure_elim fun _ => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  refine sepWP_seq_cut ((blkPl_332).base + 18996#64) ?_
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps
  subst hsp0
  refine SepWP.done rfl hrun ?_
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, sp.b0.w3, sp.b0.w4, w_out.b4.w1, sp.b0.w6, sp.b0.w7,
             sp.b0.w8, w_out.b3.w3⟩
      b1 := ⟨sp.b1.w0, sp.b1.w1, sp.b1.w2, sp.b1.w3, sp.b1.w4, sp.b1.w5, w_out.b0.w0,
             w_out.b5.w9, w_out.b1.w5, w_out.b1.w6⟩
      b2 := ⟨sp.b2.w0, sp.b2.w1, sp.b2.w2, w_out.b4.w3, sp.b2.w4, w_out.b0.w1, sp.b2.w6, 6#64,
             noneCap, w_out.b4.w2⟩
      b3 := ⟨w_out.b5.w8, w_out.w62, w_out.b1.w8, w_out.b2.w1, w_out.b2.w7, w_out.b0.w7,
             w_out.b1.w3, w_out.b2.w5, w_out.b3.w0, w_out.b2.w8⟩
      b4 := ⟨w_out.b2.w6, w_out.b1.w2, w_out.b1.w9, w_out.b1.w0, w_out.b2.w2, w_out.b0.w5,
             w_out.b0.w4, w_out.b1.w1, w_out.b2.w0, w_out.b2.w3⟩
      b5 := ⟨w_out.b0.w9, w_out.b4.w4, w_out.b1.w4, w_out.b0.w8, w_out.b1.w7, w_out.b5.w0,
             w_out.b0.w3, w_out.b2.w4, w_out.b4.w6, w_out.b5.w4⟩
      w60 := w_out.b5.w6
      w61 := w_out.b0.w2
      w62 := w_out.b0.w6
      q200 := sp.q200
      q210 := sp.q210
      q220 := sp.q220
      w230 := sp.w230
      q3c0 := w_out.q60 }
  have hfold_sp1 :
      (words63At ((s0.sp - 4240#64) + 976#64) w_out ∗
       memRegion ((s0.sp - 4240#64) + 1480#64) 376) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono_left (words63At_376_entails_memRegion_880
      ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) w_out (by bv_omega))
  refine SepWP.fold
    (F := P_rest ∗
      relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)) ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗
      statesRecvSavedCells s0)
    hfold_sp1
    ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [show (memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)) ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0) =
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out))) ∗
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
        (P_rest ∗ relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)))
        ?_ ?_ ?_ hsp_align ?_ ?_)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    · rfl
    · exact hrun
    · exact hsp
    · simp only [Reg.x19, arm64_norm, hx19]
    · exact htr
    · refine Entails.trans hPf ?_
      have hrec := writeback_ekSentCt1Received_entails_resultV1RecvAt A (F := F) outA outSt w_out
        w_out.b5.w9 sp.q200
      refine Entails.trans (Entails.of_eq ?_)
        (sepConj_mono_right (sepConj_mono_left hrec))
      rcases w_out with ⟨⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩, _, _⟩
      dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
        Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
        Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
        Reg.x30]
      simp only [arm64_norm]
      ac_rfl

/-! ## 2. Full Relocatable `.ct1Received` Arm (`+1204 -> s0.x30`, Block `332`) -/

/-- Relocatable `.ct1Received` arm when `msg.epoch > st.uc.epoch`
    (`+1204 -> s0.x30`, `0x55908..0x55a48 -> 0x55c8c..0x59ff0`, Block `332`). -/
theorem ct1Received_arm_gt_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hgt : msg.epoch > st.uc.epoch)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 1204#64)
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
        chunkedStatesAt A selfA (.ct1Received st) ∗
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
  have hcond2 := epoch_cmp_ct1r_eq_1_of_gt hgt_nat
  have htail := @ct1Received_gt_55c8c_placed _ A F ext hdealloc s0
  rw [lsmpl_base_332_eq] at hpc htail
  dsimp only [lsProg_332, chunkedStatesAt, messageAt, BitVec.ofNat_eq_ofNat] at hpc htail ⊢
  refine CryptoVerification.sepWP_seq_lscl hcl (mid := (blkPl_332).base + 2104#64) ?_
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (sendEkUnusedAt_split_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i u_ac0
  refine SepWP.fold (chunkedCt1ReceivedAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw62 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  rw [hw62]
  wp_steps
  subst hsp0
  refine SepWP.done rfl hrun (fun hcl1 => ?_)
  let sp1 : SendEkSpills :=
    { b0 := ⟨w.b5.w2, sp.b0.w1, w.b3.w1, sp.b0.w3, sp.b0.w4, sp.b0.w5, w.b4.w0, sp.b0.w7,
             sp.b0.w8, w.b3.w3⟩
      b1 := ⟨sp.b1.w0, sp.b1.w1, w.b3.w9, sp.b1.w3, w.b5.w3, sp.b1.w5, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, sp.b2.w3, w.b4.w5, w.b0.w1, w.b4.w8, sp.b2.w7,
             sp.b2.w8, w.b4.w2⟩
      b3 := ⟨w.b5.w8, w.w62, sp.b3.w2, sp.b3.w3, sp.b3.w4, sp.b3.w5, sp.b3.w6, sp.b3.w7,
             w.b3.w0, sp.b3.w9⟩
      b4 := ⟨sp.b4.w0, w.b1.w2, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, sp.b4.w6, w.b1.w1,
             w.b2.w0, w.b2.w3⟩
      b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, w.b5.w0, sp.b5.w6, w.b2.w4,
             w.b4.w6, w.b5.w4⟩
      w60 := w.b5.w6
      w61 := w.b0.w2
      w62 := w.b0.w6
      q200 := sp.q200
      q210 := sp.q210
      q220 := sp.q220
      w230 := sp.w230
      q3c0 := sp.q3c0 }
  have hfold_unused :
      ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
      memRegion (s0.sp - 4240#64) 8 ∗
      memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
      memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
      memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
      memRegion (s0.sp - 4240#64 + 2768#64) 1376 ⊢
        sendEkUnusedAt (s0.sp - 4240#64) :=
    sendEkUnusedAt_rejoin_ac0 (s0.sp - 4240#64) w.q60
  have hfold_frame :
      (words63At (selfA + 8#64) w ∗
       relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w))) ∗
      (sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
       memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
       memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
       memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
       (((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
        memRegion (s0.sp - 4240#64) 8 ∗
        memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
        memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
        memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
        memRegion (s0.sp - 4240#64 + 2768#64) 1376)) ⊢
        chunkedCt1ReceivedAt A (selfA + 8#64) st ∗
        memRegion (s0.sp - 4240#64) 4144 :=
    sepConj_mono (recompose63 (selfA + 8#64) w)
      (Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hfold_unused))))
        (sendEkFrame_entails_memRegion_4144 (s0.sp - 4240#64) sp1))
  refine SepWP.fold
    (F := P_rest ∗
      memRegion outA v1RecvSize ∗
      (selfA ↦₆₄ 5#64) ∗
      memRegion (selfA + 512#64) 416 ∗
      ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
      A.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      statesRecvSavedCells s0)
    hfold_frame ?_ ?_
  · rw [← hw62]
    dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [show (chunkedCt1ReceivedAt A (selfA + 8#64) st ∗ memRegion (s0.sp - 4240#64) 4144) ∗
        (P_rest ∗
          memRegion outA v1RecvSize ∗
          (selfA ↦₆₄ 5#64) ∗
          memRegion (selfA + 512#64) 416 ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          statesRecvSavedCells s0) =
        (P_rest ∗ ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload)) ∗
        memRegion outA v1RecvSize ∗
        (selfA ↦₆₄ 5#64) ∗
        chunkedCt1ReceivedAt A (selfA + 8#64) st ∗
        memRegion (selfA + 512#64) 416 ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (htail _ outA selfA st msg.epoch
        (P_rest ∗ ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload))
        hcl1 ?_ ?_ ?_ hsp_align ?_ ?_ ?_ ?_)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    · rfl
    · exact hrun
    · exact hsp
    · simp only [Reg.x0, arm64_norm, hx1]
    · simp only [Reg.x19, arm64_norm, hx19]
    · simp only [Reg.x25, arm64_norm, hx24]
    · exact htr
    · refine Entails.trans hPf (Entails.of_eq (by ac_rfl))

set_option maxHeartbeats 1200000 in
/-- Relocatable `.ct1Received` arm when `msg.epoch < st.uc.epoch`
    (`+1204 -> s0.x30`, `0x55908..0x55a48 -> 0x56ef8..0x56fdc -> 0x59e88..0x59ff0`, Block `332`). -/
theorem ct1Received_arm_lt_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = lsmpl.base 332 + 1204#64)
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
        chunkedStatesAt A selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Received st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hlt_nat : msg.epoch.toNat < st.uc.epoch.toNat := BitVec.lt_def.mp hlt
  have hcond1 := epoch_cmp_ct1r_eq_of_lt hlt_nat
  have hcond2 := epoch_cmp_ct1r_eq_1_of_lt hlt_nat
  have hwb := @states_recv_writeback_59e88_placed _ ext hmemcpy (F_tail := fun a => memRegion a 376)
    (Relocatable.of_memRegion 376) s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, chunkedStatesAt, messageAt, BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  refine sepWP_seq_cut ((blkPl_332).base + 18996#64) ?_
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (sendEkUnusedAt_split_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i u_ac0
  refine SepWP.fold (chunkedCt1ReceivedAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw62 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  rw [hw62]
  wp_steps 256
  subst hsp0
  refine SepWP.done rfl hrun ?_
  let sp1 : SendEkSpills :=
    { b0 := ⟨w.b5.w2, sp.b0.w1, w.b3.w1, sp.b0.w3, sp.b0.w4, w.b4.w1, w.b4.w0, sp.b0.w7,
             sp.b0.w8, w.b3.w3⟩
      b1 := ⟨sp.b1.w0, sp.b1.w1, w.b3.w9, sp.b1.w3, w.b5.w3, sp.b1.w5, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, 5#64,
             noneCap, w.b4.w2⟩
      b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
             w.b3.w0, w.b2.w8⟩
      b4 := ⟨w.b2.w6, w.b1.w2, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, w.b0.w4, w.b1.w1,
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
  have hfold_unused :
      ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
      memRegion (s0.sp - 4240#64) 8 ∗
      memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
      memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
      memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
      memRegion (s0.sp - 4240#64 + 2768#64) 1376 ⊢
        sendEkUnusedAt (s0.sp - 4240#64) :=
    sendEkUnusedAt_rejoin_ac0 (s0.sp - 4240#64) w.q60
  have hfold_self_unused :
      ((selfA ↦₆₄ 5#64) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416) ∗
      (((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
       memRegion (s0.sp - 4240#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
       memRegion (s0.sp - 4240#64 + 2768#64) 1376) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion selfA chunkedStatesSize ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono (words63At_self_entails_memRegion_928 selfA 5#64 w)
      (sepConj_mono_left hfold_unused)
  refine SepWP.fold
    (F := P_rest ∗
      relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
      ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
      A.pool ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      statesRecvSavedCells s0)
    hfold_self_unused ?_ ?_
  · rw [← hw62]
    dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [show (memRegion selfA chunkedStatesSize ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          statesRecvSavedCells s0) =
        (P_rest ∗
          relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
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
          relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool)
        ?_ ?_ ?_ hsp_align ?_ ?_)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    · rfl
    · exact hrun
    · exact hsp
    · simp only [Reg.x19, arm64_norm, hx19]
    · exact htr
    · refine Entails.trans hPf ?_
      have hrec := writeback_ct1Received_entails_resultV1RecvAt A (F := F) outA st w
        w.b5.w9 sp.q200
      refine Entails.trans (Entails.of_eq ?_)
        (sepConj_mono_right (sepConj_mono_left hrec))
      dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
        Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
        Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
        Reg.x30]
      simp only [arm64_norm, hx1]
      ac_rfl

end LibsignalBinary.Proofs.SpqrV1.States.Recv

namespace CryptoVerification.SpqrV1.States.Recv

export LibsignalBinary.Proofs.SpqrV1.States.Recv (
  ct1Received_gt_55c8c_placed
  ct1Received_post_call_56d78_placed
  ct1Received_arm_gt_placed
  ct1Received_arm_lt_placed
)

end CryptoVerification.SpqrV1.States.Recv
