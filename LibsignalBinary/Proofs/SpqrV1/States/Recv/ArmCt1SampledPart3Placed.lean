/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymBasePlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DecodesPlaced
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEk
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ct1Sampled` Arm, Part 3 (Relocatable)

Relocatable `[LibsignalPlacement]` message-kind dispatch (`+7052`), unchanged return paths
(`Path 2` and `Path 3`), and `recv_ek_chunk` common prefix (`+11404 -> +11508`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
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
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.CodeLayout

set_option maxRecDepth 400000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_4240_add_4144 sp_sub_4240_add_3856 sp_sub_4240_add_3272
  sp_sub_4240_add_2752 sp_sub_4240_add_3696 sp_sub_4240_add_3832
  sp_sub_4240_add_3840 sp_sub_4240_add_3848
  lsmpl_base_332_eq
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Message Kind Dispatch (`+7052`) & Unchanged Return Paths (`Path 2` & `Path 3`) -/

theorem ct1Sampled_msg_kind_check_other_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (msgA : BitVec 64) (msg_tag : BitVec 8) (Rest : SepProp)
    (hne2 : (BitVec.zeroExtend 32 msg_tag == 2#32) = false)
    (hne3 : (BitVec.zeroExtend 32 msg_tag != 3#32) = true)
    (hpc : s_in.pc = (blkPl_332).base + 7052#64)
    (hrun : s_in.status = .Running)
    (hx24 : s_in.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 12144#64) s_in
      (((msgA + 8#64) ↦₈ msg_tag) ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ ((msgA + 8#64) ↦₈ msg_tag) ∗ Rest) ∧
        sf.sp = s_in.sp ∧
        sf.readReg64 .x1 = s_in.readReg64 .x1 ∧
        sf.readReg64 .x12 = s_in.readReg64 .x12 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hx24
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  wp_done

theorem ct1Sampled_msg_kind_check_ek_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (msgA : BitVec 64) (Rest : SepProp)
    (hpc : s_in.pc = (blkPl_332).base + 7052#64)
    (hrun : s_in.status = .Running)
    (hx24 : s_in.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 11404#64) s_in
      (((msgA + 8#64) ↦₈ 2#8) ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ ((msgA + 8#64) ↦₈ 2#8) ∗ Rest) ∧
        sf.sp = s_in.sp ∧
        sf.readReg64 .x1 = s_in.readReg64 .x1 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = 0#64 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x12 ∧
        sf.readReg64 .x24 = msgA ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hx24
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  wp_done

theorem ct1Sampled_msg_kind_check_ekCt1Ack_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (msgA : BitVec 64) (Rest : SepProp)
    (hpc : s_in.pc = (blkPl_332).base + 7052#64)
    (hrun : s_in.status = .Running)
    (hx24 : s_in.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 11404#64) s_in
      (((msgA + 8#64) ↦₈ 3#8) ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ ((msgA + 8#64) ↦₈ 3#8) ∗ Rest) ∧
        sf.sp = s_in.sp ∧
        sf.readReg64 .x1 = s_in.readReg64 .x1 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = 1#64 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x12 ∧
        sf.readReg64 .x24 = msgA ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hx24
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  wp_done

set_option maxHeartbeats 800000 in
theorem ct1Sampled_store_and_epilogue_same_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s4 : State) (fsp stA outA w200 w208 : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (d : Split928) (sc' : CopyScratchStack)
    (Rest : SepProp)
    (htag : d.c0.w0 = polyEncoderTagVal st.sending_ct1)
    (hmid : d.mid.length = 376)
    (hregs4 : epilogueRegsEqSplit928 s4 d)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc4 : s4.pc = (blkPl_332).base + 18996#64)
    (hrun4 : s4.status = .Running)
    (hsp4 : s4.sp = fsp)
    (hx19_4 : s4.readReg64 .x19 = outA)
    (htr4 : TraceCalleeSaved s4 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s4
      (split928At stA d ∗
        copyScratchStackAt fsp sc' ∗
        epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap w200 w208) ∗
        epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap w200 w208) ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
          memRegion outA chunkedStatesSize ∗
          memRegion (outA + 928#64) 32 ∗
          memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 976#64) 3168 ∗
          statesRecvSavedCells s0 ∗
          Rest))
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled st }) ∗
          memRegion stA chunkedStatesSize ∗
          stackAt s0.sp statesRecvStackX ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  let k' := epilogueStackOfSplit928 d noneCap w200 w208
  have hmid' : k'.mid.length = 376 := hmid
  have hP4' :
      split928At stA d ∗
        copyScratchStackAt fsp sc' ∗
        epilogueStoreStackPart1At fsp k' ∗
        epilogueStoreStackPart2At fsp k' ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
          memRegion outA chunkedStatesSize ∗
          memRegion (outA + 928#64) 32 ∗
          memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 976#64) 3168 ∗
          statesRecvSavedCells s0 ∗
          Rest) ⊢
      epilogueStoreStackPart1At fsp k' ∗
      epilogueStoreStackPart2At fsp k' ∗
      memRegion outA chunkedStatesSize ∗
      memRegion (outA + 928#64) 32 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (split928At stA d ∗
        relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
        copyScratchStackAt fsp sc' ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 3168 ∗
        statesRecvSavedCells s0 ∗
        Rest) := Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hP4' ?_
  refine SepWP.seq (ct1Sampled_epilogue_store_placed hmemcpy s4 fsp outA k' _
    hmid' hfsp_align hpc4 hrun4 hsp4 hx19_4) ?_
  intro s5 P5 hpc5 hrun5 ⟨hP5, hsp5, htr5⟩
  have heq_split : epilogueSplit928 s4 k' = d :=
    epilogueSplit928_of_eq s4 d noneCap w200 w208 hregs4
  have hP5' : P5 ⊢
      stackAt fsp statesRecvCalleeStackX ∗
      memRegion fsp 4144 ∗
      statesRecvSavedCells s0 ∗
      (resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled st }) ∗
        memRegion stA chunkedStatesSize ∗
        Rest) := by
    refine Entails.trans hP5 ?_
    rw [heq_split]
    have hstk := copyScratch_and_epilogueStack_entails_memRegion_4144 fsp sc' k' hmid'
    have hst_out := chunkedCt1SampledAt_reconstruct_split928 A outA st d htag hmid
    have hst_in := split928At_entails_memRegion stA d hmid
    have hkey := optEpochSecretAt_none_of_words4 A (outA + 928#64) (s4.readReg64 .x20) w200 w208
    dsimp only [resultV1RecvAt, v1RecvAt, chunkedStatesAt, k', epilogueStackOfSplit928] at hstk hkey ⊢
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hkey
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt fsp statesRecvCalleeStackX ∗
      (copyScratchStackAt fsp sc' ∗
        epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap w200 w208) ∗
        epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap w200 w208) ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 3168) ∗
      statesRecvSavedCells s0 ∗
      (((split928At outA d ∗ relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes) ∗
        (((outA + 928#64) ↦₆₄ noneCap) ∗
          ((outA + 936#64) ↦₆₄ s4.readReg64 .x20) ∗
          ((outA + 944#64) ↦₆₄ w200) ∗
          ((outA + 952#64) ↦₆₄ w208))) ∗
        split928At stA d ∗
        Rest) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono hstk
      (sepConj_mono_right (sepConj_mono (sepConj_mono hst_out hkey)
        (sepConj_mono_left hst_in))))
  subst hfsp
  refine SepWP.weaken_pre hP5' ?_
  refine SepWP.mono
    (ct1Sampled_epilogue_19324_placed s0 s5 _ hsp0_align hpc5 hrun5 hsp5 (htr5.trans htr4)) ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)),
    hsp_f, hcs_f, htr_f⟩

theorem copy_pre_entails_placed {A : RustAlloc} {F : ShaCompress}
    (s0 : State) (fsp stA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp) :
    ((stA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ chunkedCt1SampledBodyAt A (stA + 8#64) st) ∗
      memRegion outA v1RecvSize ∗
      memRegion fsp 4144 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      statesRecvSavedCells s0 ∗
      Rest ⊢
    ∃∗ d : Split928, ∃∗ sc : CopyScratchStack, ∃∗ k : EpilogueStoreStack,
      ⌜d.c0.w0 = polyEncoderTagVal st.sending_ct1⌝ ∗
      ⌜d.mid.length = 376⌝ ∗
      (split928At stA d ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ k.we8) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        memRegion (fsp + 576#64) 376 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
          memRegion outA chunkedStatesSize ∗
          memRegion (outA + 928#64) 32 ∗
          memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 976#64) 3168 ∗
          statesRecvSavedCells s0 ∗
          Rest)) := by
  refine Entails.trans (copy_pre_entails s0 fsp stA outA st Rest) ?_
  apply Entails.sepExists_elim; intro d
  apply Entails.sepExists_elim; intro sc
  apply Entails.sepExists_elim; intro k
  refine Entails.sepExists_right d (Entails.sepExists_right sc (Entails.sepExists_right k ?_))
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
theorem ct1Sampled_path_lt_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s3 : State) (fsp stA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc3 : s3.pc = (blkPl_332).base + 10500#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = fsp)
    (hx1_3 : s3.readReg64 .x1 = stA)
    (hx12_3 : s3.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19_3 : s3.readReg64 .x19 = outA)
    (hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s3
      (((stA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ chunkedCt1SampledBodyAt A (stA + 8#64) st) ∗
        memRegion outA v1RecvSize ∗
        memRegion fsp 4144 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled st }) ∗
          memRegion stA chunkedStatesSize ∗
          stackAt s0.sp statesRecvStackX ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.weaken_pre (copy_pre_entails_placed s0 fsp stA outA st Rest) ?_
  apply ProofLib.SepWP.exists_left; intro d
  apply ProofLib.SepWP.exists_left; intro sc
  apply ProofLib.SepWP.exists_left; intro k
  wp_focus_pure; intro htag
  wp_focus_pure; intro hmid
  refine SepWP.seq (ct1Sampled_copy_lt_placed hmemcpy s3 fsp stA outA d sc k _
    hmid hfsp_align hpc3 hrun3 hsp3 hx1_3 (hx12_3.trans htag.symm) hx19_3) ?_
  intro s4 P4 hpc4 hrun4 ⟨hP4, hregs4, hsp4, hx19_4, _, htr4⟩
  exact SepWP.weaken_pre hP4
    (ct1Sampled_store_and_epilogue_same_placed hmemcpy s0 s4 fsp stA outA k.w200 k.w208 st d
      (copyLtScratch sc d) Rest htag hmid hregs4 hfsp_align hsp0_align hfsp
      hpc4 hrun4 hsp4 hx19_4 (htr4.trans htr3))

set_option maxHeartbeats 800000 in
theorem ct1Sampled_path_other_from_12144_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s3 : State) (fsp stA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc3 : s3.pc = (blkPl_332).base + 12144#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = fsp)
    (hx1_3 : s3.readReg64 .x1 = stA)
    (hx12_3 : s3.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19_3 : s3.readReg64 .x19 = outA)
    (hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s3
      (((stA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ chunkedCt1SampledBodyAt A (stA + 8#64) st) ∗
        memRegion outA v1RecvSize ∗
        memRegion fsp 4144 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled st }) ∗
          memRegion stA chunkedStatesSize ∗
          stackAt s0.sp statesRecvStackX ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.weaken_pre (copy_pre_entails_placed s0 fsp stA outA st Rest) ?_
  apply ProofLib.SepWP.exists_left; intro d
  apply ProofLib.SepWP.exists_left; intro sc
  apply ProofLib.SepWP.exists_left; intro k
  wp_focus_pure; intro htag
  wp_focus_pure; intro hmid
  refine SepWP.seq (ct1Sampled_copy_other_placed hmemcpy s3 fsp stA outA d sc k _
    hmid hfsp_align hpc3 hrun3 hsp3 hx1_3 (hx12_3.trans htag.symm) hx19_3) ?_
  intro s4 P4 hpc4 hrun4 ⟨hP4, hregs4, hsp4, hx19_4, _, htr4⟩
  exact SepWP.weaken_pre hP4
    (ct1Sampled_store_and_epilogue_same_placed hmemcpy s0 s4 fsp stA outA k.w200 k.w208 st d
      (copyOtherScratch sc d) Rest htag hmid hregs4 hfsp_align hsp0_align hfsp
      hpc4 hrun4 hsp4 hx19_4 (htr4.trans htr3))

/-! ## 2. `recv_ek_chunk` Common Prefix (`+11404 -> +11508`) & Callee Call Helpers -/

theorem subroutine_ok_post_lscl [LibsignalPlacement] {α : Type} {prog : Program}
    {i : Nat} {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog entry
      { withLsCodeLoaded lsmpl spec with
        post := fun x s0 sf => ⌜LibsignalCodeLoaded lsmpl sf.mem⌝ ∗ spec.post x s0 sf } := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcl0, _⟩ := extract_withLsCodeLoaded hpre
  have hQL : prog.CodeLoaded s0.mem :=
    hprog.eq_blockProgram ▸ hcl0 i (Nat.lt_of_lt_of_le hi (by decide)) hunmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hsteps, hout, _⟩ := h.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hcl_sf : LibsignalCodeLoaded lsmpl sf.mem :=
    hcl0.of_keepsFrozen hsteps.keepsFrozen
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hq⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcl_sf, hq⟩
  · exact Or.inr hrest

theorem subroutine_ok_post_lscro [LibsignalPlacement] {α : Type} {prog : Program}
    {i : Nat} {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog entry
      { withLsCodeRoLoaded lsmpl spec with
        post := fun x s0 sf => ⌜LibsignalCodeRoLoaded lsmpl sf.mem⌝ ∗ spec.post x s0 sf } := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcro0, _⟩ := extract_withLsCodeRoLoaded hpre
  have hQL : prog.CodeLoaded s0.mem :=
    hprog.eq_blockProgram ▸ hcro0.1 i (Nat.lt_of_lt_of_le hi (by decide)) hunmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hsteps, hout, _⟩ := h.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hcro_sf : LibsignalCodeRoLoaded lsmpl sf.mem :=
    hcro0.of_keepsFrozen hsteps.keepsFrozen
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hq⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcro_sf, hq⟩
  · exact Or.inr hrest

theorem call_addChunkX_statesRecv_placed [LibsignalPlacement] {A : RustAlloc} {P_pan : Prop}
    {prog : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (addChunkSpecX A)))
    (decA chunkA : BitVec 64) (dec : PolyDecoder) (chunk : Chunk)
    (hsorted : PolyDecoderStrictSorted dec)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = decA)
    (hx1 : s.readReg64 Reg.x1 = chunkA)
    (hsplit : P = (polyDecoderAt A decA dec ∗ chunkAt chunkA chunk ∗
      A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      LibsignalCodeLoaded lsmpl sf.mem →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP prog next_pc sf
        ((polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame)
        (fun sm Pm =>
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))))
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) := by
  have hcall_cl := subroutine_ok_post_lscl hcall hi hunmut
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall_cl (x := ⟨decA, chunkA, dec, chunk⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, addChunkSpecX]
    rw [hsp]
    have hm' : s.mem ⊨ ⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗
        ⌜s.readReg64 .x0 = decA ∧ s.readReg64 .x1 = chunkA ∧ PolyDecoderStrictSorted dec⌝ ∗
        ((polyDecoderAt A decA dec ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame ∗ R') := by
      rw [satisfies_pure_sepConj]
      exact ⟨hcl, by rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, hx1, hsorted⟩, by simpa [sepConj_assoc] using hm⟩⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm'
  · dsimp only [withLsCodeLoaded, addChunkSpecX] at hmem
    exact Satisfies.mono (sepConj_mono_left (onPanic_alloc_entails_statesRecv htrace.1)) hmem
  · dsimp only [withLsCodeLoaded, addChunkSpecX]
    rw [hsp]
    have hpost_reord :
        (⌜LibsignalCodeLoaded lsmpl sf.mem⌝ ∗
          ⌜sf.trace = s.trace ∧ PolyDecoderStrictSorted (addChunkTotal dec chunk)⌝ ∗
          polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame =
        ⌜LibsignalCodeLoaded lsmpl sf.mem⌝ ∗
        ⌜sf.trace = s.trace ∧ PolyDecoderStrictSorted (addChunkTotal dec chunk)⌝ ∗
        ((polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame) := by ac_rfl
    rw [hpost_reord]
    refine SepWPp.pure_left fun hcl_sf => ?_
    refine SepWPp.pure_left fun ⟨htr, hsorted'⟩ => ?_
    apply SepWPp.of_sepWP (mid := next_pc)
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hcl_sf hsorted'

theorem call_addChunkX_statesRecv_cro_placed [LibsignalPlacement] {A : RustAlloc} {P_pan : Prop}
    {prog : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (addChunkSpecX A)))
    (decA chunkA : BitVec 64) (dec : PolyDecoder) (chunk : Chunk)
    (hsorted : PolyDecoderStrictSorted dec)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = decA)
    (hx1 : s.readReg64 Reg.x1 = chunkA)
    (hsplit : P = (polyDecoderAt A decA dec ∗ chunkAt chunkA chunk ∗
      A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP prog next_pc sf
        ((polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame)
        (fun sm Pm =>
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))))
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) := by
  have hcall_cro := subroutine_ok_post_lscro
    (Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcall) hi hunmut
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall_cro (x := ⟨decA, chunkA, dec, chunk⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeRoLoaded, addChunkSpecX]
    rw [hsp]
    have hm' : s.mem ⊨ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝ ∗
        ⌜s.readReg64 .x0 = decA ∧ s.readReg64 .x1 = chunkA ∧ PolyDecoderStrictSorted dec⌝ ∗
        ((polyDecoderAt A decA dec ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame ∗ R') := by
      rw [satisfies_pure_sepConj]
      exact ⟨hcro, by rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, hx1, hsorted⟩, by simpa [sepConj_assoc] using hm⟩⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm'
  · dsimp only [withLsCodeRoLoaded, addChunkSpecX] at hmem
    exact Satisfies.mono (sepConj_mono_left (onPanic_alloc_entails_statesRecv htrace.1)) hmem
  · dsimp only [withLsCodeRoLoaded, addChunkSpecX]
    rw [hsp]
    have hpost_reord :
        (⌜LibsignalCodeRoLoaded lsmpl sf.mem⌝ ∗
          ⌜sf.trace = s.trace ∧ PolyDecoderStrictSorted (addChunkTotal dec chunk)⌝ ∗
          polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame =
        ⌜LibsignalCodeRoLoaded lsmpl sf.mem⌝ ∗
        ⌜sf.trace = s.trace ∧ PolyDecoderStrictSorted (addChunkTotal dec chunk)⌝ ∗
        ((polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame) := by ac_rfl
    rw [hpost_reord]
    refine SepWPp.pure_left fun hcro_sf => ?_
    refine SepWPp.pure_left fun ⟨htr, hsorted'⟩ => ?_
    apply SepWPp.of_sepWP (mid := next_pc)
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hcro_sf hsorted'

theorem call_decodedMessage_statesRecv_placed [LibsignalPlacement] {A : RustAlloc} {P_pan : Prop}
    {prog : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec A)))
    (outA decA : BitVec 64) (dec : PolyDecoder) (outMsg : Option Bytes)
    (hsorted : PolyDecoderStrictSorted dec)
    (hdec : spqrPolyApi.decoded_message dec = .ok outMsg)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx8 : s.readReg64 Reg.x8 = outA)
    (hx0 : s.readReg64 Reg.x0 = decA)
    (hsplit : P = (memRegion outA 24 ∗ polyDecoderAt A decA dec ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWP prog next_pc sf
        ((optVecU8At A outA outMsg ∗ polyDecoderAt A decA dec ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame)
        (fun sm Pm =>
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))))
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) := by
  have hcall_cro := subroutine_ok_post_lscro hcall hi hunmut
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall_cro (x := ⟨outA, decA, dec, outMsg⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeRoLoaded, polyDecoderDecodedMessagePlacedSpec]
    rw [hsp]
    have hm' : s.mem ⊨ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝ ∗
        ⌜s.readReg64 .x8 = outA ∧ s.readReg64 .x0 = decA ∧
          PolyDecoderStrictSorted dec ∧ spqrPolyApi.decoded_message dec = .ok outMsg⌝ ∗
        ((memRegion outA 24 ∗ polyDecoderAt A decA dec ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame ∗ R') := by
      rw [satisfies_pure_sepConj]
      exact ⟨hcro, by rw [satisfies_pure_sepConj]; exact ⟨⟨hx8, hx0, hsorted, hdec⟩, by simpa [sepConj_assoc] using hm⟩⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm'
  · dsimp only [withLsCodeRoLoaded, polyDecoderDecodedMessagePlacedSpec] at hmem
    exact Satisfies.mono (sepConj_mono_left (onPanic_alloc_entails_statesRecv htrace.1)) hmem
  · dsimp only [withLsCodeRoLoaded, polyDecoderDecodedMessagePlacedSpec]
    rw [hsp]
    have hpost_reord :
        (⌜LibsignalCodeRoLoaded lsmpl sf.mem⌝ ∗
          ⌜sf.trace = s.trace⌝ ∗
          optVecU8At A outA outMsg ∗ polyDecoderAt A decA dec ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame =
        ⌜LibsignalCodeRoLoaded lsmpl sf.mem⌝ ∗
        ⌜sf.trace = s.trace⌝ ∗
        ((optVecU8At A outA outMsg ∗ polyDecoderAt A decA dec ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame) := by ac_rfl
    rw [hpost_reord]
    refine SepWPp.pure_left fun hcro_sf => ?_
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP (mid := next_pc)
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hcro_sf.1

theorem call_sendCt2_statesRecv_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {P_pan : Prop} {prog : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (Unchunked.unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K)))
    (outA stA : BitVec 64)
    (st : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) (ct2 : Bytes) (mac : Mac)
    (hsc : st.send_ct2 K = .ok (outUc, ct2, mac))
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = stA)
    (hsplit : P = (memRegion outA 104 ∗ unchunkedCt1SentEkReceivedAt A stA st ∗
      Unchunked.unchunkedSendCt2PlacedRoAt ∗ A.pool ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWP prog next_pc sf
        ((unchunkedCt2SentAt A outA outUc ∗ vecU8 A (outA + 56#64) ct2 ∗
          vecU8 A (outA + 80#64) mac ∗ memRegion stA 128 ∗
          Unchunked.unchunkedSendCt2PlacedRoAt ∗ A.pool ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
        (fun sm Pm =>
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))))
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) := by
  have hcall_cl := subroutine_ok_post_lscl hcall hi hunmut
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall_cl (x := ⟨outA, stA, st, outUc, ct2, mac⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, Unchunked.unchunkedCt1SentEkReceivedSendCt2PlacedSpec]
    rw [hsp]
    have hm' : s.mem ⊨ ⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗
        ⌜s.readReg64 .x0 = outA ∧ s.readReg64 .x1 = stA ∧
          st.send_ct2 K = .ok (outUc, ct2, mac)⌝ ∗
        ((memRegion outA 104 ∗ unchunkedCt1SentEkReceivedAt A stA st ∗
          Unchunked.unchunkedSendCt2PlacedRoAt ∗ A.pool ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame ∗ R') := by
      rw [satisfies_pure_sepConj]
      exact ⟨hcl, by rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, hx1, hsc⟩, by simpa [sepConj_assoc] using hm⟩⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm'
  · dsimp only [withLsCodeLoaded, Unchunked.unchunkedCt1SentEkReceivedSendCt2PlacedSpec] at hmem
    exact Satisfies.mono (sepConj_mono_left (onPanic_alloc_entails_statesRecv htrace.1)) hmem
  · dsimp only [withLsCodeLoaded, Unchunked.unchunkedCt1SentEkReceivedSendCt2PlacedSpec]
    rw [hsp]
    have hpost_reord :
        (⌜LibsignalCodeLoaded lsmpl sf.mem⌝ ∗
          ⌜sf.trace = s.trace⌝ ∗
          unchunkedCt2SentAt A outA outUc ∗ vecU8 A (outA + 56#64) ct2 ∗
          vecU8 A (outA + 80#64) mac ∗ memRegion stA 128 ∗
          Unchunked.unchunkedSendCt2PlacedRoAt ∗ A.pool ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame =
        ⌜LibsignalCodeLoaded lsmpl sf.mem⌝ ∗
        ⌜sf.trace = s.trace⌝ ∗
        ((unchunkedCt2SentAt A outA outUc ∗ vecU8 A (outA + 56#64) ct2 ∗
          vecU8 A (outA + 80#64) mac ∗ memRegion stA 128 ∗
          Unchunked.unchunkedSendCt2PlacedRoAt ∗ A.pool ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame) := by ac_rfl
    rw [hpost_reord]
    refine SepWPp.pure_left fun hcl_sf => ?_
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP (mid := next_pc)
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hcl_sf

theorem call_sendCt2Encoder_statesRecv_placed [LibsignalPlacement] {A : RustAlloc} {P_pan : Prop}
    {prog : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (sendCt2EncoderSpec A)))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = ct2Ptr)
    (hx2 : s.readReg64 Reg.x2 = BitVec.ofNat 64 ct2.length)
    (hx3 : s.readReg64 Reg.x3 = macPtr)
    (hx4 : s.readReg64 Reg.x4 = BitVec.ofNat 64 mac.length)
    (hsplit : P = (memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
      A.pool ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWP prog next_pc sf
        ((polyEncoderAt A outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
        (fun sm Pm =>
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))))
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) := by
  have hcall_cl := subroutine_ok_post_lscl hcall hi hunmut
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall_cl (x := ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, sendCt2EncoderSpec]
    rw [hsp]
    have hm' : s.mem ⊨ ⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗
        ⌜s.readReg64 .x0 = outA ∧ s.readReg64 .x1 = ct2Ptr ∧
          s.readReg64 .x2 = BitVec.ofNat 64 ct2.length ∧ s.readReg64 .x3 = macPtr ∧
          s.readReg64 .x4 = BitVec.ofNat 64 mac.length ∧ ct2Ptr ≠ 0#64 ∧ macPtr ≠ 0#64 ∧
          Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok enc⌝ ∗
        ((memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame ∗ R') := by
      rw [satisfies_pure_sepConj]
      exact ⟨hcl, by rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hct2_ptr, hmac_ptr, henc⟩, by simpa [sepConj_assoc] using hm⟩⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm'
  · dsimp only [withLsCodeLoaded, sendCt2EncoderSpec] at hmem
    exact Satisfies.mono (sepConj_mono_left (onPanic_alloc_entails_statesRecv htrace.1)) hmem
  · dsimp only [withLsCodeLoaded, sendCt2EncoderSpec]
    rw [hsp]
    have hpost_reord :
        (⌜LibsignalCodeLoaded lsmpl sf.mem⌝ ∗
          ⌜sf.trace = s.trace⌝ ∗
          polyEncoderAt A outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame =
        ⌜LibsignalCodeLoaded lsmpl sf.mem⌝ ∗
        ⌜sf.trace = s.trace⌝ ∗
        ((polyEncoderAt A outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame) := by ac_rfl
    rw [hpost_reord]
    refine SepWPp.pure_left fun hcl_sf => ?_
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP (mid := next_pc)
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hcl_sf

set_option maxHeartbeats 1200000 in
theorem ct1Sampled_recv_ek_prefix_copy_placed [LibsignalPlacement]
    {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s_in : State) (fsp stA ve8 : BitVec 64)
    (c_uc : Words16) (dec : PolyDecoder) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11404#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = stA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 11472#64) s_in
      (wordsAt (stA + 400#64) c_uc.toList ∗
        polyDecoderAt A (stA + 528#64) dec ∗
        ((fsp + 232#64) ↦₆₄ ve8) ∗
        memRegion (fsp + 2752#64) 400 ∗
        memRegion (fsp + 3696#64) 128 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          wordsAt (stA + 400#64) c_uc.toList ∗
          wordsAt (fsp + 3696#64) c_uc.toList ∗
          polyDecoderAt A (fsp + 2752#64) dec ∗
          ((fsp + 232#64) ↦₆₄ stA) ∗
          memRegion (stA + 528#64) 400 ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  have hrel_dec : Relocatable 400 (fun a => polyDecoderAt A a dec) :=
    Relocatable.of_polyDecoderAt A dec
  have hpre :
      wordsAt (stA + 400#64) c_uc.toList ∗
        polyDecoderAt A (stA + 528#64) dec ∗
        ((fsp + 232#64) ↦₆₄ ve8) ∗
        memRegion (fsp + 2752#64) 400 ∗
        memRegion (fsp + 3696#64) 128 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest ⊢
      ∃∗ c_dst : Words16, ∃∗ bs_dec : List (BitVec 8),
        ⌜bs_dec.length = 400⌝ ∗
        wordsAt (stA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_dst.toList ∗
        ((fsp + 232#64) ↦₆₄ ve8) ∗
        ((stA + 528#64) ↦ₛ bs_dec) ∗
        memRegion (fsp + 2752#64) 400 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (relocatedHeap (fun a => polyDecoderAt A a dec) bs_dec ∗
          Rest) := by
    refine Entails.trans (sepConj_mono_right
      (sepConj_mono (hrel_dec (stA + 528#64))
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (memRegion_128_entails_words16 (fsp + 3696#64))))))) ?_
    simp only [sepExists_sepConj_left]
    simp only [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs_dec
    apply Entails.sepExists_elim; intro c_dst
    refine Entails.sepExists_right c_dst (Entails.sepExists_right bs_dec ?_)
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro c_dst
  apply ProofLib.SepWP.exists_left; intro bs_dec
  wp_focus_pure; intro hlen_dec
  subst hsp hx1
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec :=
    spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_in.sp
  refine SepWP.mono (post := fun sf Pf =>
      (Pf ⊢
        wordsAt (s_in.readReg64 .x1 + 400#64) c_uc.toList ∗
        wordsAt (s_in.sp + 3696#64) c_uc.toList ∗
        ((s_in.sp + 2752#64) ↦ₛ bs_dec) ∗
        ((s_in.sp + 232#64) ↦₆₄ s_in.readReg64 .x1) ∗
        ((s_in.readReg64 .x1 + 528#64) ↦ₛ bs_dec) ∗
        stackAt s_in.sp statesRecvCalleeStackX ∗
        (relocatedHeap (fun a => polyDecoderAt A a dec) bs_dec ∗ Rest)) ∧
      sf.sp = s_in.sp ∧
      sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
      sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
      sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
      sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
      sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
      sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
      sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
      sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
      TraceCalleeSaved sf s_in) ?_ (fun sf Pf _ _ ⟨hPf, hrest⟩ => ⟨Entails.trans hPf ?_, hrest⟩)
  · rw [hsplit, show memRegion (s_in.sp + 2752#64) 400 = memRegion (s_in.sp + 2752#64) bs_dec.length by rw [hlen_dec]]
    dsimp only [lsProg_332, lsρ, spqrMemcpySym, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
    dsimp only [Words16.toList, sessionMemcpySpec, allocHookStack] at hmemcpy_raw ⊢
    simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    wp_call hmemcpy_raw (s_in.sp + 2752#64, s_in.readReg64 .x1 + 528#64, bs_dec)
    wp_done
  · have hdec := relocatedHeap_recompose (fun a => polyDecoderAt A a dec) bs_dec (s_in.sp + 2752#64)
    have hdec_in : ((s_in.readReg64 .x1 + 528#64) ↦ₛ bs_dec) ⊢
        memRegion (s_in.readReg64 .x1 + 528#64) 400 := by
      rw [← hlen_dec]; exact ProofLib.pointsToBytes_entails_memRegion _ _
    refine Entails.trans (Entails.of_eq (show _ =
      wordsAt (s_in.readReg64 .x1 + 400#64) c_uc.toList ∗
      wordsAt (s_in.sp + 3696#64) c_uc.toList ∗
      (((s_in.sp + 2752#64) ↦ₛ bs_dec) ∗
        relocatedHeap (fun a => polyDecoderAt A a dec) bs_dec) ∗
      ((s_in.sp + 232#64) ↦₆₄ s_in.readReg64 .x1) ∗
      ((s_in.readReg64 .x1 + 528#64) ↦ₛ bs_dec) ∗
      stackAt s_in.sp statesRecvCalleeStackX ∗
      Rest by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hdec (sepConj_mono_right (sepConj_mono_left hdec_in))))

theorem ct1Sampled_recv_ek_decode_branch_none_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s_in : State) (fsp : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11496#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 13968#64) s_in
      (optVecU8At A (fsp + 3832#64) none ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ memRegion (fsp + 3832#64) 24 ∗ Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hfold := optVecU8At_none_entails_memRegion_24 A (s_in.sp + 3832#64)
  dsimp only [lsProg_332, optVecU8At, noneCap, BitVec.ofNat_eq_ofNat] at hpc hfold ⊢
  wp_steps
  refine SepWP.focus_weaken hfold (by sep_focus) ?_
  wp_done

theorem ct1Sampled_recv_ek_decode_branch_some_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s_in : State) (fsp : BitVec 64) (decoded : Bytes) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11496#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 11508#64) s_in
      (optVecU8At A (fsp + 3832#64) (some decoded) ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ vecU8 A (fsp + 3832#64) decoded ∗ Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  dsimp only [optVecU8At]
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecU8_entails_slice_and_tail A (s_in.sp + 3832#64) decoded)) ?_
  wp_simp_pre [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro cap
  apply ProofLib.SepWP.exists_left; intro ptr
  wp_focus_pure; rintro ⟨hle, hcap_lt, hptr_ne⟩
  have hcmn := Recv.cap_add_one_beq_zero_false hcap_lt
  have hrecomb := vecU8_of_slice_and_tail A (s_in.sp + 3832#64) cap ptr decoded hle hcap_lt hptr_ne
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  refine SepWP.focus_weaken hrecomb (by sep_focus) ?_
  wp_done

set_option maxHeartbeats 1200000 in
theorem ct1Sampled_recv_ek_add_and_decode_placed [LibsignalPlacement]
    {A : RustAlloc} {P_pan : Prop}
    {ext : String → Option (State → State)}
    (hadd_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX A)))
    (hdec_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec A)))
    (s0 s_in : State) (fsp msgA : BitVec 64)
    (dec : PolyDecoder) (chunk : Chunk) (outMsg : Option Bytes)
    (hsorted : PolyDecoderStrictSorted dec)
    (hdec_msg : spqrPolyApi.decoded_message (addChunkTotal dec chunk) = .ok outMsg)
    (Rest R : SepProp)
    {post : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11472#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx24 : s_in.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s_in s0)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_332).base + 11496#64 →
      sf.status = .Running →
      sf.sp = fsp →
      sf.readReg64 .x19 = s_in.readReg64 .x19 →
      sf.readReg64 .x20 = s_in.readReg64 .x20 →
      sf.readReg64 .x21 = s_in.readReg64 .x21 →
      sf.readReg64 .x22 = s_in.readReg64 .x22 →
      sf.readReg64 .x23 = s_in.readReg64 .x23 →
      sf.readReg64 .x24 = msgA →
      sf.readReg64 .x28 = s_in.readReg64 .x28 →
      sf.readReg64 .x29 = s_in.readReg64 .x29 →
      TraceCalleeSaved sf s0 →
      LibsignalCodeLoaded lsmpl sf.mem →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP (lsProg_332 (Rust.withPanics ext))
        ((blkPl_332).base + 11496#64) sf
        (optVecU8At A (fsp + 3832#64) outMsg ∗
          polyDecoderAt A (fsp + 2752#64) (addChunkTotal dec chunk) ∗
          chunkAt (msgA + 10#64) chunk ∗
          statesRecvRoPlacedAt ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest)
        (fun sm Pm =>
          SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)))) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_419).base) s_in
      (memRegion (fsp + 3832#64) 24 ∗
        polyDecoderAt A (fsp + 2752#64) dec ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoPlacedAt ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sm Pm =>
        SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) := by
  subst hsp hx24
  have hadd_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      ((blkPl_419).base) (withLsCodeLoaded lsmpl (addChunkSpecX A)) := hadd_call
  have hdec_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      ((blkPl_418).base) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec A)) := hdec_call
  have hsplit_add := stackAt_statesRecvCallee_eq_addChunk s_in.sp
  have hsplit_dec := stackAt_statesRecvCallee_eq_polyDecodedMessage s_in.sp
  dsimp only [lsProg_332, statesRecvRoPlacedAt,
    RecvCt2Chunk.polyDecodedMessageStackX, BitVec.ofNat_eq_ofNat]
    at hpc hadd_raw hdec_raw hsplit_add hsplit_dec hnext ⊢
  rw [hsplit_add]
  wp_steps
  refine call_addChunkX_statesRecv_cro_placed (P_pan := P_pan) hadd_raw
    (s_in.sp + 2752#64) (s_in.readReg64 .x24 + 10#64) dec chunk hsorted
    (s0 := s0) (ret_pc := (blkPl_332).base + 11484#64) (next_pc := (blkPl_418).base) (sp_call := s_in.sp)
    (by simpa only [State.mem, arm64_norm] using hcro)
    (by simp only [State.pc, arm64_norm]; rfl) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [TraceCalleeSaved, arm64_norm, htr.1, htr.2])
    (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, Reg.x24, arm64_norm])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 hcro1 hsorted' => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, _⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1
  refine SepWP.focus_weaken (Entails.of_eq hsplit_add.symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq hsplit_dec) (by sep_focus) ?_
  wp_steps
  refine call_decodedMessage_statesRecv_placed (P_pan := P_pan) hdec_raw
    (s_in.sp + 3832#64) (s_in.sp + 2752#64) (addChunkTotal dec chunk) outMsg hsorted' hdec_msg
    (s0 := s0) (ret_pc := (blkPl_332).base + 11496#64) (next_pc := (blkPl_332).base + 11496#64) (sp_call := s_in.sp)
    (by simpa only [State.mem, arm64_norm] using hcro1)
    (by simp only [State.pc, arm64_norm]; rfl) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [TraceCalleeSaved, arm64_norm, htr1.1, htr1.2])
    (by simp only [Reg.x8, arm64_norm, hsp1])
    (by simp only [Reg.x0, arm64_norm, hsp1])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 hcl2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, _⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx28_1, hfp_1]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx28_2 hfp_2
  refine SepWP.focus_weaken (Entails.of_eq hsplit_dec.symm) (by sep_focus) ?_
  exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sf2 hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx28_2 hfp_2 htr2 hcl2 hsorted')

end LibsignalBinary.Proofs.SpqrV1.States.Recv

namespace CryptoVerification.SpqrV1.States.Recv

export LibsignalBinary.Proofs.SpqrV1.States.Recv (
  ct1Sampled_msg_kind_check_other_placed
  ct1Sampled_msg_kind_check_ek_placed
  ct1Sampled_msg_kind_check_ekCt1Ack_placed
  ct1Sampled_store_and_epilogue_same_placed
  copy_pre_entails_placed
  ct1Sampled_path_lt_placed
  ct1Sampled_path_other_from_12144_placed
  subroutine_ok_post_lscl
  subroutine_ok_post_lscro
  call_addChunkX_statesRecv_placed
  call_addChunkX_statesRecv_cro_placed
  call_decodedMessage_statesRecv_placed
  call_sendCt2_statesRecv_placed
  call_sendCt2Encoder_statesRecv_placed
  ct1Sampled_recv_ek_prefix_copy_placed
  ct1Sampled_recv_ek_decode_branch_none_placed
  ct1Sampled_recv_ek_decode_branch_some_placed
  ct1Sampled_recv_ek_add_and_decode_placed
)

end CryptoVerification.SpqrV1.States.Recv
