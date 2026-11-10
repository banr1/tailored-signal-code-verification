/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofX
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEk
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Sampled` Arm, Part 3: Payload Dispatch & `recv_ek_chunk` Prefix

Message payload discriminant checks (`+7052`), unchanged return paths (`Path 2` and `Path 3`),
and the common `recv_ek_chunk` prefix (`+11404 -> +11508`, calling `PolyDecoder::add_chunk` and
`decoded_message`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States

set_option maxRecDepth 400000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv")
  (ls_stub% "memcpy")

/-! ## 1. Message Kind Dispatch (`+7052`) & Unchanged Return Paths -/

set_option maxHeartbeats 2000000 in
/-- Message payload discriminant check (`+7052 -> +12144`, `0x56fe0..0x56ff4`) when
    `msg_tag ≠ 2#8 ∧ msg_tag ≠ 3#8` (neither `.ek` nor `.ekCt1Ack`). -/
theorem ct1Sampled_msg_kind_check_other
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s_in : State) (msgA : BitVec 64) (msg_tag : BitVec 8) (Rest : SepProp)
    (hne2 : (BitVec.zeroExtend 32 msg_tag == 2#32) = false)
    (hne3 : (BitVec.zeroExtend 32 msg_tag != 3#32) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 7052#64)
    (hrun : s_in.status = .Running)
    (hx24 : s_in.readReg64 .x24 = msgA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 12144#64) s_in
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
  states_recv_fetches_range b (Rust.withPanics ext) 7052 20
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_steps
  wp_done

set_option maxHeartbeats 2000000 in
/-- Message payload discriminant check (`+7052 -> +11404`, `0x56fe0 -> 0x580d8 -> 0x580e0`) when
    `msg_tag = 2#8` (`MessagePayload.ek`). Sets `x23 = x12` and `x22 = 0#64`. -/
theorem ct1Sampled_msg_kind_check_ek
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s_in : State) (msgA : BitVec 64) (Rest : SepProp)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 7052#64)
    (hrun : s_in.status = .Running)
    (hx24 : s_in.readReg64 .x24 = msgA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11404#64) s_in
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
  states_recv_fetches_range b (Rust.withPanics ext) 7052 12
  states_recv_fetches_range b (Rust.withPanics ext) 11396 8
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_steps
  wp_done

set_option maxHeartbeats 2000000 in
/-- Message payload discriminant check (`+7052 -> +11404`, `0x56fe0 -> 0x56ffc -> 0x580e0`) when
    `msg_tag = 3#8` (`MessagePayload.ekCt1Ack`). Sets `x23 = x12` and `x22 = 1#64`. -/
theorem ct1Sampled_msg_kind_check_ekCt1Ack
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s_in : State) (msgA : BitVec 64) (Rest : SepProp)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 7052#64)
    (hrun : s_in.status = .Running)
    (hx24 : s_in.readReg64 .x24 = msgA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11404#64) s_in
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
  states_recv_fetches_range b (Rust.withPanics ext) 7052 32
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_steps
  wp_done

set_option maxHeartbeats 2000000 in
/-- Shared `+18996 -> s0.x30` epilogue for paths that return `Ok { key := none, state := .ct1Sampled st }`
    with scratch stack `sc' : CopyScratchStack`. -/
theorem ct1Sampled_store_and_epilogue_same
    {b : BitVec 64} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
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
    (hpc4 : s4.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64)
    (hrun4 : s4.status = .Running)
    (hsp4 : s4.sp = fsp)
    (hx19_4 : s4.readReg64 .x19 = outA)
    (htr4 : TraceCalleeSaved s4 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s4
      (split928At stA d ∗
        copyScratchStackAt fsp sc' ∗
        epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap w200 w208) ∗
        epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap w200 w208) ∗
        (relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
          memRegion outA chunkedStatesSize ∗
          memRegion (outA + 928#64) 32 ∗
          memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 976#64) 3168 ∗
          stackAt fsp statesRecvCalleeStackX ∗
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
        (relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
          memRegion outA chunkedStatesSize ∗
          memRegion (outA + 928#64) 32 ∗
          memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 976#64) 3168 ∗
          stackAt fsp statesRecvCalleeStackX ∗
          statesRecvSavedCells s0 ∗
          Rest) ⊢
      epilogueStoreStackPart1At fsp k' ∗
      epilogueStoreStackPart2At fsp k' ∗
      memRegion outA chunkedStatesSize ∗
      memRegion (outA + 928#64) 32 ∗
      (split928At stA d ∗
        relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
        copyScratchStackAt fsp sc' ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 3168 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗
        Rest) := Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hP4' ?_
  refine SepWP.seq (ct1Sampled_epilogue_store hmemcpy s4 fsp outA k' _
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
    (ct1Sampled_epilogue_19324 s0 s5 _ hsp0_align hpc5 hrun5 hsp5 (htr5.trans htr4)) ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)),
    hsp_f, hcs_f, htr_f⟩

set_option maxHeartbeats 2000000 in
theorem copy_pre_entails {A : RustAlloc} {F : ShaCompress}
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
        (relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
          memRegion outA chunkedStatesSize ∗
          memRegion (outA + 928#64) 32 ∗
          memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 976#64) 3168 ∗
          stackAt fsp statesRecvCalleeStackX ∗
          statesRecvSavedCells s0 ∗
          Rest)) := by
  rw [memRegion_out_960_split_states_key outA]
  refine Entails.trans (sepConj_mono (chunkedCt1SampledAt_extract_split928 A stA st)
    (sepConj_mono_right (sepConj_mono_left
      (memRegion_4144_entails_copyScratch_and_epilogueStack fsp)))) ?_
  simp only [sepExists_sepConj_left]
  simp only [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d
  apply Entails.sepExists_elim; intro sc
  apply Entails.sepExists_elim; intro k
  refine Entails.sepExists_right d (Entails.sepExists_right sc (Entails.sepExists_right k ?_))
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 2000000 in
/-- Complete Path 2 (`msg.epoch < st.uc.epoch`, `+10500 -> s0.x30`). -/
theorem ct1Sampled_path_lt
    {b : BitVec 64} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s3 : State) (fsp stA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc3 : s3.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 10500#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = fsp)
    (hx1_3 : s3.readReg64 .x1 = stA)
    (hx12_3 : s3.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19_3 : s3.readReg64 .x19 = outA)
    (hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s3
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
  refine SepWP.weaken_pre (copy_pre_entails s0 fsp stA outA st Rest) ?_
  apply ProofLib.SepWP.exists_left; intro d
  apply ProofLib.SepWP.exists_left; intro sc
  apply ProofLib.SepWP.exists_left; intro k
  wp_focus_pure; intro htag
  wp_focus_pure; intro hmid
  refine SepWP.seq (ct1Sampled_copy_lt hmemcpy s3 fsp stA outA d sc k _
    hmid hfsp_align hpc3 hrun3 hsp3 hx1_3 (hx12_3.trans htag.symm) hx19_3) ?_
  intro s4 P4 hpc4 hrun4 ⟨hP4, hregs4, hsp4, hx19_4, _, htr4⟩
  exact SepWP.weaken_pre hP4
    (ct1Sampled_store_and_epilogue_same hmemcpy s0 s4 fsp stA outA k.w200 k.w208 st d
      (copyLtScratch sc d) Rest htag hmid hregs4 hfsp_align hsp0_align hfsp
      hpc4 hrun4 hsp4 hx19_4 (htr4.trans htr3))

set_option maxHeartbeats 2000000 in
/-- Complete Path 3 from `+12144` (`msg.epoch == st.uc.epoch` non-`ek`/`ekCt1Ack`, `+12144 -> s0.x30`). -/
theorem ct1Sampled_path_other_from_12144
    {b : BitVec 64} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s3 : State) (fsp stA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc3 : s3.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 12144#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = fsp)
    (hx1_3 : s3.readReg64 .x1 = stA)
    (hx12_3 : s3.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19_3 : s3.readReg64 .x19 = outA)
    (hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s3
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
  refine SepWP.weaken_pre (copy_pre_entails s0 fsp stA outA st Rest) ?_
  apply ProofLib.SepWP.exists_left; intro d
  apply ProofLib.SepWP.exists_left; intro sc
  apply ProofLib.SepWP.exists_left; intro k
  wp_focus_pure; intro htag
  wp_focus_pure; intro hmid
  refine SepWP.seq (ct1Sampled_copy_other hmemcpy s3 fsp stA outA d sc k _
    hmid hfsp_align hpc3 hrun3 hsp3 hx1_3 (hx12_3.trans htag.symm) hx19_3) ?_
  intro s4 P4 hpc4 hrun4 ⟨hP4, hregs4, hsp4, hx19_4, _, htr4⟩
  exact SepWP.weaken_pre hP4
    (ct1Sampled_store_and_epilogue_same hmemcpy s0 s4 fsp stA outA k.w200 k.w208 st d
      (copyOtherScratch sc d) Rest htag hmid hregs4 hfsp_align hsp0_align hfsp
      hpc4 hrun4 hsp4 hx19_4 (htr4.trans htr3))

/-! ## 2. `recv_ek_chunk` Common Prefix (`0x580e0 -> 0x58148`, `+11404 -> +11508`) -/

theorem words16_entails_memRegion_128 (a : BitVec 64) (c : Words16) :
    wordsAt a c.toList ⊢ memRegion a 128 := by
  have hlen : (wordsBytes c.toList).length = 128 := by
    rw [length_wordsBytes, Words16.toList_length]
  rw [wordsAt_eq_pointsToBytes]
  have h := pointsToBytes_entails_memRegion a (wordsBytes c.toList)
  rwa [hlen] at h

theorem Relocatable.extract_128 {F : BitVec 64 → SepProp} (hrel : Relocatable 128 F)
    (a : BitVec 64) :
    F a ⊢ ∃∗ c : Words16,
      wordsAt a c.toList ∗ relocatedHeap F (wordsBytes c.toList) := by
  refine Entails.trans (hrel a) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  obtain ⟨c, rfl⟩ := exists_words16_of_length_128 hlen
  refine Entails.sepExists_right c ?_
  rw [← wordsAt_eq_pointsToBytes]
  exact Entails.refl _

theorem Relocatable.reconstruct_128 (F : BitVec 64 → SepProp)
    (a : BitVec 64) (c : Words16) :
    wordsAt a c.toList ∗ relocatedHeap F (wordsBytes c.toList) ⊢ F a := by
  rw [wordsAt_eq_pointsToBytes]
  exact relocatedHeap_recompose F (wordsBytes c.toList) a

theorem addChunk_ok_at_statesRecv {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : AddChunkOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 94156#64)
      ((addChunkSpecX A).inImage img) := by
  refine sub_ok_at_statesRecv ?_ h
  dsimp only [tripleRatchetProgAtExt, statesRecvName, addChunkName]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv",
      ls_lemma% fnOff "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk"]
  bv_omega

theorem addChunkX_ok_at_statesRecv {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 94156#64)
      (addChunkSpecX A) := by
  refine sub_ok_at_statesRecv ?_ (addChunkSpecX_of_addChunkSpec (add_chunk_ok_ext hA))
  dsimp only [tripleRatchetProgAtExt, statesRecvName, addChunkName]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv",
      ls_lemma% fnOff "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk"]
  bv_omega

@[local arm64_norm, local wp_norm]
theorem sp_sub_4240_add_2752 (sp : BitVec 64) : (sp - 4240#64) + 2752#64 = sp - 1488#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_4240_add_3696 (sp : BitVec 64) : (sp - 4240#64) + 3696#64 = sp - 544#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_4240_add_3832 (sp : BitVec 64) : (sp - 4240#64) + 3832#64 = sp - 408#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_4240_add_3840 (sp : BitVec 64) : (sp - 4240#64) + 3840#64 = sp - 400#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_4240_add_3848 (sp : BitVec 64) : (sp - 4240#64) + 3848#64 = sp - 392#64 := by bv_omega

theorem onPanic_alloc_entails_statesRecv {P : Prop} {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜(P ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  unfold allocFailedIn
  rw [htr, sepConj_assoc]
  refine Entails.pure_left fun ⟨haf, hpref⟩ => ?_
  exact Entails.pure_right ⟨Or.inr haf, hpref⟩ (entails_anyHeap _)

/-- Framed call rule for `addChunkSpecX A` (`0x6c420`) inside `States::recv`. -/
theorem call_addChunkX_statesRecv {A : RustAlloc} {P_pan : Prop}
    {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (addChunkSpecX A))
    (decA chunkA : BitVec 64) (dec : PolyDecoder) (chunk : Chunk)
    (hsorted : PolyDecoderStrictSorted dec)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
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
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP prog next_pc sf
        ((polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame)
        (fun sm Pm =>
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)))) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨decA, chunkA, dec, chunk⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [addChunkSpecX]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hsorted⟩, hm⟩
  · dsimp only [addChunkSpecX] at hmem
    exact Satisfies.mono (sepConj_mono_left (onPanic_alloc_entails_statesRecv htrace.1)) hmem
  · dsimp only [addChunkSpecX]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr, hsorted'⟩ => ?_
    apply SepWPp.of_sepWP (mid := next_pc)
    have hassoc :
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStackX) ∗ Frame =
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗
          (chunkAt chunkA chunk ∗ (A.pool ∗ stackAt sp_call addChunkStackX))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hsorted'

/-- Framed call rule for `polyDecoderDecodedMessageSpec A b` (`0x6bb80`) inside `States::recv`. -/
theorem call_decodedMessage_statesRecv {A : RustAlloc} {b : BitVec 64} {P_pan : Prop}
    {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (polyDecoderDecodedMessageSpec A b))
    (hb : b &&& 0xfff#64 = 0#64)
    (outA decA : BitVec 64) (dec : PolyDecoder) (outMsg : Option Bytes)
    (hsorted : PolyDecoderStrictSorted dec)
    (hdec : spqrPolyApi.decoded_message dec = .ok outMsg)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx8 : s.readReg64 Reg.x8 = outA)
    (hx0 : s.readReg64 Reg.x0 = decA)
    (hsplit : P = (memRegion outA 24 ∗ polyDecoderAt A decA dec ∗
      tokenInitAt b ∗ reduceTableAt b ∗
      A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      SepWP prog next_pc sf
        ((optVecU8At A outA outMsg ∗ polyDecoderAt A decA dec ∗
          tokenInitAt b ∗ reduceTableAt b ∗
          A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame)
        (fun sm Pm =>
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)))) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨outA, decA, dec, outMsg⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [polyDecoderDecodedMessageSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hb, hx8, hx0, hsorted, hdec⟩, hm⟩
  · dsimp only [polyDecoderDecodedMessageSpec] at hmem
    exact Satisfies.mono (sepConj_mono_left (onPanic_alloc_entails_statesRecv htrace.1)) hmem
  · dsimp only [polyDecoderDecodedMessageSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP (mid := next_pc)
    have hassoc :
        (optVecU8At A outA outMsg ∗ polyDecoderAt A decA dec ∗
          tokenInitAt b ∗ reduceTableAt b ∗
          A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame =
        (optVecU8At A outA outMsg ∗
          (polyDecoderAt A decA dec ∗
            (tokenInitAt b ∗
              (reduceTableAt b ∗
                (A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack))))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

/-- Framed call rule for `unchunkedCt1SentEkReceivedSendCt2Spec A F K b` (`0x5e400`) inside `States::recv`. -/
theorem call_sendCt2_statesRecv {A : RustAlloc} {F : ShaCompress} {K : MlKem} {b : BitVec 64}
    {P_pan : Prop} {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (unchunkedCt1SentEkReceivedSendCt2Spec A F K b))
    (hb : b &&& 0xfff#64 = 0#64)
    (outA stA : BitVec 64)
    (st : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) (ct2 : Bytes) (mac : Mac)
    (hsc : st.send_ct2 K = .ok (outUc, ct2, mac))
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = stA)
    (hsplit : P = (memRegion outA 104 ∗ unchunkedCt1SentEkReceivedAt A stA st ∗
      unchunkedSendCt2RoAt b ∗ A.pool ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      SepWP prog next_pc sf
        ((unchunkedCt2SentAt A outA outUc ∗ vecU8 A (outA + 56#64) ct2 ∗
          vecU8 A (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2RoAt b ∗ A.pool ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
        (fun sm Pm =>
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)))) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨outA, stA, st, outUc, ct2, mac⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [unchunkedCt1SentEkReceivedSendCt2Spec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hb, hx0, hx1, hsc⟩, hm⟩
  · dsimp only [unchunkedCt1SentEkReceivedSendCt2Spec] at hmem
    exact Satisfies.mono (sepConj_mono_left (onPanic_alloc_entails_statesRecv htrace.1)) hmem
  · dsimp only [unchunkedCt1SentEkReceivedSendCt2Spec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP (mid := next_pc)
    have hassoc :
        (unchunkedCt2SentAt A outA outUc ∗ vecU8 A (outA + 56#64) ct2 ∗
          vecU8 A (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2RoAt b ∗ A.pool ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame =
        (unchunkedCt2SentAt A outA outUc ∗
          (vecU8 A (outA + 56#64) ct2 ∗
            (vecU8 A (outA + 80#64) mac ∗
              (memRegion stA 128 ∗
                (unchunkedSendCt2RoAt b ∗
                  (A.pool ∗ stackAt sp_call unchunkedSendCt2Stack)))))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

/-- Framed call rule for `sendCt2EncoderSpec A` (`0x63b28`) inside `States::recv`. -/
theorem call_sendCt2Encoder_statesRecv {A : RustAlloc} {P_pan : Prop}
    {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (sendCt2EncoderSpec A))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
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
      SepWP prog next_pc sf
        ((polyEncoderAt A outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
        (fun sm Pm =>
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)))) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [sendCt2EncoderSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hct2_ptr, hmac_ptr, henc⟩, hm⟩
  · dsimp only [sendCt2EncoderSpec] at hmem
    exact Satisfies.mono (sepConj_mono_left (onPanic_alloc_entails_statesRecv htrace.1)) hmem
  · dsimp only [sendCt2EncoderSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP (mid := next_pc)
    have hassoc :
        (polyEncoderAt A outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame =
        (polyEncoderAt A outA enc ∗
          ((ct2Ptr ↦ₛ ct2) ∗ ((macPtr ↦ₛ mac) ∗ (A.pool ∗ stackAt sp_call sendCt2EncoderStack)))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

set_option maxHeartbeats 2000000 in
/-- Copies `st.uc` (`128`B at `stA + 400`) to `fsp + 3696`, stores `stA` to `fsp + 232`, and
    `memcpy`s `st.receiving_ek` (`400`B at `stA + 528`) to `fsp + 2752` (`+11404 -> +11472`,
    `0x580e0 -> 0x58124`), preserving `c_uc` at both `stA + 400` and `fsp + 3696`. -/
theorem ct1Sampled_recv_ek_prefix_copy
    {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s_in : State) (fsp stA ve8 : BitVec 64)
    (c_uc : Words16) (dec : PolyDecoder) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11404#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = stA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11472#64) s_in
      (wordsAt (stA + 400#64) c_uc.toList ∗
        polyDecoderAt A (stA + 528#64) dec ∗
        ((fsp + 232#64) ↦₆₄ ve8) ∗
        memRegion (fsp + 2752#64) 400 ∗
        memRegion (fsp + 3696#64) 128 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          wordsAt (stA + 400#64) c_uc.toList ∗
          wordsAt (fsp + 3696#64) c_uc.toList ∗
          polyDecoderAt A (fsp + 2752#64) dec ∗
          ((fsp + 232#64) ↦₆₄ stA) ∗
          memRegion (stA + 528#64) 400 ∗
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
        Rest ⊢
      ∃∗ c_dst : Words16, ∃∗ bs_dec : List (BitVec 8),
        ⌜bs_dec.length = 400⌝ ∗
        wordsAt (stA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_dst.toList ∗
        ((fsp + 232#64) ↦₆₄ ve8) ∗
        ((stA + 528#64) ↦ₛ bs_dec) ∗
        memRegion (fsp + 2752#64) 400 ∗
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
  have hmemcpy_raw := memcpy_region_ok_at_statesRecv hmemcpy
  refine SepWP.mono (post := fun sf Pf =>
      (Pf ⊢
        wordsAt (s_in.readReg64 .x1 + 400#64) c_uc.toList ∗
        wordsAt (s_in.sp + 3696#64) c_uc.toList ∗
        ((s_in.sp + 2752#64) ↦ₛ bs_dec) ∗
        ((s_in.sp + 232#64) ↦₆₄ s_in.readReg64 .x1) ∗
        ((s_in.readReg64 .x1 + 528#64) ↦ₛ bs_dec) ∗
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
  · states_recv_fetches_range b (Rust.withPanics ext) 11404 68
    dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::recv" = entry
    examples_hide_fetches
    dsimp only [Words16.toList]
    simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    wp_call hmemcpy_raw ⟨s_in.sp + 2752#64, s_in.readReg64 .x1 + 528#64, bs_dec⟩
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
      Rest by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hdec (sepConj_mono_right (sepConj_mono_left hdec_in))))

theorem cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  apply beq_false_of_ne
  intro heq
  have h1 : (cap + 1#64).toNat = 0 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  omega

/-- Branches to `+13968` (`0x58ae4`) when `outMsg = none` (`+11496 -> +13968`, `0x5813c -> 0x58ae4`)
    and folds `optVecU8At A (fsp + 3832#64) none` into `memRegion (fsp + 3832#64) 24`. -/
theorem ct1Sampled_recv_ek_decode_branch_none
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (s_in : State) (fsp : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11496#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 13968#64) s_in
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
  states_recv_fetches_range b (Rust.withPanics ext) 11496 12
  dsimp only [tripleRatchetProgAtExt, statesRecvName, optVecU8At, noneCap,
    BitVec.ofNat_eq_ofNat] at hpc hfold ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.focus_weaken hfold (by sep_focus) ?_
  wp_done

/-- Falls through to `+11508` (`0x58148`) when `outMsg = some decoded` (`+11496 -> +11508`,
    `0x5813c -> 0x58148`) while preserving `vecU8 A (fsp + 3832#64) decoded`. -/
theorem ct1Sampled_recv_ek_decode_branch_some
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (s_in : State) (fsp : BitVec 64) (decoded : Bytes) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11496#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11508#64) s_in
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
  have hcmn := cap_add_one_beq_zero_false hcap_lt
  have hrecomb := vecU8_of_slice_and_tail A (s_in.sp + 3832#64) cap ptr decoded hle hcap_lt hptr_ne
  states_recv_fetches_range b (Rust.withPanics ext) 11496 12
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.focus_weaken hrecomb (by sep_focus) ?_
  wp_done

set_option maxHeartbeats 1200000 in
/-- Calls `PolyDecoder::add_chunk` (`0x6c420`) on `fsp + 2752` and `msgA + 10`, then calls
    `<PolyDecoder as Decoder>::decoded_message` (`0x6bb80`) with output at `fsp + 3832`
    (`+11472 -> +11496`, `0x58124 -> 0x5813c`). -/
theorem ct1Sampled_recv_ek_add_and_decode
    {b : BitVec 64} {A : RustAlloc} {P_pan : Prop}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (hdec_call : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr polyDecoderDecodedMessageName)
      (polyDecoderDecodedMessageSpec A b))
    (hb : b &&& 0xfff#64 = 0#64)
    (s0 s_in : State) (fsp msgA : BitVec 64)
    (dec : PolyDecoder) (chunk : Chunk) (outMsg : Option Bytes)
    (hsorted : PolyDecoderStrictSorted dec)
    (hdec_msg : spqrPolyApi.decoded_message (addChunkTotal dec chunk) = .ok outMsg)
    (Rest R : SepProp)
    {post : State → SepProp → Prop}
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11472#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx24 : s_in.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s_in s0)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11496#64 →
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
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11496#64) sf
        (optVecU8At A (fsp + 3832#64) outMsg ∗
          polyDecoderAt A (fsp + 2752#64) (addChunkTotal dec chunk) ∗
          chunkAt (msgA + 10#64) chunk ∗
          statesRecvRoAt b ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest)
        (fun sm Pm =>
          SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)))) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 94156#64) s_in
      (memRegion (fsp + 3832#64) 24 ∗
        polyDecoderAt A (fsp + 2752#64) dec ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoAt b ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sm Pm =>
        SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) := by
  subst hsp hx24
  have hadd_raw := addChunkX_ok_at_statesRecv hA
  have hdec_raw := polyDecodedMsg_ok_at_statesRecv hdec_call
  have hsplit_add := stackAt_statesRecvCallee_eq_addChunk s_in.sp
  have hsplit_dec := stackAt_statesRecvCallee_eq_polyDecodedMessage s_in.sp
  states_recv_fetches_range b (Rust.withPanics ext) 11472 24
  dsimp only [tripleRatchetProgAtExt, statesRecvName, statesRecvRoAt,
    RecvCt2Chunk.polyDecodedMessageStackX, BitVec.ofNat_eq_ofNat]
    at hpc hadd_raw hdec_raw hsplit_add hsplit_dec hnext ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  rw [hsplit_add]
  wp_steps
  refine call_addChunkX_statesRecv (P_pan := P_pan) hadd_raw
    (s_in.sp + 2752#64) (s_in.readReg64 .x24 + 10#64) dec chunk hsorted
    (s0 := s0) (ret_pc := entry + 11484#64) (next_pc := entry + 91948#64) (sp_call := s_in.sp)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [TraceCalleeSaved, arm64_norm, htr.1, htr.2])
    (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, Reg.x24, arm64_norm])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 hsorted' => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, _⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1
  refine SepWP.focus_weaken (Entails.of_eq hsplit_add.symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq hsplit_dec) (by sep_focus) ?_
  wp_steps
  refine call_decodedMessage_statesRecv (P_pan := P_pan) hdec_raw hb
    (s_in.sp + 3832#64) (s_in.sp + 2752#64) (addChunkTotal dec chunk) outMsg hsorted' hdec_msg
    (s0 := s0) (ret_pc := entry + 11496#64) (next_pc := entry + 11496#64) (sp_call := s_in.sp)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [TraceCalleeSaved, arm64_norm, htr1.1, htr1.2])
    (by simp only [Reg.x8, arm64_norm, hsp1])
    (by simp only [Reg.x0, arm64_norm, hsp1])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, _⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx28_1, hfp_1]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx28_2 hfp_2
  refine SepWP.focus_weaken (Entails.of_eq hsplit_dec.symm) (by sep_focus) ?_
  exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sf2 hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx28_2 hfp_2 htr2 hsorted')

end CryptoVerification.SpqrV1.States.Recv
