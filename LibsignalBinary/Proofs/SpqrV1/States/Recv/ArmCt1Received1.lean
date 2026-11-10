/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Received` Arm, Part 1

**Checked by Lean.** Stack/writeback helpers, pure `Ct1Received::recv_ct2_chunk` unfolding,
post-call writeback blocks, and the `msg.epoch > st.uc.epoch` and `msg.epoch < st.uc.epoch` paths
of `.ct1Received` (`0x55908`, `+1204`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.DecodedMessage
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48

/-! ## 1. Stack & Writeback Entailment Helpers -/

theorem sendEkUnusedAt_split_ac0 (fsp : BitVec 64) :
    sendEkUnusedAt fsp ⊢
      ∃∗ qac0 : BitVec 128,
        ((fsp + 2752#64) ↦₁₂₈ qac0) ∗
        memRegion fsp 8 ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 2736#64) 16 ∗
        memRegion (fsp + 2768#64) 1376 := by
  unfold sendEkUnusedAt
  rw [ProofLib.memRegion_split' (b := fsp + 2736#64) (n := 16) (k := 1392)
        (b' := fsp + 2752#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2752#64) (n := 16) (k := 1376)
        (b' := fsp + 2768#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (memRegion_16_entails_128_recv (fsp + 2752#64))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, ← sepConj_assoc]
  apply Entails.sepExists_elim; intro qac0
  refine Entails.sepExists_right qac0 ?_
  exact Entails.of_eq (by ac_rfl)

theorem sendEkUnusedAt_rejoin_ac0 (fsp : BitVec 64) (qac0 : BitVec 128) :
    ((fsp + 2752#64) ↦₁₂₈ qac0) ∗
    memRegion fsp 8 ∗
    memRegion (fsp + 568#64) 8 ∗
    memRegion (fsp + 952#64) 8 ∗
    memRegion (fsp + 2736#64) 16 ∗
    memRegion (fsp + 2768#64) 1376 ⊢
      sendEkUnusedAt fsp := by
  unfold sendEkUnusedAt
  rw [ProofLib.memRegion_split' (b := fsp + 2736#64) (n := 16) (k := 1392)
        (b' := fsp + 2752#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2752#64) (n := 16) (k := 1376)
        (b' := fsp + 2768#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (Entails.of_eq (show _ =
    memRegion fsp 8 ∗ memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
    (memRegion (fsp + 2736#64) 16 ∗ (((fsp + 2752#64) ↦₁₂₈ qac0) ∗ memRegion (fsp + 2768#64) 1376)) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (pointsTo128_entails_memRegion_16 (fsp + 2752#64) qac0)))))

theorem none_tail_entails_optEpochSecretAt_none (A : RustAlloc) (a w1 : BitVec 64) (q2 : BitVec 128) :
    (a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₁₂₈ q2) ⊢
      optEpochSecretAt A a none := by
  dsimp only [optEpochSecretAt]
  rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16)
        (b' := a + 16#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono
    (ProofLib.pointsTo64_entails_memRegion (a + 8#64) w1)
    (pointsTo128_entails_memRegion_16 (a + 16#64) q2))

theorem self_504_416_entails_memRegion_928 (selfA tag : BitVec 64) :
    (selfA ↦₆₄ tag) ∗ memRegion (selfA + 8#64) 504 ∗ memRegion (selfA + 512#64) 416 ⊢
      memRegion selfA chunkedStatesSize := by
  unfold chunkedStatesSize
  rw [ProofLib.memRegion_split selfA 8 920 (by decide),
      ProofLib.memRegion_split' (b := selfA + 8#64) (n := 504) (k := 416)
        (b' := selfA + 512#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion selfA tag)

theorem writeback_ct1Received_entails_resultV1RecvAt (A : RustAlloc) {F : ShaCompress}
    (outA : BitVec 64) (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (w : Words63) (w936 : BitVec 64) (q944 : BitVec 128) :
    (outA ↦₆₄ 5#64) ∗
    words63At (outA + 8#64) w ∗
    relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
    memRegion (outA + 512#64) 376 ∗
    memRegion (outA + 888#64) 40 ∗
    ((outA + 928#64) ↦₆₄ noneCap) ∗
    ((outA + 936#64) ↦₆₄ w936) ∗
    ((outA + 944#64) ↦₁₂₈ q944) ⊢
      resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Received st }) := by
  dsimp only [resultV1RecvAt, v1RecvAt, chunkedStatesAt]
  have h416 : memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40 ⊢
      memRegion (outA + 512#64) 416 := by
    rw [ProofLib.memRegion_split' (b := outA + 512#64) (n := 376) (k := 40)
      (b' := outA + 888#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hnone := none_tail_entails_optEpochSecretAt_none A (outA + 928#64) w936 q944
  have h936 : (outA + 928#64) + 8#64 = outA + 936#64 := by bv_omega
  have h944 : (outA + 928#64) + 16#64 = outA + 944#64 := by bv_omega
  rw [h936, h944] at hnone
  refine Entails.trans (Entails.of_eq (show _ =
    ((outA ↦₆₄ 5#64) ∗
     (words63At (outA + 8#64) w ∗
      relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w))) ∗
     (memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40)) ∗
    (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944)) by ac_rfl)) ?_
  exact sepConj_mono
    (sepConj_mono_right (sepConj_mono (recompose63 (outA + 8#64) w) h416))
    hnone

theorem writeback_ekSentCt1Received_entails_resultV1RecvAt (A : RustAlloc) {F : ShaCompress}
    (outA : BitVec 64) (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (w : Words63) (w936 : BitVec 64) (q944 : BitVec 128) :
    (outA ↦₆₄ 6#64) ∗
    words63At (outA + 8#64) w ∗
    relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
    memRegion (outA + 512#64) 376 ∗
    memRegion (outA + 888#64) 40 ∗
    ((outA + 928#64) ↦₆₄ noneCap) ∗
    ((outA + 936#64) ↦₆₄ w936) ∗
    ((outA + 944#64) ↦₁₂₈ q944) ⊢
      resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekSentCt1Received st }) := by
  dsimp only [resultV1RecvAt, v1RecvAt, chunkedStatesAt]
  have h416 : memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40 ⊢
      memRegion (outA + 512#64) 416 := by
    rw [ProofLib.memRegion_split' (b := outA + 512#64) (n := 376) (k := 40)
      (b' := outA + 888#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hnone := none_tail_entails_optEpochSecretAt_none A (outA + 928#64) w936 q944
  have h936 : (outA + 928#64) + 8#64 = outA + 936#64 := by bv_omega
  have h944 : (outA + 928#64) + 16#64 = outA + 944#64 := by bv_omega
  rw [h936, h944] at hnone
  refine Entails.trans (Entails.of_eq (show _ =
    ((outA ↦₆₄ 6#64) ∗
     (words63At (outA + 8#64) w ∗
      relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w))) ∗
     (memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40)) ∗
    (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944)) by ac_rfl)) ?_
  exact sepConj_mono
    (sepConj_mono_right (sepConj_mono (recompose63 (outA + 8#64) w) h416))
    hnone

/-! ## 2. Pure Model Unfolding for `Ct1Received::recv_ct2_chunk` -/

attribute [local irreducible] addChunkTotal decodedMessageTotal

theorem spqrPolyApi_add_chunk_eq_ok2 (self : PolyDecoder) (chunk : Chunk)
    (hpts_len : self.pts.length = 16) :
    spqrPolyApi.add_chunk self chunk = .ok (addChunkTotal self chunk) := by
  dsimp only [spqrPolyApi]
  rw [addChunk_eq_ok self chunk hpts_len]
  rfl

theorem except_bind_ok2 {ε α β : Type} {x : Except ε α} {v : α}
    (h : x = .ok v) (f : α → Except ε β) :
    Bind.bind x f = f v := by
  rw [h]; rfl

theorem except_lift_bind_ok2 {α β : Type} {x : Except SpqrPanic α} {v : α}
    (h : x = .ok v) (f : α → Except StatesPanic β) :
    Bind.bind (liftM x) f = f v := by
  rw [h]; rfl

def polyDecoderNew80 : PolyDecoder :=
  { pts := List.replicate NUM_POLYS SortedSetPt.new
    ptsNeeded := 80
    isComplete := false }

theorem expectDecoderNew_160 :
    expectDecoderNew spqrPolyApi "v1/chunked/send_ek.rs:174" 160 = .ok polyDecoderNew80 := by
  decide

theorem polyDecoderNew80_strictSorted :
    PolyDecoderStrictSorted polyDecoderNew80 := by
  intro s hs
  rw [polyDecoderNew80, List.mem_replicate] at hs
  rcases hs with ⟨_, rfl⟩
  exact List.Pairwise.nil

theorem ct1Received_recv_ct2_chunk_eq_ok {F : ShaCompress}
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)) (chunk : Chunk) :
    ∃ outSt,
      st.recv_ct2_chunk st.uc.epoch chunk = .ok outSt ∧
      PolyDecoderStrictSorted outSt.receiving_ct2 := by
  have hlen0 : polyDecoderNew80.pts.length = 16 := rfl
  have hadd := spqrPolyApi_add_chunk_eq_ok2 polyDecoderNew80 chunk hlen0
  have hsort' := (addChunkBsearch_eq_addChunkTotal polyDecoderNew80 chunk hlen0 polyDecoderNew80_strictSorted).2
  let outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F) :=
    { uc := st.uc, receiving_ct2 := addChunkTotal polyDecoderNew80 chunk }
  refine ⟨outSt, ?_, hsort'⟩
  have hstep : st.recv_ct2_chunk st.uc.epoch chunk =
      (do
        let receivingCt2 ← expectDecoderNew spqrPolyApi "v1/chunked/send_ek.rs:174" 160
        let receivingCt2 ← liftM (spqrPolyApi.add_chunk receivingCt2 chunk)
        Except.ok { uc := st.uc, receiving_ct2 := receivingCt2 }) := by
    unfold Chunked.SendEk.Ct1Received.recv_ct2_chunk
    rw [bne_self_eq_false, ite_eq_right_iff.mpr (fun h => nomatch h)]
    rfl
  rw [hstep, except_bind_ok2 expectDecoderNew_160, except_lift_bind_ok2 hadd]

open CryptoVerification.SpqrV1.States.Leaves (sub_ok_of_addr_eq)

theorem fnAddr_bwd_eq_recv {c : Program} {f1 f2 : String} {o1 o2 d k : Nat}
    {b : BitVec 64} {X : String → Option (State → State)}
    (ho1 : c.fnOff f1 = o1) (ho2 : c.fnOff f2 = o2) (hd : o2 + d = o1)
    (hk : BitVec.ofNat 64 k = -BitVec.ofNat 64 d) :
    (c.rebase b X).fnAddr f1 + BitVec.ofNat 64 k = (c.rebase b X).fnAddr f2 := by
  have hback : (c.rebase b X).fnAddr f2 = (c.rebase b X).fnAddr f1 - BitVec.ofNat 64 d :=
    Program.fnAddr_back (d := d) (b := b) (X := X) ho1 ho2 hd
  rw [hback, hk]
  bv_omega

theorem stackAt_statesRecvCallee_split_dropStack32 (sp : BitVec 64) :
    stackAt sp statesRecvCalleeStackX =
      memRegion (sp - BitVec.ofNat 64 statesRecvCalleeStackX) (statesRecvCalleeStackX - dropStack32) ∗
      stackAt sp dropStack32 := by
  simp only [stackAt]
  exact ProofLib.memRegion_split'
    (b := sp - BitVec.ofNat 64 statesRecvCalleeStackX)
    (n := statesRecvCalleeStackX - dropStack32) (k := dropStack32)
    (b' := sp - BitVec.ofNat 64 dropStack32) rfl
    (by change sp - 4128#64 = (sp - 19552#64) + 15424#64; bv_omega)
    (by decide)

theorem stackAt_statesRecvCallee_split_ct1RecvCt2 (sp : BitVec 64) :
    stackAt sp statesRecvCalleeStackX =
      memRegion (sp - BitVec.ofNat 64 statesRecvCalleeStackX)
        (statesRecvCalleeStackX - ct1ReceivedRecvCt2ChunkStack) ∗
      stackAt sp ct1ReceivedRecvCt2ChunkStack := by
  simp only [stackAt]
  exact ProofLib.memRegion_split'
    (b := sp - BitVec.ofNat 64 statesRecvCalleeStackX)
    (n := statesRecvCalleeStackX - ct1ReceivedRecvCt2ChunkStack) (k := ct1ReceivedRecvCt2ChunkStack)
    (b' := sp - BitVec.ofNat 64 ct1ReceivedRecvCt2ChunkStack) rfl
    (by change sp - 16976#64 = (sp - 19552#64) + 2576#64; bv_omega)
    (by decide)

theorem memRegion_880_split_504_376 (a a' : BitVec 64) (h : a + 504#64 = a') :
    memRegion a 880 = memRegion a 504 ∗ memRegion a' 376 :=
  ProofLib.memRegion_split' (b := a) (n := 504) (k := 376) (b' := a') rfl h.symm (by decide)

theorem words63At_376_entails_memRegion_880 (a a' : BitVec 64) (w : Words63) (h : a + 504#64 = a') :
    words63At a w ∗ memRegion a' 376 ⊢ memRegion a 880 := by
  rw [memRegion_880_split_504_376 a a' h]
  exact sepConj_mono_left (words63At_entails_memRegion a w)

/-! ## 3. `.ct1Received` (`0x55908`, `+1204`) Helper Blocks -/

/-- `msg.epoch > st.uc.epoch` error block `0x55c8c..0x55ca4` (`+2104 -> +19356`) for `.ct1Received`:
    writes `Err(EpochOutOfRange(msg.epoch))` to `outA`, calls `0x4c8bc` (`drop_chunked_ct1_received_ok_ext`)
    on `selfA + 8#64`, and branches to `0x59fd0` (`states_recv_epilogue_59fd0`). -/
theorem ct1Received_gt_55c8c {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s0 s : State) (outA selfA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (ep : BitVec 64) (P_rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 2104#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = selfA + 8#64)
    (hx19 : s.readReg64 .x19 = outA)
    (hx25 : s.readReg64 .x25 = ep)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
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
  have hdrop_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18446744073709515880#64)
      (dropChunkedCt1ReceivedSpec A F) := Leaves.sub_ok_of_addr_eq
    (fnAddr_bwd_eq_recv (d := 35736) (k := 18446744073709515880) (b := b) (X := Rust.withPanics ext)
      statesRecv_fnOff libsignalSessionCode_fnOff_0x474c4 (by decide) rfl).symm
    (drop_chunked_ct1_received_ok_ext hdealloc)
  have hepilogue := @states_recv_epilogue_59fd0 b ext s0
  states_recv_fetches_range b (Rust.withPanics ext) 2104 28
  dsimp only [tripleRatchetProgAtExt, statesRecvName, dropChunkedCt1ReceivedSpec,
    chunkedCt1ReceivedSize, BitVec.ofNat_eq_ofNat] at hdrop_raw hepilogue hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  rw [memRegion_out_960_split_err outA]
  wp_pull_exists; rename_i v0 b8 v16
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_steps
  subst hsp0
  have hsplit_sp := stackAt_statesRecvCallee_split_dropStack32 (s0.sp - 4240#64)
  refine SepWP.focus_weaken (Entails.of_eq hsplit_sp) (by sep_focus) ?_
  wp_call hdrop_raw ⟨selfA + 8#64, st⟩
  wp_conv_pre => rw [hsp]
  refine SepWP.focus_weaken (Entails.of_eq hsplit_sp.symm) (by sep_focus) ?_
  wp_steps
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
      rfl (by assumption) (by exact (by assumption : _ = s.sp).trans hsp)
      hsp_align ⟨(by assumption : _ = s.trace).trans htr.1, (by assumption : _ = calleeSavedVRegs _).trans (by simpa only [arm64_norm] using htr.2)⟩)
    (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

set_option autoImplicit false in
set_option maxHeartbeats 1200000 in
private theorem ct1Received_post_call_core {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    {Inv : State → Prop} {calleeStk finalStk : Nat}
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hwb : ∀ (sm : State) (outA : BitVec 64) (sp : SendEkSpills) (P_rest : SepProp),
      Inv sm →
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64 →
      sm.status = .Running → sm.sp = s0.sp - 4240#64 → s0.spAligned = true →
      sm.readReg64 .x19 = outA → TraceCalleeSaved sm s0 →
      SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm
        (P_rest ∗ memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) calleeStk ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
        (fun sf Pf =>
          (Pf ⊢ P_rest ∗ (outA ↦₆₄ sp.b2.w7) ∗ words63At (outA + 8#64) (writebackWords63 sm sp) ∗
            memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40 ∗
            ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗ ((outA + 936#64) ↦₆₄ sm.readReg64 .x20) ∗
            ((outA + 944#64) ↦₁₂₈ sp.q200) ∗ stackAt s0.sp finalStk) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace))
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 6436#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) calleeStk ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        chunkedEkSentCt1ReceivedAt A ((s0.sp - 4240#64) + 976#64) outSt ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sm Pm => Inv sm →
        SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm Pm
          (fun sf Pf =>
            (Pf ⊢
              P_rest ∗
              resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekSentCt1Received outSt }) ∗
              stackAt s0.sp finalStk) ∧
            sf.sp = s0.sp ∧
            CalleeSavedPreserved s0 sf ∧
            sf.trace = s0.trace)) := by
  states_recv_fetches_range b (Rust.withPanics ext) 6436 384
  states_recv_fetches_range b (Rust.withPanics ext) 6992 60
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hwb hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  refine SepWP.fold (chunkedEkSentCt1ReceivedAt_extract63 A ((s0.sp - 4240#64) + 976#64) outSt)
    (by sep_focus) ?_
  wp_pull_exists; rename_i w_out
  refine SepWP.pure_elim fun _ => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps
  subst hsp0
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
      stackAt (s0.sp - 4240#64) calleeStk ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗
      statesRecvSavedCells s0)
    hfold_sp1
    ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    sep_ac_rfl_recv_ext
  · rw [show (memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)) ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) calleeStk ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0) =
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out))) ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) calleeStk ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0 by sep_ac_rfl_recv_ext]
    refine SepWP.done rfl hrun fun hinv_wb => ?_
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗ relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)))
        hinv_wb rfl hrun hsp hsp_align (by simp only [Reg.x19, arm64_norm, hx19]) htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
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
    sep_ac_rfl_recv_ext

set_option autoImplicit false in
/-- Post-call writeback block `0x56d78..0x56ef4 -> 0x56fa4..0x56fdc -> 0x59e88..0x59ff0`
    (`+6436 -> +19356`) after `<Ct1Received>::recv_ct2_chunk` returns `outSt` at `fsp + 976#64`. -/
theorem ct1Received_post_call_56d78 {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 6436#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
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
        sf.trace = s0.trace) :=
  SepWP.seq
    (ct1Received_post_call_core (Inv := fun _ => True) s0 s outA outSt sp P_rest
      (fun sm outA sp P_rest _ => @states_recv_writeback_59e88 b ext hmemcpy
        (F_tail := fun a => memRegion a 376) (Relocatable.of_memRegion 376) s0 sm outA sp P_rest)
      hpc hrun hsp hsp_align hx19 htr)
    (fun _ _ _ _ h => h trivial)

set_option autoImplicit false in
/-- Post-call writeback block (`+6436 -> +19356`) after `<Ct1Received>::recv_ct2_chunk` returns
    `outSt` at `fsp + 976#64`, backed by `AllocContractsX` at `statesRecvCalleeStackXExt`. -/
theorem ct1Received_post_call_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hinv_img : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 6436#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
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
          stackAt s0.sp statesRecvStackXExt) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) :=
  CryptoVerification.LibsignalTripleRatchet.SepWP.seq_inImage hinv_img
    (ct1Received_post_call_core s0 s outA outSt sp P_rest
      (fun sm outA sp P_rest => @states_recv_writeback_59e88_stk_ext img A ext hAx
        (F_tail := fun a => memRegion a 376) (Relocatable.of_memRegion 376) s0 sm outA sp P_rest)
      hpc hrun hsp hsp_align hx19 htr)

theorem fnAddr_adrp_56ae8 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr statesRecvName + 5780#64) &&&
      0xfffffffffffff000#64) = b + 0x51000#64 := by
  rw [Program.fnAddr_rebase, statesRecv_fnOff]
  revert hb; bv_bits

theorem states_recv_ct1Received_gt (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (hgt : msg.epoch > st.uc.epoch) :
    States.recv K (.ct1Received st) msg = .error (.err (.epochOutOfRange msg.epoch)) := by
  have hgt' : msg.epoch > st.epoch := hgt
  dsimp only [States.recv]
  rw [ite_eq_left_iff.mpr (fun h => absurd hgt' h)]

theorem states_recv_ct1Received_lt (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (hlt : msg.epoch < st.uc.epoch) :
    States.recv K (.ct1Received st) msg =
      .ok { key := none, state := .ct1Received st } := by
  have hlt' : msg.epoch < st.epoch := hlt
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    change ¬ (st.epoch < msg.epoch)
    exact BitVec.not_lt.mpr (BitVec.le_of_lt hlt')
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_left_iff.mpr (fun h => absurd hlt' h)]

theorem states_recv_ct1Received_eq_other (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (heq : msg.epoch = st.uc.epoch)
    (hct2 : ∀ c, msg.payload ≠ .ct2 c) :
    States.recv K (.ct1Received st) msg =
      .ok { key := none, state := .ct1Received st } := by
  have heq' : msg.epoch = st.epoch := heq
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  have hnot_lt' : ¬ (msg.epoch < st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_right_iff.mpr (fun h => absurd h hnot_lt')]
  cases hpay : msg.payload with
  | ct2 c => exact absurd hpay (hct2 c)
  | _ => rfl

theorem states_recv_ct1Received_eq_ct2 (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ct2 chunk)
    (hrecv : st.recv_ct2_chunk st.uc.epoch chunk = .ok outSt) :
    States.recv K (.ct1Received st) msg =
      .ok { key := none, state := .ekSentCt1Received outSt } := by
  have heq' : msg.epoch = st.epoch := heq
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  have hnot_lt' : ¬ (msg.epoch < st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_right_iff.mpr (fun h => absurd h hnot_lt'),
      hpay, heq]
  change Except.bind (StatesResult.ofPanic (st.recv_ct2_chunk st.uc.epoch chunk)) _ = _
  rw [hrecv]
  rfl

/-! ## 4. Full `.ct1Received` Arm (`+1204 -> s0.x30`, `0x55908 -> 0x59ff0`) -/

theorem epoch_cmp_ct1r_eq_of_gt {st_ep msg_ep : BitVec 64} (hgt : msg_ep.toNat > st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) == 0#32) = false := by
  have h1 : st_ep.ule msg_ep = true := by rw [BitVec.ule_eq_decide, decide_eq_true_eq]; omega
  have h2 : msg_ep.ule st_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1, h2]

theorem epoch_cmp_ct1r_eq_1_of_gt {st_ep msg_ep : BitVec 64} (hgt : msg_ep.toNat > st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) == 1#32) = true := by
  have h1 : st_ep.ule msg_ep = true := by rw [BitVec.ule_eq_decide, decide_eq_true_eq]; omega
  have h2 : msg_ep.ule st_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1, h2]

theorem epoch_cmp_ct1r_eq_of_lt {st_ep msg_ep : BitVec 64} (hlt : msg_ep.toNat < st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) == 0#32) = false := by
  have h1 : st_ep.ule msg_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1]

theorem epoch_cmp_ct1r_eq_1_of_lt {st_ep msg_ep : BitVec 64} (hlt : msg_ep.toNat < st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) == 1#32) = false := by
  have h1 : st_ep.ule msg_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1]

theorem epoch_cmp_ct1r_eq_of_eq (ep : BitVec 64) :
    (BitVec.truncate 32 ((if ep.ule ep = true then if ep.ule ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) == 0#32) = true := by
  have h1 : ep.ule ep = true := by rw [BitVec.ule_eq_decide, decide_eq_true_eq]
  simp [h1]

theorem words63At_self_entails_memRegion_928 (selfA tag : BitVec 64) (w : Words63) :
    (selfA ↦₆₄ tag) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416 ⊢
      memRegion selfA chunkedStatesSize := by
  refine Entails.trans ?_ (self_504_416_entails_memRegion_928 selfA tag)
  exact sepConj_mono_right (sepConj_mono_left (words63At_entails_memRegion (selfA + 8#64) w))

/-- `.ct1Received` arm when `msg.epoch > st.uc.epoch` (`+1204 -> s0.x30`, `0x55908..0x55a48 -> 0x55c8c..0x59ff0`). -/
theorem ct1Received_arm_gt
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hgt : msg.epoch > st.uc.epoch)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1204#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
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
  have htail := @ct1Received_gt_55c8c A F b ext hdealloc s0
  states_recv_fetches_range b (Rust.withPanics ext) 1204 320
  dsimp only [tripleRatchetProgAtExt, statesRecvName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc htail ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
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
        rfl hrun hsp hsp_align
        (by simp only [Reg.x0, arm64_norm, hx1])
        (by simp only [Reg.x19, arm64_norm, hx19])
        (by simp only [Reg.x25, arm64_norm, hx24])
        htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf (Entails.of_eq (by ac_rfl))

set_option autoImplicit false in
set_option maxHeartbeats 1200000 in
private theorem ct1Received_arm_lt_core
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    {Inv : State → Prop} {calleeStk finalStk : Nat}
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hwb : ∀ (sm : State) (outA : BitVec 64) (sp : SendEkSpills) (P_rest : SepProp),
      Inv sm →
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64 →
      sm.status = .Running → sm.sp = s0.sp - 4240#64 → s0.spAligned = true →
      sm.readReg64 .x19 = outA → TraceCalleeSaved sm s0 →
      SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm
        (P_rest ∗ memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) calleeStk ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
        (fun sf Pf =>
          (Pf ⊢ P_rest ∗ (outA ↦₆₄ sp.b2.w7) ∗ words63At (outA + 8#64) (writebackWords63 sm sp) ∗
            memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40 ∗
            ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗ ((outA + 936#64) ↦₆₄ sm.readReg64 .x20) ∗
            ((outA + 944#64) ↦₁₂₈ sp.q200) ∗ stackAt s0.sp finalStk) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace))
    (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1204#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) calleeStk ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sm Pm => Inv sm →
        SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm Pm
          (fun sf Pf =>
            (Pf ⊢
              P_rest ∗
              resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Received st }) ∗
              memRegion selfA chunkedStatesSize ∗
              messageAt spqrPolyApi msgA msg ∗
              A.pool ∗
              stackAt s0.sp finalStk) ∧
            sf.sp = s0.sp ∧
            CalleeSavedPreserved s0 sf ∧
            sf.trace = s0.trace)) := by
  have hlt_nat : msg.epoch.toNat < st.uc.epoch.toNat := BitVec.lt_def.mp hlt
  have hcond1 := epoch_cmp_ct1r_eq_of_lt hlt_nat
  have hcond2 := epoch_cmp_ct1r_eq_1_of_lt hlt_nat
  states_recv_fetches_range b (Rust.withPanics ext) 1204 324
  states_recv_fetches_range b (Rust.withPanics ext) 6820 232
  dsimp only [tripleRatchetProgAtExt, statesRecvName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
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
      stackAt (s0.sp - 4240#64) calleeStk ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      statesRecvSavedCells s0)
    hfold_self_unused ?_ ?_
  · rw [← hw62]
    dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    sep_ac_rfl_recv_ext
  · rw [show (memRegion selfA chunkedStatesSize ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) calleeStk ∗
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
        stackAt (s0.sp - 4240#64) calleeStk ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0 by sep_ac_rfl_recv_ext]
    refine SepWP.done rfl hrun fun hinv_wb => ?_
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗
          relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool)
        hinv_wb rfl hrun hsp hsp_align (by simp only [Reg.x19, arm64_norm, hx19]) htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_ct1Received_entails_resultV1RecvAt A (F := F) outA st w
      w.b5.w9 sp.q200
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_left hrec))
    dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
      Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
      Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      Reg.x30]
    simp only [arm64_norm, hx1]
    sep_ac_rfl_recv_ext

set_option autoImplicit false in
/-- `.ct1Received` arm when `msg.epoch < st.uc.epoch` (`+1204 -> s0.x30`, `0x55908..0x55a48 -> 0x56ef8..0x56fdc -> 0x59e88..0x59ff0`). -/
theorem ct1Received_arm_lt
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1204#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
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
        sf.trace = s0.trace) :=
  SepWP.seq
    (ct1Received_arm_lt_core (Inv := fun _ => True) s0 s outA selfA msgA st msg P_rest
      (fun sm outA sp P_rest _ => @states_recv_writeback_59e88 b ext hmemcpy
        (F_tail := fun a => memRegion a 376) (Relocatable.of_memRegion 376) s0 sm outA sp P_rest)
      hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
    (fun _ _ _ _ h => h trivial)

set_option autoImplicit false in
/-- `.ct1Received` arm when `msg.epoch < st.uc.epoch` (`+1204 -> +18996 -> lr`) under `AllocContractsX`. -/
theorem ct1Received_arm_lt_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hinv_img : ImgCallInv img s)
    (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 1204#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Received st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackXExt) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) :=
  CryptoVerification.LibsignalTripleRatchet.SepWP.seq_inImage hinv_img
    (ct1Received_arm_lt_core s0 s outA selfA msgA st msg P_rest
      (fun sm outA sp P_rest => @states_recv_writeback_59e88_stk_ext img A ext hAx
        (F_tail := fun a => memRegion a 376) (Relocatable.of_memRegion 376) s0 sm outA sp P_rest)
      hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)

end CryptoVerification.SpqrV1.States.Recv
