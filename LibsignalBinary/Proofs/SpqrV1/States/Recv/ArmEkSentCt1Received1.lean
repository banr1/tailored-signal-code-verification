/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ekSentCt1Received` Arm, Part 1

**Checked by Lean.** Verifies the `msg.epoch > st.uc.epoch`, `msg.epoch < st.uc.epoch`,
`msg.epoch = st.uc.epoch ∧ msg.payload ≠ .ct2 _`, and post-call `.error` paths of
`.ekSentCt1Received` (`0x55538`, `+228`).
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

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_96_add_8_recv sp_sub_80_add_8_recv sp_sub_64_add_8_recv sp_sub_48_add_8_recv
  sp_sub_32_add_8_recv sp_sub_16_add_8_recv sp_sub_96_add_96_recv
  sp_sub_4240_add_4144_hs bv376_toNat_hs

theorem stackAt_statesRecvStackX_split_dropStack32 (sp : BitVec 64) :
    stackAt sp statesRecvStackX =
      memRegion (sp - 23792#64) 19664 ∗ stackAt sp dropStack32 :=
  stackAt_split_bottom sp dropStack32 19664 (by decide)

/-! ## 1. `.ekSentCt1Received` (`0x55538`, `+228`): `msg.epoch > st.uc.epoch` -/

/-- `msg.epoch > st.uc.epoch` tail-call block `0x55664..0x5569c` (`+528 -> s0.x30`) for `.ekSentCt1Received`:
    writes `Err(EpochOutOfRange(msg.epoch))` to `outA`, restores `sp = s0.sp` and `x19..x30`,
    and tail-calls `0x4c92c` (`drop_chunked_ek_sent_ct1_received_ok_ext`) on `selfA + 8#64`. -/
theorem ekSentCt1Received_gt_55664 {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s0 s : State) (outA selfA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (ep : BitVec 64) (P_rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 528#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx8 : s.readReg64 .x8 = selfA + 8#64)
    (hx19 : s.readReg64 .x19 = outA)
    (hx25 : s.readReg64 .x25 = ep)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
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
  have hdrop_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18446744073709515992#64)
      (dropChunkedEkSentCt1ReceivedSpec A F) := Leaves.sub_ok_of_addr_eq
    (fnAddr_bwd_eq_recv (d := 35624) (k := 18446744073709515992) (b := b) (X := Rust.withPanics ext)
      statesRecv_fnOff libsignalSessionCode_fnOff_0x47534 (by decide) rfl).symm
    (drop_chunked_ek_sent_ct1_received_ok_ext hdealloc)
  states_recv_fetches_range b (Rust.withPanics ext) 528 60
  dsimp only [tripleRatchetProgAtExt, statesRecvName, dropChunkedEkSentCt1ReceivedSpec,
    chunkedEkSentCt1ReceivedSize, BitVec.ofNat_eq_ofNat] at hdrop_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp_align (by decide)
  rw [memRegion_out_960_split_err outA]
  wp_pull_exists; rename_i v0 b8 v16
  unfold statesRecvSavedCells
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hsp96_align ⊢
  wp_steps
  subst hsp0
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

/-- `.ekSentCt1Received` arm when `msg.epoch > st.uc.epoch` (`+228 -> s0.x30`, `0x55538..0x5569c -> b 0x4c92c`). -/
theorem ekSentCt1Received_arm_gt
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hgt : msg.epoch > st.uc.epoch)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 228#64)
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
  have htail := @ekSentCt1Received_gt_55664 A F b ext hdealloc s0
  states_recv_fetches_range b (Rust.withPanics ext) 228 300
  dsimp only [tripleRatchetProgAtExt, statesRecvName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc htail ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
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
        rfl hrun hsp hsp_align
        (by simp only [Reg.x8, arm64_norm, hx1])
        (by simp only [Reg.x19, arm64_norm, hx19])
        (by simp only [Reg.x25, arm64_norm, hx24])
        htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    exact Entails.trans hPf (Entails.of_eq (by ac_rfl))

/-! ## 2. `.ekSentCt1Received` (`0x55538`, `+228`): `msg.epoch < st.uc.epoch` -/

set_option maxHeartbeats 1200000 in
/-- `.ekSentCt1Received` arm when `msg.epoch < st.uc.epoch`
    (`+228 -> s0.x30`, `0x55538..0x55660 -> 0x57508..0x575c8 -> 0x57ffc..0x5800c -> 0x59e88..0x59ff0`). -/
theorem ekSentCt1Received_arm_lt
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 228#64)
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
  have hwb := @states_recv_writeback_59e88 b ext hmemcpy (F_tail := fun a => memRegion a 376)
    (Relocatable.of_memRegion 376) s0
  states_recv_fetches_range b (Rust.withPanics ext) 228 300
  states_recv_fetches_range b (Rust.withPanics ext) 8372 196
  states_recv_fetches_range b (Rust.withPanics ext) 11176 20
  dsimp only [tripleRatchetProgAtExt, statesRecvName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
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

/-! ## 3. `.ekSentCt1Received` (`0x55538`, `+228`): `msg.epoch = st.uc.epoch` & `msg.payload ≠ .ct2 _` -/

set_option maxHeartbeats 1200000 in
/-- `.ekSentCt1Received` arm when `msg.epoch = st.uc.epoch` and `msg.payload ≠ .ct2 _`
    (`+228 -> s0.x30`, `0x55538..0x55658 -> 0x56544..0x5654c -> 0x57f40..0x5800c -> 0x59e88..0x59ff0`). -/
theorem ekSentCt1Received_arm_eq_other
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (heq : msg.epoch = st.uc.epoch)
    (hct2 : ∀ c, msg.payload ≠ .ct2 c)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 228#64)
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
  have hwb := @states_recv_writeback_59e88 b ext hmemcpy (F_tail := fun a => memRegion a 376)
    (Relocatable.of_memRegion 376) s0
  states_recv_fetches_range b (Rust.withPanics ext) 228 292
  states_recv_fetches_range b (Rust.withPanics ext) 4336 12
  states_recv_fetches_range b (Rust.withPanics ext) 10988 208
  dsimp only [tripleRatchetProgAtExt, statesRecvName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
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

/-! ## 4. Post-Call `.error (.err .macVerifyFailed)` Path (`0x56574..0x565a4 -> 0x59fd0..0x59ff0`) and Call Rule -/

def errMacVerifyTag8At (a : BitVec 64) : SepProp :=
  (a ↦₈ 3#8) ∗ memRegion (a + 1#64) 7

def errMacVerifyTag8Split : SplitBytes 8 errMacVerifyTag8At :=
  have h : ∀ a, ((a ↦₈ 3#8) ∗ memRegion (a + BitVec.ofNat 64 1) 7) = errMacVerifyTag8At a :=
    fun _ => rfl
  SplitBytes.congr h ((SplitBytes.pointsTo8 3#8).seq (SplitBytes.region 7 (by decide)) (by decide))

theorem extract_errMacVerifyTag8_word (a : BitVec 64) :
    errMacVerifyTag8At a ⊢ ∃∗ w : BitVec 64, (a ↦₆₄ w) ∗ errMacVerifyTag8Split.heap (unpack64 w) := by
  refine Entails.trans (errMacVerifyTag8Split.to_bytes a) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 hlen
  subst hw
  rw [← pointsTo64_eq_pointsToBytes a w]
  exact Entails.sepExists_right w (Entails.refl _)

theorem recompose_errMacVerifyTag8_word (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) ∗ errMacVerifyTag8Split.heap (unpack64 w) ⊢ errMacVerifyTag8At a := by
  rw [pointsTo64_eq_pointsToBytes a w]
  exact errMacVerifyTag8Split.of_bytes a (unpack64 w) (unpack64_length w)

theorem err_result_976_extract (A : RustAlloc) {F : ShaCompress} (fsp : BitVec 64) :
    ekSentCt1ReceivedRecvChunkResultAt A (F := F) (fsp + 976#64) (.error (.err .macVerifyFailed)) ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ((fsp + 976#64) ↦₆₄ none2Cap) ∗
        ((fsp + 984#64) ↦₆₄ w1) ∗
        ((fsp + 992#64) ↦₆₄ w2) ∗
        ((fsp + 1000#64) ↦₆₄ w3) ∗
        errMacVerifyTag8Split.heap (unpack64 w1) ∗
        memRegion (fsp + 1008#64) 472 := by
  dsimp only [ekSentCt1ReceivedRecvChunkResultAt, spqrErrorByte]
  rw [show (fsp + 976#64) + 8#64 = fsp + 984#64 by bv_omega,
      show (fsp + 976#64) + 9#64 = fsp + 985#64 by bv_omega,
      ProofLib.memRegion_split' (b := fsp + 985#64) (n := 7) (k := 488)
        (b' := fsp + 992#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 992#64) (n := 8) (k := 480)
        (b' := fsp + 1000#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1000#64) (n := 8) (k := 472)
        (b' := fsp + 1008#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 992#64),
      ProofLib.memRegion_eight (fsp + 1000#64)]
  have htag : ((fsp + 984#64) ↦₈ 3#8) ∗ memRegion (fsp + 985#64) 7 ⊢
      ∃∗ w1 : BitVec 64, ((fsp + 984#64) ↦₆₄ w1) ∗ errMacVerifyTag8Split.heap (unpack64 w1) := by
    rw [show fsp + 985#64 = (fsp + 984#64) + 1#64 by bv_omega]
    exact extract_errMacVerifyTag8_word (fsp + 984#64)
  refine Entails.trans (Entails.of_eq (show _ =
    ((fsp + 976#64) ↦₆₄ none2Cap) ∗
    (((fsp + 984#64) ↦₈ 3#8) ∗ memRegion (fsp + 985#64) 7) ∗
    (∃∗ v : BitVec 64, (fsp + 992#64) ↦₆₄ v) ∗
    (∃∗ v : BitVec 64, (fsp + 1000#64) ↦₆₄ v) ∗
    memRegion (fsp + 1008#64) 472 by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left htag)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3 ?_))
  exact Entails.of_eq (by ac_rfl)

theorem err_result_976_fold_880 (fsp w1 w2 w3 : BitVec 64) :
    ((fsp + 976#64) ↦₆₄ none2Cap) ∗
    ((fsp + 984#64) ↦₆₄ w1) ∗
    ((fsp + 992#64) ↦₆₄ w2) ∗
    ((fsp + 1000#64) ↦₆₄ w3) ∗
    memRegion (fsp + 1008#64) 472 ∗
    memRegion (fsp + 1480#64) 376 ⊢
      memRegion (fsp + 976#64) 880 := by
  rw [ProofLib.memRegion_split' (b := fsp + 976#64) (n := 8) (k := 872)
        (b' := fsp + 984#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 984#64) (n := 8) (k := 864)
        (b' := fsp + 992#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 992#64) (n := 8) (k := 856)
        (b' := fsp + 1000#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1000#64) (n := 8) (k := 848)
        (b' := fsp + 1008#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1008#64) (n := 472) (k := 376)
        (b' := fsp + 1480#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))))

theorem memRegion_960_split_err4 (outA : BitVec 64) :
    memRegion outA v1RecvSize ⊢
      ∃∗ v0 : BitVec 64, ∃∗ v8 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v24 : BitVec 64,
        (outA ↦₆₄ v0) ∗ ((outA + 8#64) ↦₆₄ v8) ∗
        ((outA + 16#64) ↦₆₄ v16) ∗ ((outA + 24#64) ↦₆₄ v24) ∗
        memRegion (outA + 32#64) 928 := by
  unfold v1RecvSize
  rw [ProofLib.memRegion_split outA 8 952 (by decide),
      ProofLib.memRegion_split' (b := outA + 8#64) (n := 8) (k := 944)
        (b' := outA + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outA + 16#64) (n := 8) (k := 936)
        (b' := outA + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outA + 24#64) (n := 8) (k := 928)
        (b' := outA + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight outA,
      ProofLib.memRegion_eight (outA + 8#64),
      ProofLib.memRegion_eight (outA + 16#64),
      ProofLib.memRegion_eight (outA + 24#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro v24
  apply Entails.sepExists_elim; intro v16
  apply Entails.sepExists_elim; intro v8
  apply Entails.sepExists_elim; intro v0
  refine Entails.sepExists_right v0 (Entails.sepExists_right v8
    (Entails.sepExists_right v16 (Entails.sepExists_right v24 ?_)))
  exact Entails.of_eq (by ac_rfl)

theorem err4_entails_resultV1RecvAt_macVerifyFailed (A : RustAlloc) {F : ShaCompress}
    (outA w1 w2 w3 : BitVec 64) :
    (outA ↦₆₄ noneCap) ∗
    ((outA + 8#64) ↦₆₄ w1) ∗
    errMacVerifyTag8Split.heap (unpack64 w1) ∗
    ((outA + 16#64) ↦₆₄ w2) ∗
    ((outA + 24#64) ↦₆₄ w3) ∗
    memRegion (outA + 32#64) 928 ⊢
      resultV1RecvAt A (F := F) outA (.error (.err .macVerifyFailed)) := by
  dsimp only [resultV1RecvAt, spqrErrorByte]
  have hrec := recompose_errMacVerifyTag8_word (outA + 8#64) w1
  unfold errMacVerifyTag8At at hrec
  rw [show (outA + 8#64) + 1#64 = outA + 9#64 by bv_omega] at hrec
  have h951 :
      memRegion (outA + 9#64) 7 ∗
      ((outA + 16#64) ↦₆₄ w2) ∗
      ((outA + 24#64) ↦₆₄ w3) ∗
      memRegion (outA + 32#64) 928 ⊢
        memRegion (outA + 9#64) 951 := by
    rw [ProofLib.memRegion_split' (b := outA + 9#64) (n := 7) (k := 944)
          (b' := outA + 16#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outA + 16#64) (n := 8) (k := 936)
          (b' := outA + 24#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outA + 24#64) (n := 8) (k := 928)
          (b' := outA + 32#64) rfl (by bv_omega) (by decide)]
    refine Entails.trans (Entails.of_eq (show _ =
      memRegion (outA + 9#64) 7 ∗
      (((outA + 16#64) ↦₆₄ w2) ∗ (((outA + 24#64) ↦₆₄ w3) ∗ memRegion (outA + 32#64) 928)) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)))
  refine Entails.trans (Entails.of_eq (show _ =
    (outA ↦₆₄ noneCap) ∗
    (((outA + 8#64) ↦₆₄ w1) ∗ errMacVerifyTag8Split.heap (unpack64 w1)) ∗
    (((outA + 16#64) ↦₆₄ w2) ∗
      ((outA + 24#64) ↦₆₄ w3) ∗ memRegion (outA + 32#64) 928) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hrec)) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    (outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 3#8) ∗
    (memRegion (outA + 9#64) 7 ∗ ((outA + 16#64) ↦₆₄ w2) ∗
      ((outA + 24#64) ↦₆₄ w3) ∗ memRegion (outA + 32#64) 928) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right h951)

/-- Post-call block `0x56574..0x565a4 -> 0x59fd0..0x59ff0` (`+4384 -> s0.x30`) when
    `recv_ct2_chunk` returns `.error (.err .macVerifyFailed)`. -/
theorem ekSentCt1Received_post_call_err_56574
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (outA : BitVec 64)
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 4384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
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
  have hep := @states_recv_epilogue_59fd0 b ext s0
  states_recv_fetches_range b (Rust.withPanics ext) 4384 52
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hep ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
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

theorem fnAddr_fwd_recvCt2Chunk {b : BitVec 64} {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr recvCt2ChunkName =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr statesRecvName + 38872#64 := by
  dsimp only [tripleRatchetProgAtExt, statesRecvName, recvCt2ChunkName]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      CryptoVerification.libsignalSessionCode_fnOff_0x5005c,
      CryptoVerification.libsignalSessionCode_fnOff_0x59834]
  bv_omega

/-- Framed call rule for `recvCt2ChunkSpec K F A b` (`0x5ec2c`). -/
theorem call_ekSentCt1ReceivedRecvCt2Chunk {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {b : BitVec 64} {prog : Program} {entry ret_pc : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (hcall : subroutine_ok prog entry (recvCt2ChunkSpec K F A b))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (hsort : PolyDecoderStrictSorted st.receiving_ct2)
    (hroot : st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post Q_panic : State → SepProp → Prop}
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
      tokenInitAt b ∗ reduceTableAt b ∗
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
          tokenInitAt b ∗ reduceTableAt b ∗
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
    dsimp only [recvCt2ChunkSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hb, hx0, hx1, hx2, hx3, hsort, hroot⟩, hm⟩
  · dsimp only [recvCt2ChunkSpec] at hmem
    refine allowPanic_frame (fun ⟨hdisj, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at hdisj ⊢
    rw [htrace.1] at hdisj htr_sub
    exact ⟨hdisj, htr_sub⟩
  · dsimp only [recvCt2ChunkSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (ekSentCt1ReceivedRecvChunkResultAt A (F := F) outA (st.recv_ct2_chunk K st.uc.epoch chunk) ∗
          memRegion stA chunkedEkSentCt1ReceivedSize ∗ chunkAt chunkA chunk ∗
          tokenInitAt b ∗ reduceTableAt b ∗
          A.pool ∗ stackAt sp_call recvCt2ChunkStackX) ∗ Frame =
        (ekSentCt1ReceivedRecvChunkResultAt A (F := F) outA (st.recv_ct2_chunk K st.uc.epoch chunk) ∗
          (memRegion stA chunkedEkSentCt1ReceivedSize ∗
            (chunkAt chunkA chunk ∗ (tokenInitAt b ∗ (reduceTableAt b ∗
              (A.pool ∗ stackAt sp_call recvCt2ChunkStackX)))))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

theorem messagePayloadTag_ct2 (chunk : Chunk) :
    messagePayloadTag (.ct2 chunk) = 6#8 := rfl

def mkWords63_done (g : AuthWords) (ep : BitVec 64) (p : Words5x10)
    (v_sec : VecWords) (sec_ep w_pad : BitVec 64) : Words63 :=
  { b0 := ⟨noneCap, g.v1.w0, g.v1.w1, g.v1.w2, g.v2.w0, g.v2.w1, g.v2.w2, ep, p.b0.w0, p.b0.w1⟩
    b1 := ⟨p.b0.w2, p.b0.w3, p.b0.w4, p.b0.w5, p.b0.w6, p.b0.w7, p.b0.w8, p.b0.w9, p.b1.w0, p.b1.w1⟩
    b2 := ⟨p.b1.w2, p.b1.w3, p.b1.w4, p.b1.w5, p.b1.w6, p.b1.w7, p.b1.w8, p.b1.w9, p.b2.w0, p.b2.w1⟩
    b3 := ⟨p.b2.w2, p.b2.w3, p.b2.w4, p.b2.w5, p.b2.w6, p.b2.w7, p.b2.w8, p.b2.w9, p.b3.w0, p.b3.w1⟩
    b4 := ⟨p.b3.w2, p.b3.w3, p.b3.w4, p.b3.w5, p.b3.w6, p.b3.w7, p.b3.w8, p.b3.w9, p.b4.w0, p.b4.w1⟩
    b5 := ⟨p.b4.w2, p.b4.w3, p.b4.w4, p.b4.w5, p.b4.w6, p.b4.w7, p.b4.w8, p.b4.w9, v_sec.w0, v_sec.w1⟩
    q60 := sec_ep ++ v_sec.w2
    w62 := w_pad }

theorem words63List_mkWords63_done (g : AuthWords) (ep : BitVec 64) (p : Words5x10)
    (v_sec : VecWords) (sec_ep w_pad : BitVec 64) :
    ([noneCap] ++ (ct2SentWordsList g ep ++ words5x10List p)) ++
      (vecWordsList v_sec ++ [sec_ep, w_pad]) =
      words63List (mkWords63_done g ep p v_sec sec_ep w_pad) := by
  simp only [words63List, mkWords63_done, words5x10List, words10List,
    ct2SentWordsList, authWordsList, vecWordsList,
    Leaves.extractLsb'_0_64_append, Leaves.extractLsb'_64_64_append, List.append_assoc,
    List.cons_append, List.nil_append]

theorem chunkedNoHeaderReceivedAt_extract57_ct2 (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (nhr : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    chunkedNoHeaderReceivedAt A a nhr ⊢
      ∃∗ g : AuthWords, ∃∗ p : Words5x10,
        wordsAt a (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p) ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
          (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) := by
  unfold chunkedNoHeaderReceivedAt
  refine Entails.trans (sepConj_mono
    (unchunkedCt2SentAt_extract A a ⟨nhr.uc.epoch, nhr.uc.auth⟩)
    (relocatable_400_extract_words5x10 (Relocatable.of_polyDecoderAt A nhr.receiving_hdr) (a + 56#64))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro g
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro p
  refine Entails.sepExists_right g (Entails.sepExists_right p ?_)
  exact wordsExtract_sepConj rfl (fun _ => rfl)

theorem done_result_976_extract (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (nhr : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (sec : EpochSecret) :
    ekSentCt1ReceivedRecvChunkResultAt A (F := F) a (.ok (.done (nhr, sec))) ⊢
      ∃∗ g : AuthWords, ∃∗ p : Words5x10, ∃∗ v_sec : VecWords, ∃∗ w_pad : BitVec 64,
        words63At a (mkWords63_done g nhr.uc.epoch p v_sec sec.epoch w_pad) ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
          (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
        relocatedHeap (fun dst => vecU8 A dst sec.secret)
          (wordsBytes (vecWordsList v_sec)) := by
  dsimp only [ekSentCt1ReceivedRecvChunkResultAt, ekSentCt1ReceivedRecvChunkAt, epochSecretAt]
  apply Entails.pure_left; intro _
  rw [ProofLib.memRegion_eight (a + 496#64)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono
    (chunkedNoHeaderReceivedAt_extract57_ct2 A (a + 8#64) nhr)
    (sepConj_mono_left (sepConj_mono_left (vecU8_extract A (a + 464#64) sec.secret))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, ← sepConj_assoc]
  apply Entails.sepExists_elim; intro w_pad
  apply Entails.sepExists_elim; intro v_sec
  apply Entails.sepExists_elim; intro g
  apply Entails.sepExists_elim; intro p
  refine Entails.sepExists_right g (Entails.sepExists_right p
    (Entails.sepExists_right v_sec (Entails.sepExists_right w_pad ?_)))
  have hw_eq :
      words63At a (mkWords63_done g nhr.uc.epoch p v_sec sec.epoch w_pad) =
      (a ↦₆₄ noneCap) ∗
      wordsAt (a + 8#64) (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p) ∗
      wordsAt (a + 464#64) (vecWordsList v_sec) ∗
      ((a + 488#64) ↦₆₄ sec.epoch) ∗
      ((a + 496#64) ↦₆₄ w_pad) := by
    rw [words63At_eq_wordsAt, ← words63List_mkWords63_done,
        wordsAt_append ([noneCap] ++ (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p))
          (vecWordsList v_sec ++ [sec.epoch, w_pad]),
        wordsAt_append [noneCap] (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p),
        wordsAt_append (vecWordsList v_sec) [sec.epoch, w_pad]]
    simp only [List.length_append, List.length_singleton, length_ct2SentWordsList,
      length_words5x10List, length_vecWordsList, wordsAt, sepConj_emp,
      bv_add_lit_add_lit_recv, sepConj_assoc]
  simp only [hw_eq, bv_add_lit_add_lit_recv, arm64_norm]
  exact Entails.of_eq (by ac_rfl)

def mkWords63_nhr_tail (g : AuthWords) (ep : BitVec 64) (p : Words5x10)
    (u57 u58 u59 : BitVec 64) (q60 : BitVec 128) (w62 : BitVec 64) : Words63 :=
  { b0 := ⟨g.v1.w0, g.v1.w1, g.v1.w2, g.v2.w0, g.v2.w1, g.v2.w2, ep, p.b0.w0, p.b0.w1, p.b0.w2⟩
    b1 := ⟨p.b0.w3, p.b0.w4, p.b0.w5, p.b0.w6, p.b0.w7, p.b0.w8, p.b0.w9, p.b1.w0, p.b1.w1, p.b1.w2⟩
    b2 := ⟨p.b1.w3, p.b1.w4, p.b1.w5, p.b1.w6, p.b1.w7, p.b1.w8, p.b1.w9, p.b2.w0, p.b2.w1, p.b2.w2⟩
    b3 := ⟨p.b2.w3, p.b2.w4, p.b2.w5, p.b2.w6, p.b2.w7, p.b2.w8, p.b2.w9, p.b3.w0, p.b3.w1, p.b3.w2⟩
    b4 := ⟨p.b3.w3, p.b3.w4, p.b3.w5, p.b3.w6, p.b3.w7, p.b3.w8, p.b3.w9, p.b4.w0, p.b4.w1, p.b4.w2⟩
    b5 := ⟨p.b4.w3, p.b4.w4, p.b4.w5, p.b4.w6, p.b4.w7, p.b4.w8, p.b4.w9, u57, u58, u59⟩
    q60 := q60
    w62 := w62 }

theorem words63List_mkWords63_nhr_tail (g : AuthWords) (ep : BitVec 64) (p : Words5x10)
    (u57 u58 u59 : BitVec 64) (q60 : BitVec 128) (w62 : BitVec 64) :
    words63List (mkWords63_nhr_tail g ep p u57 u58 u59 q60 w62) =
      (ct2SentWordsList g ep ++ words5x10List p) ++
      [u57, u58, u59, q60.extractLsb' 0 64, q60.extractLsb' 64 64, w62] := by
  simp only [words63List, mkWords63_nhr_tail, words5x10List, words10List,
    ct2SentWordsList, authWordsList, vecWordsList, List.append_assoc,
    List.cons_append, List.nil_append]

theorem writeback_noHeaderReceived_some_entails_resultV1RecvAt
    (A : RustAlloc) {F : ShaCompress} (outA : BitVec 64)
    (nhr : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (sec : EpochSecret)
    (g : AuthWords) (p : Words5x10) (v_sec : VecWords)
    (u57 u58 u59 : BitVec 64) (q60 : BitVec 128) (w62 : BitVec 64) :
    relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
      (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
    relocatedHeap (fun dst => vecU8 A dst sec.secret)
      (wordsBytes (vecWordsList v_sec)) ∗
    (outA ↦₆₄ 7#64) ∗
    words63At (outA + 8#64) (mkWords63_nhr_tail g nhr.uc.epoch p u57 u58 u59 q60 w62) ∗
    memRegion (outA + 512#64) 376 ∗
    memRegion (outA + 888#64) 40 ∗
    ((outA + 928#64) ↦₆₄ v_sec.w0) ∗
    ((outA + 936#64) ↦₆₄ v_sec.w1) ∗
    ((outA + 944#64) ↦₁₂₈ (sec.epoch ++ v_sec.w2)) ⊢
      resultV1RecvAt A (F := F) outA (.ok { key := some sec, state := .noHeaderReceived nhr }) := by
  dsimp only [resultV1RecvAt, v1RecvAt, chunkedStatesAt, optEpochSecretAt, epochSecretAt]
  have hw63 :
      words63At (outA + 8#64) (mkWords63_nhr_tail g nhr.uc.epoch p u57 u58 u59 q60 w62) =
      wordsAt (outA + 8#64) (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p) ∗
      wordsAt (outA + 464#64) [u57, u58, u59, q60.extractLsb' 0 64, q60.extractLsb' 64 64, w62] := by
    rw [words63At_eq_wordsAt, words63List_mkWords63_nhr_tail,
        wordsAt_append (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)]
    simp only [List.length_append, length_ct2SentWordsList, length_words5x10List,
      bv_add_lit_add_lit_recv]
  have hsec_words :
      ((outA + 928#64) ↦₆₄ v_sec.w0) ∗
      ((outA + 936#64) ↦₆₄ v_sec.w1) ∗
      ((outA + 944#64) ↦₁₂₈ (sec.epoch ++ v_sec.w2)) =
      wordsAt (outA + 928#64) (vecWordsList v_sec) ∗
      ((outA + 952#64) ↦₆₄ sec.epoch) := by
    simp only [vecWordsList, wordsAt, sepConj_emp, pointsTo128_eq_pair64_recv,
      Leaves.extractLsb'_0_64_append, Leaves.extractLsb'_64_64_append,
      bv_add_lit_add_lit_recv, sepConj_assoc]
  have hnhr_rec :
      wordsAt (outA + 8#64) (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p) ∗
      relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
        (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ⊢
      chunkedNoHeaderReceivedAt A (outA + 8#64) nhr := by
    rw [wordsAt_eq_pointsToBytes]
    exact relocatedHeap_recompose _ _ (outA + 8#64)
  have hsec_rec :
      wordsAt (outA + 928#64) (vecWordsList v_sec) ∗
      relocatedHeap (fun dst => vecU8 A dst sec.secret)
        (wordsBytes (vecWordsList v_sec)) ⊢
      vecU8 A (outA + 928#64) sec.secret := by
    rw [wordsAt_eq_pointsToBytes]
    exact relocatedHeap_recompose _ _ (outA + 928#64)
  have h464 :
      wordsAt (outA + 464#64) [u57, u58, u59, q60.extractLsb' 0 64, q60.extractLsb' 64 64, w62] ∗
      memRegion (outA + 512#64) 376 ∗
      memRegion (outA + 888#64) 40 ⊢
      memRegion (outA + 464#64) 464 := by
    rw [ProofLib.memRegion_split' (b := outA + 464#64) (n := 48) (k := 416)
          (b' := outA + 512#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outA + 512#64) (n := 376) (k := 40)
          (b' := outA + 888#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (wordsAt_entails_memRegion _ (outA + 464#64) 48 rfl)
  rw [hw63, hsec_words, bv_add_lit_add_lit_recv]
  have hreord :
      relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
        (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
      relocatedHeap (fun dst => vecU8 A dst sec.secret)
        (wordsBytes (vecWordsList v_sec)) ∗
      (outA ↦₆₄ 7#64) ∗
      (wordsAt (outA + 8#64) (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p) ∗
       wordsAt (outA + 464#64) [u57, u58, u59, q60.extractLsb' 0 64, q60.extractLsb' 64 64, w62]) ∗
      memRegion (outA + 512#64) 376 ∗
      memRegion (outA + 888#64) 40 ∗
      (wordsAt (outA + 928#64) (vecWordsList v_sec) ∗
       ((outA + 952#64) ↦₆₄ sec.epoch)) =
      ((outA ↦₆₄ 7#64) ∗
       (wordsAt (outA + 8#64) (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p) ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
          (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p))) ∗
       (wordsAt (outA + 464#64) [u57, u58, u59, q60.extractLsb' 0 64, q60.extractLsb' 64 64, w62] ∗
        memRegion (outA + 512#64) 376 ∗
        memRegion (outA + 888#64) 40)) ∗
      ((wordsAt (outA + 928#64) (vecWordsList v_sec) ∗
        relocatedHeap (fun dst => vecU8 A dst sec.secret)
          (wordsBytes (vecWordsList v_sec))) ∗
       ((outA + 952#64) ↦₆₄ sec.epoch)) := by ac_rfl
  rw [hreord]
  exact sepConj_mono
    (sepConj_mono_right (sepConj_mono hnhr_rec h464))
    (sepConj_mono_left hsec_rec)

theorem adrp_add_59974 {b : BitVec 64} (hb : b &&& 0xfff#64 = 0#64) :
    (((b + 0x5005c#64 + 17696#64) &&& 0xfffffffffffff000#64) + bv% (page% (ls_xref% 0x5457c 0x545a0) - 0x54000)) + bv% ((ls_xref% 0x5457c 0x545a0) % 4096) =
      b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
  rw [BitVec.add_assoc b 0x5005c#64 17696#64, adrp_page_of_aligned hb]
  change (b + 0x54000#64) + bv% (page% (ls_xref% 0x5457c 0x545a0) - 0x54000) + bv% ((ls_xref% 0x5457c 0x545a0) % 4096) = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)
  bv_omega

theorem fnAddr_adrp_59974 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    ((((libsignalSessionCode.rebase b H).fnAddr statesRecvName + 17696#64) &&&
      0xfffffffffffff000#64) + bv% (page% (ls_xref% 0x5457c 0x545a0) - 0x54000)) + bv% ((ls_xref% 0x5457c 0x545a0) % 4096) = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
  dsimp only [statesRecvName]
  rw [Program.fnAddr_rebase, CryptoVerification.libsignalSessionCode_fnOff_0x5005c]
  exact adrp_add_59974 hb

theorem memRegion_880_split_504_376_ct2 (a a504 : BitVec 64) (ha : a + 504#64 = a504) :
    memRegion a 880 = memRegion a 504 ∗ memRegion a504 376 :=
  ProofLib.memRegion_split' rfl ha.symm (by decide)

end CryptoVerification.SpqrV1.States.Recv
