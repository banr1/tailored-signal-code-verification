/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.headerSent` Arm, Part 1

Shared `RecvMemcpyOps` writeback helpers and the `msg.epoch > st.uc.epoch`,
`msg.epoch < st.uc.epoch`, and `msg.epoch = st.uc.epoch ∧ msg.payload ≠ .ct1 _` branches of
`.headerSent` (`0x55760`, `+780`).
-/

@[expose] public section

set_option autoImplicit false

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

@[local arm64_norm, local wp_norm]
theorem sp_sub_4240_add_4144_hs (sp : BitVec 64) : (sp - 4240#64) + 4144#64 = sp - 96#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem bv376_toNat_hs : (376#64 : BitVec 64).toNat = 376 := rfl

theorem Relocatable.of_pointsToBytes {n : Nat} (bs : List (BitVec 8)) (hlen : bs.length = n) :
    Relocatable n (fun a => a ↦ₛ bs) := by
  intro a; dsimp only
  refine Entails.sepExists_right bs (Entails.pure_right hlen ?_)
  conv_lhs => rw [← sepConj_emp (a ↦ₛ bs)]
  refine sepConj_mono_right (relocatedHeap_intro emp fun dst => ?_)
  rw [sepConj_emp]
  exact Entails.refl _

theorem epoch_cmp_ct1r_bne_1_of_gt {st_ep msg_ep : BitVec 64} (hgt : msg_ep.toNat > st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) != 1#32) = false := by
  have h1 : st_ep.ule msg_ep = true := by rw [BitVec.ule_eq_decide, decide_eq_true_eq]; omega
  have h2 : msg_ep.ule st_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1, h2]

theorem epoch_cmp_ct1r_bne_1_of_lt {st_ep msg_ep : BitVec 64} (hlt : msg_ep.toNat < st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) != 1#32) = true := by
  have h1 : st_ep.ule msg_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1]

theorem stackAt_statesRecvStackX_split_dropStackPoly64 (sp : BitVec 64) :
    stackAt sp statesRecvStackX =
      memRegion (sp - 23792#64) 19632 ∗ stackAt sp dropStackPoly64 :=
  stackAt_split_bottom sp dropStackPoly64 19632 (by decide)

theorem words63At_376_self_entails_memRegion_928 (selfA tag : BitVec 64) (w : Words63)
    (tailBytes : List (BitVec 8)) (hlen : tailBytes.length = 376) :
    (selfA ↦₆₄ tag) ∗ words63At (selfA + 8#64) w ∗
      ((selfA + 512#64) ↦ₛ tailBytes) ∗ memRegion (selfA + 888#64) 40 ⊢
      memRegion selfA chunkedStatesSize := by
  have h376 : ((selfA + 512#64) ↦ₛ tailBytes) ⊢ memRegion (selfA + 512#64) 376 := by
    rw [← hlen]
    exact ProofLib.pointsToBytes_entails_memRegion (selfA + 512#64) tailBytes
  have h880 : words63At (selfA + 8#64) w ∗ ((selfA + 512#64) ↦ₛ tailBytes) ⊢
      memRegion (selfA + 8#64) 880 :=
    Entails.trans (sepConj_mono_right h376)
      (words63At_376_entails_memRegion_880 (selfA + 8#64) (selfA + 512#64) w (by bv_omega))
  refine Entails.trans (Entails.of_eq (show _ =
    (selfA ↦₆₄ tag) ∗ (words63At (selfA + 8#64) w ∗ ((selfA + 512#64) ↦ₛ tailBytes)) ∗
    memRegion (selfA + 888#64) 40 by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_right (sepConj_mono_left h880))
    (self_880_40_entails_memRegion_928 selfA tag)

/-! ## 1. `.headerSent` (`0x55760`, `+780`): `msg.epoch > st.uc.epoch` -/

/-- `msg.epoch > st.uc.epoch` tail-call block `0x558cc..0x55904` (`+1144 -> s0.x30`) for `.headerSent`:
    writes `Err(EpochOutOfRange(msg.epoch))` to `outA`, restores `sp = s0.sp` and `x19..x30`,
    and tail-calls `0x4c858` (`drop_chunked_header_sent_ok_ext`) on `selfA + 8#64`. -/
theorem headerSent_gt_558cc {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s0 s : State) (outA selfA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (ep : BitVec 64) (P_rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1144#64)
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
        (selfA ↦₆₄ 4#64) ∗
        chunkedHeaderSentAt A (selfA + 8#64) st ∗
        memRegion (selfA + 888#64) 40 ∗
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
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18446744073709515780#64)
      (dropChunkedHeaderSentSpec A F) := Leaves.sub_ok_of_addr_eq
    (fnAddr_bwd_eq_recv (d := 35836) (k := 18446744073709515780) (b := b) (X := Rust.withPanics ext)
      statesRecv_fnOff libsignalSessionCode_fnOff_0x47460 (by decide) rfl).symm
    (drop_chunked_header_sent_ok_ext hdealloc)
  states_recv_fetches_range b (Rust.withPanics ext) 1144 60
  dsimp only [tripleRatchetProgAtExt, statesRecvName, dropChunkedHeaderSentSpec,
    chunkedHeaderSentSize, BitVec.ofNat_eq_ofNat] at hdrop_raw hpc ⊢
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
  have hsplit_sp := stackAt_statesRecvStackX_split_dropStackPoly64 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit_sp) (by sep_focus) ?_
  wp_call hdrop_raw ⟨selfA + 8#64, st⟩
  refine SepWP.focus_weaken (Entails.of_eq hsplit_sp.symm) (by sep_focus) ?_
  refine SepWP.fold
    (F := P_rest ∗ A.pool ∗ stackAt s0.sp statesRecvStackX)
    (sepConj_mono
      (err_epochOutOfRange_entails_resultV1RecvAt A (F := F) outA ep)
      (self_880_40_entails_memRegion_928 selfA 4#64))
    (by ac_rfl) ?_
  wp_done

/-- `.headerSent` arm when `msg.epoch > st.uc.epoch` (`+780 -> s0.x30`, `0x55760..0x55904 -> b 0x4c858`). -/
theorem headerSent_arm_gt
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hgt : msg.epoch > st.uc.epoch)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 780#64)
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
        chunkedStatesAt A selfA (.headerSent st) ∗
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
  have htail := @headerSent_gt_558cc A F b ext hdealloc s0
  states_recv_fetches_range b (Rust.withPanics ext) 780 364
  dsimp only [tripleRatchetProgAtExt, statesRecvName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc htail ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedHeaderSentAt_extract63_376 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w tailBytes
  refine SepWP.pure_elim fun ⟨hw62, htail_len⟩ => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    rw [hw62]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨w.b5.w2, w.b3.w5, w.b3.w1, sp.b0.w3, w.b3.w2, w.b4.w1, w.b4.w0, sp.b0.w7,
             w.b3.w4, w.b3.w3⟩
      b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, w.b3.w6, w.b5.w3, w.b3.w7, sp.b1.w6, w.b5.w9,
             sp.b1.w8, sp.b1.w9⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, sp.b2.w5, w.b4.w8, sp.b2.w7,
             sp.b2.w8, w.b4.w2⟩
      b3 := ⟨sp.b3.w0, w.w62, sp.b3.w2, sp.b3.w3, sp.b3.w4, sp.b3.w5, w.b1.w3, w.b2.w5,
             sp.b3.w8, sp.b3.w9⟩
      b4 := ⟨w.b2.w6, w.b1.w2, sp.b4.w2, w.b1.w0, sp.b4.w4, sp.b4.w5, w.b0.w4, sp.b4.w7,
             sp.b4.w8, w.b2.w3⟩
      b5 := ⟨sp.b5.w0, w.b4.w4, w.b1.w4, w.b0.w8, sp.b5.w4, w.b5.w0, sp.b5.w6, w.b2.w4,
             w.b4.w6, sp.b5.w9⟩
      w60 := w.b5.w6
      w61 := sp.w61
      w62 := w.b0.w6
      q200 := sp.q200
      q210 := sp.q210
      q220 := sp.q220
      w230 := sp.w230
      q3c0 := sp.q3c0 }
  have hfold_frame :
      (words63At (selfA + 8#64) w ∗
       ((selfA + 8#64 + 504#64) ↦ₛ tailBytes) ∗
       relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes)) ∗
      (sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
       memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
       memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
       memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
       sendEkUnusedAt (s0.sp - 4240#64)) ⊢
        chunkedHeaderSentAt A (selfA + 8#64) st ∗
        memRegion (s0.sp - 4240#64) 4144 :=
    sepConj_mono (recompose63_376 (selfA + 8#64) w tailBytes)
      (sendEkFrame_entails_memRegion_4144 (s0.sp - 4240#64) sp1)
  refine SepWP.fold
    (F := P_rest ∗
      memRegion outA v1RecvSize ∗
      (selfA ↦₆₄ 4#64) ∗
      memRegion (selfA + 888#64) 40 ∗
      ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
      A.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      statesRecvSavedCells s0)
    hfold_frame ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    rw [hw62]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  · rw [show (chunkedHeaderSentAt A (selfA + 8#64) st ∗ memRegion (s0.sp - 4240#64) 4144) ∗
        (P_rest ∗
          memRegion outA v1RecvSize ∗
          (selfA ↦₆₄ 4#64) ∗
          memRegion (selfA + 888#64) 40 ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          statesRecvSavedCells s0) =
        (P_rest ∗ ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload)) ∗
        memRegion outA v1RecvSize ∗
        (selfA ↦₆₄ 4#64) ∗
        chunkedHeaderSentAt A (selfA + 8#64) st ∗
        memRegion (selfA + 888#64) 40 ∗
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
    refine Entails.trans hPf (Entails.of_eq (by ac_rfl))

/-! ## 2. Shared `memcpy` / Writeback Operations Bundle & `.headerSent` (`0x55760`, `+780`): `msg.epoch < st.uc.epoch` -/

private structure RecvMemcpyOps (b : BitVec 64) (ext : String → Option (State → State))
    (s0 : State) (Inv : State → Prop) : Prop where
  seq : ∀ {mid_pc : BitVec 64} {s_a : State} {P_a : SepProp}
    {post_a : State → SepProp → Prop},
    Inv s_a →
    SepWP (tripleRatchetProgAtExt b ext) mid_pc s_a P_a
      (fun sm Pm => Inv sm →
        SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm Pm post_a) →
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s_a P_a post_a
  call_memcpy : ∀ {ret_pc : BitVec 64} {F_cp : BitVec 64 → SepProp}
    (hrel : Relocatable 376 F_cp) (dst src : BitVec 64)
    {s_c : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop},
    Inv s_c →
    s_c.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
      bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy") →
    s_c.status = .Running →
    s_c.sp = sp_call →
    (sp_call &&& 15#64 == 0#64) = true →
    s_c.readReg64 Reg.lr = ret_pc →
    TraceCalleeSaved s_c s0 →
    s_c.readReg64 Reg.x0 = dst →
    s_c.readReg64 Reg.x1 = src →
    (s_c.readReg64 Reg.x2).toNat = 376 →
    P = (memRegion dst 376 ∗ F_cp src ∗ stackAt sp_call statesRecvCalleeStackX) ∗ Frame →
    (∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s_c sf → TraceCalleeSaved sf s0 → Inv sf →
      SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        ((F_cp dst ∗ memRegion src 376 ∗ stackAt sp_call statesRecvCalleeStackX) ∗ Frame) post) →
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s_c P post
  writeback : ∀ {F_tail : BitVec 64 → SepProp} (hrel : Relocatable 376 F_tail)
    (sm : State) (outA : BitVec 64) (sp_wb : SendEkSpills) (P_wb : SepProp),
    Inv sm →
    sm.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64 →
    sm.status = .Running →
    sm.sp = s0.sp - 4240#64 →
    s0.spAligned = true →
    sm.readReg64 .x19 = outA →
    TraceCalleeSaved sm s0 →
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm
      (P_wb ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp_wb ∗
        F_tail ((s0.sp - 4240#64) + 576#64) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_wb ∗
          (outA ↦₆₄ sp_wb.b2.w7) ∗
          words63At (outA + 8#64) (writebackWords63 sm sp_wb) ∗
          F_tail (outA + 512#64) ∗
          memRegion (outA + 888#64) 40 ∗
          ((outA + 928#64) ↦₆₄ sp_wb.b2.w8) ∗
          ((outA + 936#64) ↦₆₄ sm.readReg64 .x20) ∗
          ((outA + 944#64) ↦₁₂₈ sp_wb.q200) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)

private theorem recvMemcpyOps_of_memcpy {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 : State) :
    RecvMemcpyOps b ext s0 (fun _ => True) where
  seq _ h := SepWP.seq h (fun _ _ _ _ hw => hw trivial)
  call_memcpy {ret_pc F_cp} hrel dst src {s_c sp_call P Frame post} _ hpc hrun hsp hsp_align hlr
      htrace hx0 hx1 hx2 hsplit hnext := by
    have hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
          bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
        sessionMemcpyRegionSpec := Leaves.sub_ok_of_addr_eq
      (fnAddr_fwd_eq (d := num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
        (b := b) (X := Rust.withPanics ext)
        statesRecv_fnOff (ls_stub% "memcpy") (by decide)).symm hmemcpy
    refine call_memcpy_relocate_cs (ret_pc := ret_pc) hmemcpy_raw hrel dst src
      (Frame := stackAt sp_call statesRecvCalleeStackX ∗ Frame)
      hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2
      (by rw [hsplit]; sep_ac_rfl_recv_ext)
      (fun sf hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
    rw [show (F_cp dst ∗ memRegion src 376) ∗ (stackAt sp_call statesRecvCalleeStackX ∗ Frame) =
        (F_cp dst ∗ memRegion src 376 ∗ stackAt sp_call statesRecvCalleeStackX) ∗ Frame by
      sep_ac_rfl_recv_ext]
    exact hnext sf hpc1 hrun1 hsp1 hcs1 htr1 trivial
  writeback hrel sm outA sp_wb P_wb _ :=
    @states_recv_writeback_59e88 b ext hmemcpy _ hrel s0 sm outA sp_wb P_wb

private theorem recvMemcpyOps_of_alloc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hAx : AllocContractsX img A ext)
    (s0 : State) :
    RecvMemcpyOps img.base ext s0 (ImgCallInv img) where
  seq hinv h := SepWP.seq_inImage hinv h
  call_memcpy {ret_pc F_cp} hrel dst src {s_c sp_call P Frame post} hin hpc hrun hsp hsp_align hlr
      htrace hx0 hx1 hx2 hsplit hnext := by
    have hmemcpy_raw := session_memcpy_region_ok_at_ext_of_alloc hAx statesRecvName
      (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
    exact call_memcpy_relocate_cs_inImage_stk_ext (ret_pc := ret_pc)
      (stk := statesRecvCalleeStackX) (k_stk := 3168)
      hmemcpy_raw hrel dst src hin hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2
      (by decide) (by decide) hsplit hnext
  writeback hrel sm outA sp_wb P_wb :=
    @states_recv_writeback_59e88_ext img A ext hAx _ hrel s0 sm outA sp_wb P_wb

set_option maxHeartbeats 1200000 in
private theorem headerSent_arm_lt_gen
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    {Inv : State → Prop}
    (s0 s : State) (ops : RecvMemcpyOps b ext s0 Inv)
    (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hinv_img : Inv s)
    (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 780#64)
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
        chunkedStatesAt A selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerSent st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  apply ops.seq
    (mid_pc := (tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
      bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")) hinv_img
  have hlt_nat : msg.epoch.toNat < st.uc.epoch.toNat := BitVec.lt_def.mp hlt
  have hcond1 := epoch_cmp_ct1r_eq_of_lt hlt_nat
  have hcond2 := epoch_cmp_ct1r_bne_1_of_lt hlt_nat
  have hmc := @ops.call_memcpy
  have hseq := @ops.seq
  states_recv_fetches_range b (Rust.withPanics ext) 780 364
  states_recv_fetches_range b (Rust.withPanics ext) 10376 124
  states_recv_fetches_range b (Rust.withPanics ext) 11316 80
  dsimp only [tripleRatchetProgAtExt, statesRecvName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hmc hseq ⊢
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedHeaderSentAt_extract63_376 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w tailBytes
  refine SepWP.pure_elim fun ⟨hw62, htail_len⟩ => ?_
  have hrel_tail := Relocatable.of_pointsToBytes tailBytes htail_len
  have hwb := @ops.writeback (F_tail := fun a => a ↦ₛ tailBytes) hrel_tail
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hwb
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  have h512 : selfA + 8#64 + 504#64 = selfA + 512#64 := by bv_omega
  rw [h512]
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    rw [hw62]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 200
  refine SepWP.done rfl (by exact hrun) fun hinv_call => ?_
  refine hmc (ret_pc := entry + 10476#64) hrel_tail
    (sp0 - 3664#64) (selfA + 512#64)
    hinv_call rfl (by exact hrun) (by exact hsp) hfsp_align rfl (by exact htr) rfl
    (by simp only [Reg.x1, arm64_norm, hx1]) rfl
    (by sep_frame) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1 hinv1
  have hx19_1 : sf1.readReg64 .x19 = outA :=
    hcs1.1.trans (by simp only [Reg.x19, arm64_norm, hx19])
  have hx20_1 : sf1.readReg64 .x20 = w.b1.w5 := hcs1.2.1
  have hx22_1 : sf1.readReg64 .x22 = w.b0.w0 := hcs1.2.2.2.1
  have hx25_1 : sf1.readReg64 .x25 = w.b0.w1 := hcs1.2.2.2.2.2.2.1
  have hx28_1 : sf1.readReg64 .x28 = w.b1.w6 := hcs1.2.2.2.2.2.2.2.2.2.1
  apply hseq (mid_pc := entry + 18996#64) hinv1
  wp_steps
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨w.b5.w2, w.b3.w5, w.b3.w1, w.b2.w9, w.b3.w2, w.b4.w1, w.b4.w0, w.b3.w8,
             w.b3.w4, w.b3.w3⟩
      b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, w.b3.w6, w.b5.w3, w.b3.w7, sp.b1.w6, w.b5.w9,
             sp.b1.w8, sp.b1.w9⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, sp.b2.w5, w.b4.w8, 4#64,
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
  have hfold_self_sp :
      ((selfA ↦₆₄ 4#64) ∗ words63At (selfA + 8#64) w ∗
       memRegion (selfA + 512#64) 376 ∗ memRegion (selfA + 888#64) 40) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion selfA chunkedStatesSize ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 := by
    have h880 := words63At_376_entails_memRegion_880 (selfA + 8#64) (selfA + 512#64) w (by bv_omega)
    have h928 : (selfA ↦₆₄ 4#64) ∗ (words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 376) ∗
        memRegion (selfA + 888#64) 40 ⊢ memRegion selfA chunkedStatesSize :=
      Entails.trans (sepConj_mono_right (sepConj_mono_left h880))
        (self_880_40_entails_memRegion_928 selfA 4#64)
    refine sepConj_mono_left (Entails.trans (Entails.of_eq (by ac_rfl)) h928)
  have h3664 : s0.sp - 3664#64 = (s0.sp - 4240#64) + 576#64 := by bv_omega
  rw [h3664]
  refine SepWP.fold
    (F := P_rest ∗
      relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
      ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
      A.pool ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
      memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗
      statesRecvSavedCells s0)
    hfold_self_sp ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    rw [hw62]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [show (memRegion selfA chunkedStatesSize ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0) =
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool) ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.done rfl hrun1 fun hinv_wb => ?_
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool)
        hinv_wb rfl hrun1 hsp1 hsp_align
        (by simp only [Reg.x19, arm64_norm, hx19_1])
        htr1)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_headerSent_entails_resultV1RecvAt A (F := F) outA st w tailBytes
      w.b5.w9 sp.q200
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_left hrec))
    dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
      Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
      Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      Reg.x30]
    simp only [arm64_norm, hx20_1, hx22_1, hx25_1, hx28_1, ← hw62]
    ac_rfl

/-- `.headerSent` arm when `msg.epoch < st.uc.epoch`
    (`+780 -> s0.x30`, `0x55760..0x558c8 -> 0x57cdc..0x57d54 -> 0x58088..0x580d4 -> 0x59e88..0x59ff0`). -/
theorem headerSent_arm_lt
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 780#64)
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
        chunkedStatesAt A selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerSent st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) :=
  headerSent_arm_lt_gen s0 s (recvMemcpyOps_of_memcpy hmemcpy s0)
    outA selfA msgA st msg P_rest trivial hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr

/-- `.headerSent` arm when `msg.epoch < st.uc.epoch` under `AllocContractsX`. -/
theorem headerSent_arm_lt_hs_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hinv_img : ImgCallInv img s)
    (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 780#64)
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
        chunkedStatesAt A selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerSent st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) :=
  headerSent_arm_lt_gen s0 s (recvMemcpyOps_of_alloc hAx s0)
    outA selfA msgA st msg P_rest hinv_img hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr

/-! ## 3. `.headerSent` (`0x55760`, `+780`): `msg.epoch = st.uc.epoch` and `msg.payload ≠ .ct1 _` -/

set_option maxHeartbeats 1200000 in
private theorem headerSent_arm_eq_other_gen
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    {Inv : State → Prop}
    (s0 s : State) (ops : RecvMemcpyOps b ext s0 Inv)
    (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hinv_img : Inv s)
    (heq : msg.epoch = st.uc.epoch)
    (hct1 : ∀ c, msg.payload ≠ .ct1 c)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 780#64)
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
        chunkedStatesAt A selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerSent st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  apply ops.seq
    (mid_pc := (tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
      bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")) hinv_img
  have hcond_eq := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hcond_tag1 := messagePayloadTag_eq_5_of_not_ct1 hct1
  have hcond_tag2 := messagePayloadTag_bne_5_of_not_ct1 hct1
  have hmc := @ops.call_memcpy
  have hseq := @ops.seq
  states_recv_fetches_range b (Rust.withPanics ext) 780 356
  states_recv_fetches_range b (Rust.withPanics ext) 5056 12
  states_recv_fetches_range b (Rust.withPanics ext) 11196 200
  dsimp only [tripleRatchetProgAtExt, statesRecvName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hmc hseq ⊢
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedHeaderSentAt_extract63_376 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w tailBytes
  refine SepWP.pure_elim fun ⟨hw62, htail_len⟩ => ?_
  have hrel_tail := Relocatable.of_pointsToBytes tailBytes htail_len
  have hwb := @ops.writeback (F_tail := fun a => a ↦ₛ tailBytes) hrel_tail
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hwb
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  have h512 : selfA + 8#64 + 504#64 = selfA + 512#64 := by bv_omega
  rw [h512]
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    rw [hw62, heq, messagePayloadAt_eq_tag_tail msgA msg.payload]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 200
  refine SepWP.done rfl (by exact hrun) fun hinv_call => ?_
  refine hmc (ret_pc := entry + 11296#64) hrel_tail
    (sp0 - 3664#64) (selfA + 512#64)
    hinv_call rfl (by exact hrun) (by exact hsp) hfsp_align rfl (by exact htr) rfl
    (by simp only [Reg.x1, arm64_norm, hx1]) rfl
    (by sep_frame) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1 hinv1
  have hx19_1 : sf1.readReg64 .x19 = outA :=
    hcs1.1.trans (by simp only [Reg.x19, arm64_norm, hx19])
  have hx22_1 : sf1.readReg64 .x22 = w.b1.w5 := hcs1.2.2.2.1
  have hx25_1 : sf1.readReg64 .x25 = w.b0.w1 := hcs1.2.2.2.2.2.2.1
  have hx28_1 : sf1.readReg64 .x28 = w.b1.w6 := hcs1.2.2.2.2.2.2.2.2.2.1
  apply hseq (mid_pc := entry + 18996#64) hinv1
  wp_steps
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨w.b5.w2, w.b3.w5, w.b3.w1, w.b2.w9, w.b3.w2, w.b4.w1, w.b4.w0, w.b3.w8,
             w.b3.w4, w.b3.w3⟩
      b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, w.b3.w6, w.b5.w3, w.b3.w7, w.b0.w0, w.b5.w9,
             sp.b1.w8, sp.b1.w9⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, sp.b2.w5, w.b4.w8, 4#64,
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
  have hfold_self_sp :
      ((selfA ↦₆₄ 4#64) ∗ words63At (selfA + 8#64) w ∗
       memRegion (selfA + 512#64) 376 ∗ memRegion (selfA + 888#64) 40) ∗
      (((msgA + 8#64) ↦₈ messagePayloadTag msg.payload) ∗ messagePayloadTailAt msgA msg.payload) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion selfA chunkedStatesSize ∗
        messagePayloadAt spqrPolyApi msgA msg.payload ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 := by
    have h880 := words63At_376_entails_memRegion_880 (selfA + 8#64) (selfA + 512#64) w (by bv_omega)
    have h928 : (selfA ↦₆₄ 4#64) ∗ (words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 376) ∗
        memRegion (selfA + 888#64) 40 ⊢ memRegion selfA chunkedStatesSize :=
      Entails.trans (sepConj_mono_right (sepConj_mono_left h880))
        (self_880_40_entails_memRegion_928 selfA 4#64)
    refine sepConj_mono (Entails.trans (Entails.of_eq (by ac_rfl)) h928)
      (sepConj_mono_left (Entails.of_eq (messagePayloadAt_eq_tag_tail msgA msg.payload).symm))
  have h3664 : s0.sp - 3664#64 = (s0.sp - 4240#64) + 576#64 := by bv_omega
  rw [h3664]
  refine SepWP.fold
    (F := P_rest ∗
      relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
      (msgA ↦₆₄ msg.epoch) ∗
      A.pool ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
      memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗
      statesRecvSavedCells s0)
    hfold_self_sp ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    rw [hw62, heq]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [show (memRegion selfA chunkedStatesSize ∗
          messagePayloadAt spqrPolyApi msgA msg.payload ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
          (msgA ↦₆₄ msg.epoch) ∗
          A.pool ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0) =
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool) ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.done rfl hrun1 fun hinv_wb => ?_
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool)
        hinv_wb rfl hrun1 hsp1 hsp_align
        (by simp only [Reg.x19, arm64_norm, hx19_1])
        htr1)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_headerSent_entails_resultV1RecvAt A (F := F) outA st w tailBytes
      w.b5.w9 sp.q200
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_left hrec))
    dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
      Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
      Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      Reg.x30]
    simp only [arm64_norm, hx22_1, hx25_1, hx28_1, ← hw62]
    ac_rfl

/-- `.headerSent` arm when `msg.epoch = st.uc.epoch` and `∀ c, msg.payload ≠ .ct1 c`
    (`+780 -> s0.x30`, `0x55760..0x558c0 -> 0x56814..0x5681c -> 0x58010..0x580d4 -> 0x59e88..0x59ff0`). -/
theorem headerSent_arm_eq_other
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (heq : msg.epoch = st.uc.epoch)
    (hct1 : ∀ c, msg.payload ≠ .ct1 c)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 780#64)
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
        chunkedStatesAt A selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerSent st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) :=
  headerSent_arm_eq_other_gen s0 s (recvMemcpyOps_of_memcpy hmemcpy s0)
    outA selfA msgA st msg P_rest trivial heq hct1 hpc hrun hsp hsp_align hx1 hx19 hx24 htr

/-- `.headerSent` arm when `msg.epoch = st.uc.epoch` and `∀ c, msg.payload ≠ .ct1 c`
    under `AllocContractsX`. -/
theorem headerSent_arm_eq_other_hs_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hinv_img : ImgCallInv img s)
    (heq : msg.epoch = st.uc.epoch)
    (hct1 : ∀ c, msg.payload ≠ .ct1 c)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 780#64)
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
        chunkedStatesAt A selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerSent st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) :=
  headerSent_arm_eq_other_gen s0 s (recvMemcpyOps_of_alloc hAx s0)
    outA selfA msgA st msg P_rest hinv_img heq hct1 hpc hrun hsp hsp_align hx1 hx19 hx24 htr

end CryptoVerification.SpqrV1.States.Recv
