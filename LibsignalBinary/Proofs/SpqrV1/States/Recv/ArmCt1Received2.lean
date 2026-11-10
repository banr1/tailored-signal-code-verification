/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchExt
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Received` Arm, Part 2

**Checked by Lean.** Verifies `ct1Received_arm_eq_other`, `ct1Received_arm_eq_ct2`, and the
complete `.ct1Received` arm (`states_recv_arm_ct1Received`, `0x55908`, `+1204`).
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
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
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

/-- Discriminant byte at `msgA + 8#64` of `MessagePayload spqrPolyApi`. -/
def messagePayloadTag (p : MessagePayload spqrPolyApi) : BitVec 8 :=
  match p with
  | .none => 0#8
  | .hdr _ => 1#8
  | .ek _ => 2#8
  | .ekCt1Ack _ => 3#8
  | .ct1Ack _ => 4#8
  | .ct1 _ => 5#8
  | .ct2 _ => 6#8

/-- Tail (`39` bytes at `msgA + 9#64`) of `messagePayloadAt spqrPolyApi msgA p`. -/
def messagePayloadTailAt (a : BitVec 64) (p : MessagePayload spqrPolyApi) : SepProp :=
  match p with
  | .none => memRegion (a + 0x09#64) 39
  | .hdr c | .ek c | .ekCt1Ack c | .ct1 c | .ct2 c =>
      memRegion (a + 0x09#64) 1 ∗ chunkAt (a + 0x0a#64) c ∗ memRegion (a + 0x2c#64) 4
  | .ct1Ack b =>
      ((a + 0x09#64) ↦₈ (if b then 1#8 else 0#8)) ∗ memRegion (a + 0x0a#64) 38

theorem messagePayloadAt_eq_tag_tail (a : BitVec 64) (p : MessagePayload spqrPolyApi) :
    messagePayloadAt spqrPolyApi a p =
      ((a + 8#64) ↦₈ messagePayloadTag p) ∗ messagePayloadTailAt a p := by
  cases p <;> rfl

theorem messagePayloadTag_eq_6_of_not_ct2 {p : MessagePayload spqrPolyApi} (h : ∀ c, p ≠ .ct2 c) :
    (BitVec.zeroExtend 32 (messagePayloadTag p) == 6#32) = false := by
  cases p with
  | ct2 c => exact absurd rfl (h c)
  | _ => rfl

theorem messagePayloadTag_bne_6_of_not_ct2 {p : MessagePayload spqrPolyApi} (h : ∀ c, p ≠ .ct2 c) :
    (BitVec.zeroExtend 32 (messagePayloadTag p) != 6#32) = true := by
  cases p with
  | ct2 c => exact absurd rfl (h c)
  | _ => rfl

set_option autoImplicit false in
set_option maxHeartbeats 1200000 in
private theorem ct1Received_arm_eq_other_core
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    {Inv : State → Prop} {calleeStk finalStk : Nat}
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (P_rest : SepProp)
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
    (heq : msg.epoch = st.uc.epoch) (hct2 : ∀ c, msg.payload ≠ .ct2 c)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1204#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ A.pool ∗ stackAt (s0.sp - 4240#64) calleeStk ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sm Pm => Inv sm →
        SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm Pm
          (fun sf Pf =>
            (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Received st }) ∗
              memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
              A.pool ∗ stackAt s0.sp finalStk) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) := by
  have hcond1 := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hcond_tag1 := messagePayloadTag_eq_6_of_not_ct2 hct2
  have hcond_tag2 := messagePayloadTag_bne_6_of_not_ct2 hct2
  states_recv_fetches_range b (Rust.withPanics ext) 1204 316
  states_recv_fetches_range b (Rust.withPanics ext) 5764 16
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
    rw [hw62, heq, messagePayloadAt_eq_tag_tail msgA msg.payload]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
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
      w60 := w.b5.w6, w61 := w.b0.w2, w62 := w.b0.w6
      q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := w.q60 }
  have hfold_unused :
      ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗ memRegion (s0.sp - 4240#64) 8 ∗
      memRegion (s0.sp - 4240#64 + 568#64) 8 ∗ memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
      memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗ memRegion (s0.sp - 4240#64 + 2768#64) 1376 ⊢
        sendEkUnusedAt (s0.sp - 4240#64) :=
    sendEkUnusedAt_rejoin_ac0 (s0.sp - 4240#64) w.q60
  have hfold_self_unused :
      ((selfA ↦₆₄ 5#64) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416) ∗
      (((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗ memRegion (s0.sp - 4240#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 568#64) 8 ∗ memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗ memRegion (s0.sp - 4240#64 + 2768#64) 1376) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion selfA chunkedStatesSize ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono (words63At_self_entails_memRegion_928 selfA 5#64 w)
      (sepConj_mono_left hfold_unused)
  refine SepWP.fold
    (F := P_rest ∗
      relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
      ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool ∗
      memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) calleeStk ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ statesRecvSavedCells s0)
    hfold_self_unused ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    rw [hw62, heq, messagePayloadAt_eq_tag_tail msgA msg.payload]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    sep_ac_rfl_recv_ext
  · rw [show (memRegion selfA chunkedStatesSize ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗ relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool ∗
          memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) calleeStk ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ statesRecvSavedCells s0) =
        (P_rest ∗ relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool) ∗
        memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) calleeStk ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0 by sep_ac_rfl_recv_ext]
    refine SepWP.done rfl hrun fun hinv_wb => ?_
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗ relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool)
        hinv_wb rfl hrun hsp hsp_align (by simp only [Reg.x19, arm64_norm, hx19]) htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_ct1Received_entails_resultV1RecvAt A (F := F) outA st w w.b5.w9 sp.q200
    refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_right (sepConj_mono_left hrec))
    dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
      Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
      Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      Reg.x30]
    simp only [arm64_norm, hx1]
    sep_ac_rfl_recv_ext

set_option autoImplicit false in
/-- `.ct1Received` arm when `msg.epoch = st.uc.epoch` and `msg.payload ≠ .ct2 _`
    (`+1204 -> s0.x30`, `0x55908..0x55a40 -> 0x56ad8..0x56ae4 -> 0x56ef8..0x56fdc -> 0x59e88..0x59ff0`). -/
theorem ct1Received_arm_eq_other
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (P_rest : SepProp)
    (heq : msg.epoch = st.uc.epoch) (hct2 : ∀ c, msg.payload ≠ .ct2 c)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1204#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Received st }) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  SepWP.seq
    (ct1Received_arm_eq_other_core (Inv := fun _ => True) s0 s outA selfA msgA st msg P_rest
      (fun sm outA sp P_rest _ => @states_recv_writeback_59e88 b ext hmemcpy
        (F_tail := fun a => memRegion a 376) (Relocatable.of_memRegion 376) s0 sm outA sp P_rest)
      heq hct2 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
    (fun _ _ _ _ h => h trivial)

set_option autoImplicit false in
/-- `.ct1Received` arm when `msg.epoch = st.uc.epoch` and `msg.payload ≠ .ct2 _`
    (`+1204 -> +18996 -> lr`) under `AllocContractsX`. -/
theorem ct1Received_arm_eq_other_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (P_rest : SepProp)
    (hinv_img : ImgCallInv img s)
    (heq : msg.epoch = st.uc.epoch) (hct2 : ∀ c, msg.payload ≠ .ct2 c)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 1204#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Received st }) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          A.pool ∗ stackAt s0.sp statesRecvStackXExt) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  CryptoVerification.LibsignalTripleRatchet.SepWP.seq_inImage hinv_img
    (ct1Received_arm_eq_other_core s0 s outA selfA msgA st msg P_rest
      (fun sm outA sp P_rest => @states_recv_writeback_59e88_stk_ext img A ext hAx
        (F_tail := fun a => memRegion a 376) (Relocatable.of_memRegion 376) s0 sm outA sp P_rest)
      heq hct2 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)

theorem memRegion_880_entails_words63_376 (a a504 : BitVec 64) (ha : a + 504#64 = a504) :
    memRegion a 880 ⊢ ∃∗ w : Words63, words63At a w ∗ memRegion a504 376 := by
  rw [memRegion_880_split_504_376 a a504 ha]
  refine Entails.trans (sepConj_mono_left (memRegion_504_entails_words63At a)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w
  exact Entails.sepExists_right w (Entails.refl _)

theorem messagePayloadAt_ct2 (a : BitVec 64) (c : Chunk) :
    messagePayloadAt spqrPolyApi a (.ct2 c) =
      ((a + 8#64) ↦₈ 6#8) ∗ memRegion (a + 9#64) 1 ∗
        chunkAt (a + 10#64) c ∗ memRegion (a + 44#64) 4 := rfl

theorem fnAddr_fwd_ct1RecvCt2 {b : BitVec 64} {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr ct1ReceivedRecvCt2ChunkName =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr statesRecvName + 36512#64 := by
  dsimp only [tripleRatchetProgAtExt, statesRecvName, ct1ReceivedRecvCt2ChunkName]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      CryptoVerification.libsignalSessionCode_fnOff_0x5005c,
      CryptoVerification.libsignalSessionCode_fnOff_0x58efc]
  bv_omega

/-- Framed call rule for `ct1ReceivedRecvCt2ChunkSpec A F` (`0x5e2f4`), bridging from `SepWP`
    before the call to `SepWPp` (propagating `allocFailedIn s0 sf`) and back to `SepWP` after the call. -/
theorem call_ct1ReceivedRecvCt2Chunk {A : RustAlloc} {F : ShaCompress}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (ct1ReceivedRecvCt2ChunkSpec A F))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (hrecv : st.recv_ct2_chunk st.uc.epoch chunk = .ok outSt)
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
      chunkedCt1ReceivedAt A stA st ∗ chunkAt chunkA chunk ∗
      A.pool ∗ stackAt sp_call ct1ReceivedRecvCt2ChunkStack) ∗ Frame)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) →
      Q_panic sf P_f)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((chunkedEkSentCt1ReceivedAt A outA outSt ∗
          memRegion stA chunkedCt1ReceivedSize ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call ct1ReceivedRecvCt2ChunkStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Q_panic) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨outA, stA, chunkA, st, chunk, outSt⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ => hpanic sf _ fun hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [ct1ReceivedRecvCt2ChunkSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hrecv⟩, hm⟩
  · dsimp only [ct1ReceivedRecvCt2ChunkSpec] at hmem
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace.1] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [ct1ReceivedRecvCt2ChunkSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (chunkedEkSentCt1ReceivedAt A outA outSt ∗
          memRegion stA chunkedCt1ReceivedSize ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call ct1ReceivedRecvCt2ChunkStack) ∗ Frame =
        (chunkedEkSentCt1ReceivedAt A outA outSt ∗
          (memRegion stA chunkedCt1ReceivedSize ∗
            (chunkAt chunkA chunk ∗ (A.pool ∗ stackAt sp_call ct1ReceivedRecvCt2ChunkStack)))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

set_option autoImplicit false in
private theorem call_ct1ReceivedRecvCt2Chunk_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      ((growToCalleeExt ct1ReceivedRecvCt2ChunkStack
        (ct1ReceivedRecvCt2ChunkSpec A F)).inImage img))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (hrecv : st.recv_ct2_chunk st.uc.epoch chunk = .ok outSt)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post Q_panic : State → SepProp → Prop}
    (hinv_img : ImgCallInv img s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.uc.epoch) (hx3 : s.readReg64 Reg.x3 = chunkA)
    (hsplit : P = (memRegion outA chunkedEkSentCt1ReceivedSize ∗
      chunkedCt1ReceivedAt A stA st ∗ chunkAt chunkA chunk ∗
      A.pool ∗ stackAt sp_call statesRecvCalleeStackXExt) ∗ Frame)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) →
      Q_panic sf P_f)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      ImgCallInv img sf →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((chunkedEkSentCt1ReceivedAt A outA outSt ∗
          memRegion stA chunkedCt1ReceivedSize ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call statesRecvCalleeStackXExt) ∗ Frame) post) :
    SepWPp prog (s0.readReg64 Reg.lr) s P post Q_panic := by
  refine CryptoVerification.LibsignalTripleRatchet.SepWPp.call_inImage hcall hinv_img
    (x := ⟨outA, stA, chunkA, st, chunk, outSt⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ => hpanic sf _ fun hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [growToCalleeExt, ct1ReceivedRecvCt2ChunkSpec]
    rw [hsp]
    rw [stackAt_statesRecvCalleeExt_split sp_call ct1ReceivedRecvCt2ChunkStack] at hm
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hrecv⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl_recv_ext)) hm⟩
  · dsimp only [Spec.inImage, growToCalleeExt, ct1ReceivedRecvCt2ChunkSpec] at hmem
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace.1] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [Spec.inImage, growToCalleeExt, ct1ReceivedRecvCt2ChunkSpec]
    simp only [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre ?_
      (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
        ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hinv_sf)
    rw [stackAt_statesRecvCalleeExt_split sp_call ct1ReceivedRecvCt2ChunkStack]
    exact Entails.of_eq (by sep_ac_rfl_recv_ext)

set_option autoImplicit false in
set_option maxHeartbeats 1600000 in
private theorem ct1Received_arm_eq_ct2_step_to_call
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    {calleeStk : Nat}
    (hb : b &&& 0xfff#64 = 0#64)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (P_rest : SepProp)
    {post_call : State → SepProp → Prop}
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ct2 chunk)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1204#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0)
    (hcont : ∀ (sm : State) (sp1 : SendEkSpills),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr ct1ReceivedRecvCt2ChunkName →
      sm.status = .Running → sm.sp = s0.sp - 4240#64 →
      sm.readReg64 Reg.lr = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 6436#64 →
      TraceCalleeSaved sm s0 →
      sm.readReg64 Reg.x19 = outA →
      sm.readReg64 Reg.x0 = (s0.sp - 4240#64) + 976#64 →
      sm.readReg64 Reg.x1 = (s0.sp - 4240#64) + 1856#64 →
      sm.readReg64 Reg.x2 = st.uc.epoch →
      sm.readReg64 Reg.x3 = msgA + 10#64 →
      post_call sm
        (memRegion ((s0.sp - 4240#64) + 976#64) 504 ∗
          chunkedCt1ReceivedAt A ((s0.sp - 4240#64) + 1856#64) st ∗
          chunkAt (msgA + 10#64) chunk ∗ A.pool ∗ stackAt (s0.sp - 4240#64) calleeStk ∗
          P_rest ∗ memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
            memRegion (msgA + 44#64) 4) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          memRegion outA v1RecvSize ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
          statesRecvSavedCells s0)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ct1ReceivedRecvCt2ChunkName) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        A.pool ∗ stackAt (s0.sp - 4240#64) calleeStk ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      post_call := by
  have hcond1 := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hadrp := fnAddr_adrp_56ae8 (b := b) (H := Rust.withPanics ext) hb
  rw [fnAddr_fwd_ct1RecvCt2] at hcont ⊢
  states_recv_fetches_range b (Rust.withPanics ext) 1204 316
  states_recv_fetches_range b (Rust.withPanics ext) 5764 44
  states_recv_fetches_range b (Rust.withPanics ext) 6016 420
  dsimp only [tripleRatchetProgAtExt, statesRecvName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hadrp hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (sendEkUnusedAt_split_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i u_ac0
  refine SepWP.fold (memRegion_880_entails_words63_376
    ((s0.sp - 4240#64) + 1856#64) ((s0.sp - 4240#64) + 2360#64) (by bv_omega)) (by sep_focus) ?_
  wp_pull_exists; rename_i w_arg
  refine SepWP.fold (chunkedCt1ReceivedAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw62 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    rw [hw62, heq, hpay, messagePayloadAt_ct2 msgA chunk]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 256
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨w.b5.w2, sp.b0.w1, w.b3.w1, sp.b0.w3, sp.b0.w4, sp.b0.w5, w.b4.w0, sp.b0.w7,
             sp.b0.w8, w.b3.w3⟩
      b1 := ⟨sp.b1.w0, sp.b1.w1, w.b3.w9, sp.b1.w3, w.b5.w3, sp.b1.w5, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, sp.b2.w3, w.b4.w5, w.b0.w1, w.b4.w8, sp.b2.w7,
             msgA, w.b4.w2⟩
      b3 := ⟨w.b5.w8, w.w62, sp.b3.w2, sp.b3.w3, sp.b3.w4, sp.b3.w5, sp.b3.w6, sp.b3.w7,
             w.b3.w0, sp.b3.w9⟩
      b4 := ⟨sp.b4.w0, w.b1.w2, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, sp.b4.w6, w.b1.w1,
             w.b2.w0, w.b2.w3⟩
      b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, w.b5.w0, sp.b5.w6, w.b2.w4,
             w.b4.w6, w.b5.w4⟩
      w60 := w.b5.w6, w61 := w.b0.w2, w62 := w.b0.w6
      q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := sp.q3c0 }
  have hfold_unused :
      ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗ memRegion (s0.sp - 4240#64) 8 ∗
      memRegion (s0.sp - 4240#64 + 568#64) 8 ∗ memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
      memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗ memRegion (s0.sp - 4240#64 + 2768#64) 1376 ⊢
        sendEkUnusedAt (s0.sp - 4240#64) :=
    sendEkUnusedAt_rejoin_ac0 (s0.sp - 4240#64) w.q60
  have hfold_pre_call :
      ((selfA ↦₆₄ 5#64) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416) ∗
      (words63At ((s0.sp - 4240#64) + 1856#64) w ∗
       relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w))) ∗
      (((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗ memRegion (s0.sp - 4240#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 568#64) 8 ∗ memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗ memRegion (s0.sp - 4240#64 + 2768#64) 1376) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion selfA chunkedStatesSize ∗ chunkedCt1ReceivedAt A ((s0.sp - 4240#64) + 1856#64) st ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono (words63At_self_entails_memRegion_928 selfA 5#64 w)
      (sepConj_mono (recompose63 ((s0.sp - 4240#64) + 1856#64) w)
        (sepConj_mono_left hfold_unused))
  refine SepWP.fold
    (F := P_rest ∗
      ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
        chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) ∗
      ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      A.pool ∗ memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) calleeStk ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗ statesRecvSavedCells s0)
    hfold_pre_call ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    rw [hw62, heq]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    sep_ac_rfl_recv_ext
  · refine SepWP.focus_weaken
      (Entails.of_eq (memRegion_880_split_504_376
        ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) (by bv_omega)))
      (by sep_focus) ?_
    refine SepWP.weaken_pre ?_
      (SepWP.done rfl hrun
        (hcont _ sp1 rfl hrun hsp
          (by simp only [Reg.lr, arm64_norm]) htr
          (by simp only [Reg.x19, arm64_norm, hx19])
          (by simp only [Reg.x0, arm64_norm]) (by simp only [Reg.x1, arm64_norm])
          (by simp only [Reg.x2, arm64_norm]) (by simp only [Reg.x3, arm64_norm])))
    exact Entails.of_eq (by simp only [arm64_norm]; sep_ac_rfl_recv_ext)

set_option autoImplicit false in
/-- `.ct1Received` arm when `msg.epoch = st.uc.epoch` and `msg.payload = .ct2 chunk`
    (`+1204 -> s0.x30`, `0x55908..0x55a40 -> 0x56ad8..0x56b00 -> 0x56bd4..0x56d74 -> 0x56d78..0x59ff0`). -/
theorem ct1Received_arm_eq_ct2
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (hcall : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ct1ReceivedRecvCt2ChunkName)
      (ct1ReceivedRecvCt2ChunkSpec A F))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (P_rest R : SepProp) {Q_post Q_panic : State → SepProp → Prop}
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ct2 chunk)
    (hrecv : st.recv_ct2_chunk st.uc.epoch chunk = .ok outSt)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1204#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0)
    (hdone : ∀ (sf : State) (Pf : SepProp), sf.pc = s0.readReg64 Reg.lr → sf.status = .Running →
      (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekSentCt1Received outSt }) ∗
        memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace → Q_post sf Pf)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) →
      Q_panic sf P_f) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ct1ReceivedRecvCt2ChunkName) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sm Pm =>
        SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) sm Pm Q_post Q_panic) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  refine ct1Received_arm_eq_ct2_step_to_call hb s0 s outA selfA msgA st msg chunk P_rest
    heq hpay hpc hrun hsp hsp_align hx1 hx19 hx24 htr ?_
  intro sm sp1 hpc_m hrun_m hsp_m hlr_m htr_m hx19_m hx0_m hx1_m hx2_m hx3_m
  refine SepWPp.of_sepWP
    (call_ct1ReceivedRecvCt2Chunk hcall
      ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1856#64) (msgA + 10#64)
      st chunk outSt hrecv
      (s0 := s0) (sp_call := s0.sp - 4240#64)
      (ret_pc := (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 6436#64) (R := R)
      (Frame := P_rest ∗ memRegion selfA chunkedStatesSize ∗
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
          memRegion (msgA + 44#64) 4) ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        memRegion outA v1RecvSize ∗ memRegion ((s0.sp - 4240#64) - 19552#64) 2576 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗ statesRecvSavedCells s0)
      hpc_m hrun_m hsp_m hfsp_align hlr_m htr_m hx0_m hx1_m hx2_m hx3_m
      (by
        rw [stackAt_statesRecvCallee_split_ct1RecvCt2 (s0.sp - 4240#64)]
        dsimp only [chunkedEkSentCt1ReceivedSize, statesRecvCalleeStackX, recvCt2ChunkStackX,
          recvCt2ChunkFrameBytes, polyDecodedMessageStackX, extHookStack,
          ct1ReceivedRecvCt2ChunkStack, BitVec.ofNat_eq_ofNat]
        simp only [arm64_norm]; sep_ac_rfl_recv_ext)
      hpanic ?_)
  intro sf_c hpc_c hrun_c hsp_c hcs_c htr_c
  refine SepWP.focus_weaken
    (Entails.of_eq (memRegion_880_split_504_376
      ((s0.sp - 4240#64) + 1856#64) ((s0.sp - 4240#64) + 2360#64) (by bv_omega)).symm)
    (by sep_focus) ?_
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_statesRecvCallee_split_ct1RecvCt2 (s0.sp - 4240#64)).symm)
    (by sep_focus) ?_
  have hmsg_eq :
      ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
       chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) =
      ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) := by
    rw [hpay, messagePayloadAt_ct2 msgA chunk]
  have hx19_c : sf_c.readReg64 .x19 = outA := by
    dsimp only [Reg.x19] at hx19_m ⊢; exact hcs_c.1.trans hx19_m
  refine SepWP.weaken_pre (Entails.of_eq ?_)
    (SepWP.mono
      (ct1Received_post_call_56d78 (A := A) hmemcpy s0 sf_c outA outSt sp1
        (P_rest ∗ memRegion selfA chunkedStatesSize ∗
         ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
         ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
         A.pool)
        hpc_c hrun_c hsp_c hsp_align hx19_c htr_c)
      (fun sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        hdone sf Pf hpc_f hrun_f
          ⟨Entails.trans hPf (Entails.of_eq (by dsimp only [messageAt]; sep_ac_rfl_recv_ext)),
            hsp_sf, hcs_sf, htr_sf⟩))
  rw [← hmsg_eq]; simp only [arm64_norm]; sep_ac_rfl_recv_ext

set_option autoImplicit false in
private theorem ct1Received_arm_eq_ct2_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hAx : AllocContractsX img A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1ReceivedRecvCt2ChunkName)
      ((growToCalleeExt ct1ReceivedRecvCt2ChunkStack
        (ct1ReceivedRecvCt2ChunkSpec A F)).inImage img))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (P_rest R : SepProp) {Q_post Q_panic : State → SepProp → Prop}
    (hinv_img : ImgCallInv img s)
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ct2 chunk)
    (hrecv : st.recv_ct2_chunk st.uc.epoch chunk = .ok outSt)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 1204#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0)
    (hdone : ∀ (sf : State) (Pf : SepProp), sf.pc = s0.readReg64 Reg.lr → sf.status = .Running →
      (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekSentCt1Received outSt }) ∗
        memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        A.pool ∗ stackAt s0.sp statesRecvStackXExt) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace → Q_post sf Pf)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) →
      Q_panic sf P_f) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      Q_post Q_panic := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  apply SepWPp.of_sepWP_frozen hinv_img.1 hinv_img.2
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr ct1ReceivedRecvCt2ChunkName)
  refine ct1Received_arm_eq_ct2_step_to_call hb s0 s outA selfA msgA st msg chunk P_rest
    heq hpay hpc hrun hsp hsp_align hx1 hx19 hx24 htr ?_
  intro sm sp1 hpc_m hrun_m hsp_m hlr_m htr_m hx19_m hx0_m hx1_m hx2_m hx3_m hF_call hsym_call
  refine call_ct1ReceivedRecvCt2Chunk_ext hcall
    ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1856#64) (msgA + 10#64)
    st chunk outSt hrecv
    (s0 := s0) (sp_call := s0.sp - 4240#64)
    (ret_pc := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 6436#64) (R := R)
    (Frame := P_rest ∗ memRegion selfA chunkedStatesSize ∗
      ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
        memRegion (msgA + 44#64) 4) ∗
      ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      memRegion outA v1RecvSize ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
      statesRecvSavedCells s0)
    ⟨hF_call, hsym_call⟩ hpc_m hrun_m hsp_m hfsp_align hlr_m htr_m hx0_m hx1_m hx2_m hx3_m
    (by
      dsimp only [chunkedEkSentCt1ReceivedSize, BitVec.ofNat_eq_ofNat]
      simp only [arm64_norm])
    hpanic ?_
  intro sf_c hpc_c hrun_c hsp_c hcs_c htr_c hinv_c
  refine SepWP.focus_weaken
    (Entails.of_eq (memRegion_880_split_504_376
      ((s0.sp - 4240#64) + 1856#64) ((s0.sp - 4240#64) + 2360#64) (by bv_omega)).symm)
    (by sep_focus) ?_
  have hmsg_eq :
      ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
       chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) =
      ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) := by
    rw [hpay, messagePayloadAt_ct2 msgA chunk]
  have hx19_c : sf_c.readReg64 .x19 = outA := by
    dsimp only [Reg.x19] at hx19_m ⊢; exact hcs_c.1.trans hx19_m
  refine SepWP.weaken_pre (Entails.of_eq ?_)
    (SepWP.mono
      (ct1Received_post_call_ext hAx s0 sf_c outA outSt sp1
        (P_rest ∗ memRegion selfA chunkedStatesSize ∗
         ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
         ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
         A.pool)
        hinv_c hpc_c hrun_c hsp_c hsp_align hx19_c htr_c)
      (fun sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        hdone sf Pf hpc_f hrun_f
          ⟨Entails.trans hPf (Entails.of_eq (by dsimp only [messageAt]; sep_ac_rfl_recv_ext)),
            hsp_sf, hcs_sf, htr_sf⟩))
  rw [← hmsg_eq]; simp only [arm64_norm]; sep_ac_rfl_recv_ext

/-- Complete `.ct1Received` arm of `<States>::recv` (`+1204 -> s0.x30`, `0x55908 -> 0x59ff0`):
    handles all `msg` cases (`msg.epoch > st.uc.epoch`, `msg.epoch < st.uc.epoch`,
    `msg.epoch = st.uc.epoch` with `msg.payload ≠ .ct2 _`, and `msg.epoch = st.uc.epoch` with
    `msg.payload = .ct2 chunk`). -/
theorem states_recv_arm_ct1Received
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ct1ReceivedRecvCt2ChunkName)
      (ct1ReceivedRecvCt2ChunkSpec A F))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1204#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        statesRecvRoAt b ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantSpec A F K b (.ct1Received st) msg).post (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantSpec A F K b (.ct1Received st) msg).onPanic (outA, selfA, msgA) s0 sf ∗ R)) := by
  by_cases hgt : msg.epoch > st.uc.epoch
  · refine sepWPp_of_statesRecv_exit s0 s outA selfA msgA (.ct1Received st) msg _ R ?_
    rw [states_recv_ct1Received_gt K st msg hgt]
    rw [show memRegion outA v1RecvSize ∗
          chunkedStatesAt A selfA (.ct1Received st) ∗
          messageAt spqrPolyApi msgA msg ∗
          statesRecvRoAt b ∗
          A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 =
        statesRecvRoAt b ∗
          memRegion outA v1RecvSize ∗
          chunkedStatesAt A selfA (.ct1Received st) ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (ct1Received_arm_gt hdealloc s0 s outA selfA msgA st msg (statesRecvRoAt b)
        hgt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · refine sepWPp_of_statesRecv_exit s0 s outA selfA msgA (.ct1Received st) msg _ R ?_
      rw [states_recv_ct1Received_lt K st msg hlt]
      rw [show memRegion outA v1RecvSize ∗
            chunkedStatesAt A selfA (.ct1Received st) ∗
            messageAt spqrPolyApi msgA msg ∗
            statesRecvRoAt b ∗
            A.pool ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗
            statesRecvSavedCells s0 =
          statesRecvRoAt b ∗
            memRegion outA v1RecvSize ∗
            chunkedStatesAt A selfA (.ct1Received st) ∗
            messageAt spqrPolyApi msgA msg ∗
            A.pool ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗
            statesRecvSavedCells s0 by ac_rfl]
      refine SepWP.mono
        (ct1Received_arm_lt hmemcpy s0 s outA selfA msgA st msg (statesRecvRoAt b)
          hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
        (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)
    · have heq : msg.epoch = st.uc.epoch := by
        have h1 : ¬ (st.uc.epoch < msg.epoch) := hgt
        have h2 : ¬ (msg.epoch < st.uc.epoch) := hlt
        exact BitVec.le_antisymm (BitVec.not_lt.mp h1) (BitVec.not_lt.mp h2)
      cases hpay : msg.payload with
      | ct2 chunk =>
        obtain ⟨outSt, hrecv, _⟩ := ct1Received_recv_ct2_chunk_eq_ok st chunk
        dsimp only [statesRecvRoAt, unchunkedSendCt2RoAt]
        rw [show memRegion outA v1RecvSize ∗
              chunkedStatesAt A selfA (.ct1Received st) ∗
              messageAt spqrPolyApi msgA msg ∗
              (statesRecvJumpTableAt b ∗
                (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel)) ∗
                tokenInitAt b ∗ reduceTableAt b) ∗
              A.pool ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗
              statesRecvSavedCells s0 =
            (statesRecvJumpTableAt b ∗
              ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
              tokenInitAt b ∗ reduceTableAt b) ∗
              memRegion outA v1RecvSize ∗
              chunkedStatesAt A selfA (.ct1Received st) ∗
              messageAt spqrPolyApi msgA msg ∗
              ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
              A.pool ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗
              statesRecvSavedCells s0 by ac_rfl]
        refine SepWPp.of_sepWP
          (ct1Received_arm_eq_ct2 hb hcall hmemcpy s0 s outA selfA msgA st msg chunk outSt
            (statesRecvJumpTableAt b ∗
              ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
              tokenInitAt b ∗ reduceTableAt b) R
            heq hpay hrecv hpc hrun hsp hsp_align hx1 hx19 hx24 htr
            (fun sf Pf _ _ ⟨hPf, hspf, hcs, htrf⟩ => ?_)
            (fun sf Pf hpan hmem_f => ?_))
        · refine ⟨fun hmem_f => ?_, hspf, hcs⟩
          dsimp only [statesRecvVariantSpec]
          rw [states_recv_ct1Received_eq_ct2 K st msg chunk outSt heq hpay hrecv,
              sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨htrf, Satisfies.mono (sepConj_mono_left ?_) hmem_f⟩
          refine Entails.trans hPf (Entails.of_eq ?_)
          dsimp only [statesRecvRoAt, unchunkedSendCt2RoAt]
          ac_rfl
        · have hpan' := hpan hmem_f
          dsimp only [statesRecvVariantSpec, statesRecvOnPanic]
          rw [sepConj_assoc, satisfies_pure_sepConj] at hpan' ⊢
          exact ⟨⟨Or.inr hpan'.1.1, hpan'.1.2⟩, hpan'.2⟩
      | none | hdr _ | ek _ | ekCt1Ack _ | ct1Ack _ | ct1 _ =>
        have hct2 : ∀ c, msg.payload ≠ .ct2 c := by intro c hc; rw [hpay] at hc; cases hc
        refine sepWPp_of_statesRecv_exit s0 s outA selfA msgA (.ct1Received st) msg _ R ?_
        rw [states_recv_ct1Received_eq_other K st msg heq hct2]
        rw [show memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Received st) ∗
              messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 =
            statesRecvRoAt b ∗ memRegion outA v1RecvSize ∗
              chunkedStatesAt A selfA (.ct1Received st) ∗ messageAt spqrPolyApi msgA msg ∗
              A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 by ac_rfl]
        refine SepWP.mono
          (ct1Received_arm_eq_other hmemcpy s0 s outA selfA msgA st msg (statesRecvRoAt b)
            heq hct2 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
          (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

set_option autoImplicit false in
private theorem states_recv_arm_ct1Received_inImage_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64) (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1ReceivedRecvCt2ChunkName)
      ((growToCalleeExt ct1ReceivedRecvCt2ChunkStack
        (ct1ReceivedRecvCt2ChunkSpec A F)).inImage img))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (R : SepProp) (himg_s : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 1204#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantSpecExt A F K img.base (.ct1Received st) msg).post
            (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantSpecExt A F K img.base (.ct1Received st) msg).onPanic
            (outA, selfA, msgA) s0 sf ∗ R)) := by
  have hpre_ro_front :
      memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 =
      statesRecvRoAt img.base ∗ memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.ct1Received st) ∗ messageAt spqrPolyApi msgA msg ∗
        A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 := by
    sep_ac_rfl_recv_ext
  by_cases hgt : msg.epoch > st.uc.epoch
  · refine sepWPp_of_statesRecv_exit_ext s0 s outA selfA msgA (.ct1Received st) msg _ R ?_
    rw [states_recv_ct1Received_gt K st msg hgt]
    rw [show memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Received st) ∗
          messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
          memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 =
        (statesRecvRoAt img.base ∗ memRegion (s0.sp - 40176#64) 16384) ∗
          memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Received st) ∗
          messageAt spqrPolyApi msgA msg ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 by
      rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]; sep_ac_rfl_recv_ext]
    refine SepWP.mono
      (ct1Received_arm_gt hdealloc s0 s outA selfA msgA st msg
        (statesRecvRoAt img.base ∗ memRegion (s0.sp - 40176#64) 16384)
        hgt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨Entails.trans hPf
          (Entails.of_eq (by rw [stackAt_statesRecvStackXExt_eq_X s0.sp]; sep_ac_rfl_recv_ext)),
         hsp_sf, hcs_sf, htr_sf⟩)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · refine sepWPp_of_statesRecv_exit_ext s0 s outA selfA msgA (.ct1Received st) msg _ R ?_
      rw [states_recv_ct1Received_lt K st msg hlt, hpre_ro_front]
      refine SepWP.mono
        (ct1Received_arm_lt_ext hAx s0 s outA selfA msgA st msg (statesRecvRoAt img.base)
          himg_s hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
        (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl_recv_ext)), hsp_sf, hcs_sf, htr_sf⟩)
    · have heq : msg.epoch = st.uc.epoch :=
        BitVec.le_antisymm (BitVec.not_lt.mp hgt) (BitVec.not_lt.mp hlt)
      cases hpay : msg.payload with
      | ct2 chunk =>
        obtain ⟨outSt, hrecv, _⟩ := ct1Received_recv_ct2_chunk_eq_ok st chunk
        dsimp only [statesRecvRoAt, unchunkedSendCt2RoAt]
        rw [show memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Received st) ∗
              messageAt spqrPolyApi msgA msg ∗
              (statesRecvJumpTableAt img.base ∗
                (((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
                  ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel)) ∗
                tokenInitAt img.base ∗ reduceTableAt img.base) ∗
              A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 =
            (statesRecvJumpTableAt img.base ∗
              ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
              tokenInitAt img.base ∗ reduceTableAt img.base) ∗
              memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Received st) ∗
              messageAt spqrPolyApi msgA msg ∗
              ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
              A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 by sep_ac_rfl_recv_ext]
        refine ct1Received_arm_eq_ct2_ext hb hAx hcall s0 s outA selfA msgA st msg chunk outSt
          (statesRecvJumpTableAt img.base ∗
            ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
            tokenInitAt img.base ∗ reduceTableAt img.base) R
          himg_s heq hpay hrecv hpc hrun hsp hsp_align hx1 hx19 hx24 htr
          (fun sf Pf _ _ ⟨hPf, hspf, hcs, htrf⟩ => ?_)
          (fun sf Pf hpan hmem_f => ?_)
        · refine ⟨fun hmem_f => ?_, hspf, hcs⟩
          dsimp only [statesRecvVariantSpecExt]
          rw [states_recv_ct1Received_eq_ct2 K st msg chunk outSt heq hpay hrecv,
              sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨htrf, Satisfies.mono (sepConj_mono_left ?_) hmem_f⟩
          refine Entails.trans hPf (Entails.of_eq ?_)
          dsimp only [statesRecvRoAt, unchunkedSendCt2RoAt]
          sep_ac_rfl_recv_ext
        · have hpan' := hpan hmem_f
          dsimp only [statesRecvVariantSpecExt, statesRecvOnPanic]
          rw [sepConj_assoc, satisfies_pure_sepConj] at hpan' ⊢
          exact ⟨⟨Or.inr hpan'.1.1, hpan'.1.2⟩, hpan'.2⟩
      | none | hdr _ | ek _ | ekCt1Ack _ | ct1Ack _ | ct1 _ =>
        have hct2 : ∀ c, msg.payload ≠ .ct2 c := by intro c hc; rw [hpay] at hc; cases hc
        refine sepWPp_of_statesRecv_exit_ext s0 s outA selfA msgA (.ct1Received st) msg _ R ?_
        rw [states_recv_ct1Received_eq_other K st msg heq hct2, hpre_ro_front]
        refine SepWP.mono
          (ct1Received_arm_eq_other_ext hAx s0 s outA selfA msgA st msg (statesRecvRoAt img.base)
            himg_s heq hct2 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
          (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl_recv_ext)), hsp_sf, hcs_sf, htr_sf⟩)

set_option autoImplicit false in
/-- Per-variant `.inImage img` specification proof for `States.ct1Received st`
    (`tag = 5#64`, arm entry `+1204`, `40176` B stack) under `AllocContractsX` + `DeallocOkExt`. -/
theorem states_recv_ct1Received_ok_x_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext) (hdealloc : DeallocOkExt img.base A ext)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1ReceivedRecvCt2ChunkName)
      ((growToCalleeExt ct1ReceivedRecvCt2ChunkStack
        (ct1ReceivedRecvCt2ChunkSpec A F)).inImage img))
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpecExt A F K img.base (.ct1Received st) msg).inImage img) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [Spec.inImage, statesRecvVariantSpecExt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg0, ⟨hb, hx0, hx1, hx2, _hinv⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackXExt ∗ (memRegion outA v1RecvSize ∗
      chunkedStatesAt A selfA (.ct1Received st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl_recv_ext)) hmem, ?_⟩
  have hpro := states_recv_prologue_ext (b := img.base) (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct1Received st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool) hsp0_align hpc0 hrun0
  refine sepWPp_seq_clean_inImage_ax himg0 hpro ?_
  intro s1 hpc1 hrun1 himg1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, _, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  dsimp only [chunkedStatesAt]
  have hdisp := states_recv_dispatch (b := img.base) (ext := ext) hb s1 (s0.sp - 4240#64) selfA 5#64
    (chunkedCt1ReceivedAt A (selfA + 8#64) st ∗ memRegion (selfA + 512#64) 416 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗ memRegion (s0.sp - 4240#64) 4144 ∗
     statesRecvSavedCells s0)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) hpc1 hrun1 hsp1 hx1_1
  dsimp only [statesRecvArmOffset] at hdisp
  refine sepWPp_seq_clean_inImage_ax himg1
    (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl_recv_ext)) hdisp) ?_
  intro s2 hpc2 hrun2 himg2 ⟨hsp2, _, hx1_2, _, _, _, _, hx19_2, _, hx24_2, _, _, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [chunkedStatesAt]; sep_ac_rfl_recv_ext))
    (states_recv_arm_ct1Received_inImage_ext hb hAx hdealloc hcall s0 s2 outA selfA msgA st msg R
      himg2 hpc2 hrun2 hsp2 hsp0_align hx1_2 hx19_2 hx24_2 (htr2.trans htr1))

set_option autoImplicit false in
theorem states_recv_ct1Received_ok_x_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext) (hdealloc : DeallocOkExt img.base A ext)
    (hC : StatesRecvContractsAx img A F K ext)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpecExt A F K img.base (.ct1Received st) msg).inImage img) :=
  states_recv_ct1Received_ok_x_ext hAx hdealloc hC.ct1ReceivedRecvCt2Chunk_ok st msg

end CryptoVerification.SpqrV1.States.Recv
