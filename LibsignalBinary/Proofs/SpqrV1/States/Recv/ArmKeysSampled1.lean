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
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<States>::recv` — `.keysSampled` Arm, Part 1

**Checked by Lean.** Post-call writeback helpers, the `msg.epoch > st.uc.epoch` and
`msg.epoch < st.uc.epoch` branches of `.keysSampled` (`0x55b58`, `+1796`), and their
`AllocContractsX` corollaries.
-/

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
  sp_sub_96_add_8_recv sp_sub_80_add_8_recv sp_sub_64_add_8_recv sp_sub_48_add_8_recv
  sp_sub_32_add_8_recv sp_sub_16_add_8_recv sp_sub_96_add_96_recv
  sp_sub_4240_add_4144_hs bv376_toNat_hs

/-! ## 1. `.keysSampled` (`0x55b58`, `+1796`): Helpers & `msg.epoch > st.uc.epoch` -/

theorem words63_keysSampled_entails_ct1ReceivedAt (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) (w : Words63) :
    words63At a w ∗
      relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w)) ⊢
      chunkedCt1ReceivedAt A a (chunkedKeysSampledToCt1Received st) := by
  rw [← chunkedKeysSampledAt_eq_ct1ReceivedAt]
  exact recompose63 a w

theorem fnAddr_fwd_keysSampledRecvCt1 {b : BitVec 64} {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr keysSampledRecvCt1ChunkName =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr statesRecvName + 49940#64 := by
  dsimp only [tripleRatchetProgAtExt, statesRecvName, keysSampledRecvCt1ChunkName]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      CryptoVerification.libsignalSessionCode_fnOff_0x5005c,
      CryptoVerification.libsignalSessionCode_fnOff_0x5c370]
  bv_omega

theorem fnAddr_adrp_57010 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr statesRecvName + 7100#64) &&&
      0xfffffffffffff000#64) = b + 0x51000#64 := by
  rw [Program.fnAddr_rebase, statesRecv_fnOff]
  revert hb; bv_bits

theorem stackAt_statesRecvCallee_split_keysSampledRecvCt1 (sp : BitVec 64) :
    stackAt sp statesRecvCalleeStackX =
      memRegion (sp - BitVec.ofNat 64 statesRecvCalleeStackX)
        (statesRecvCalleeStackX - keysSampledRecvCt1ChunkStack) ∗
      stackAt sp keysSampledRecvCt1ChunkStack := by
  have hdiff : BitVec.ofNat 64 statesRecvCalleeStackX -
      BitVec.ofNat 64 (statesRecvCalleeStackX - keysSampledRecvCt1ChunkStack) =
      BitVec.ofNat 64 keysSampledRecvCt1ChunkStack := rfl
  simp only [stackAt]
  exact ProofLib.memRegion_split'
    (b := sp - BitVec.ofNat 64 statesRecvCalleeStackX)
    (n := statesRecvCalleeStackX - keysSampledRecvCt1ChunkStack) (k := keysSampledRecvCt1ChunkStack)
    (b' := sp - BitVec.ofNat 64 keysSampledRecvCt1ChunkStack) rfl
    (by rw [← hdiff]; bv_omega)
    (by decide)

set_option maxHeartbeats 1200000 in
/-- Generalised post-call writeback block (`+7748 -> s0.x30`) after `<KeysSampled>::recv_ct1_chunk`
    returns `outSt` at `fsp + 1856#64`, parameterized over caller stack budgets and frame invariant. -/
theorem keysSampled_post_call_57298_gen {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) {stk_callee stk_ret : Nat} {Inv : State → Prop}
    (hseq_inv : ∀ {mid_pc : BitVec 64} {s_a : State} {P_a : SepProp}
      {post_a : State → SepProp → Prop},
      Inv s_a →
      SepWP (tripleRatchetProgAtExt b ext) mid_pc s_a P_a
        (fun sm Pm => Inv sm →
          SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm Pm post_a) →
      SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s_a P_a post_a)
    (hcall_memcpy : ∀ (tailBytes : List (BitVec 8))
      (_hrel : Relocatable 376 (fun a => a ↦ₛ tailBytes))
      (dst src sp_call : BitVec 64) {sm : State} {P Frame : SepProp}
      {post_m : State → SepProp → Prop},
      Inv sm →
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy") →
      sm.status = .Running →
      sm.sp = sp_call →
      (sp_call &&& 15#64 == 0#64) = true →
      sm.readReg64 Reg.lr = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 8156#64 →
      TraceCalleeSaved sm s0 →
      sm.readReg64 Reg.x0 = dst →
      sm.readReg64 Reg.x1 = src →
      (sm.readReg64 Reg.x2).toNat = 376 →
      P = (memRegion dst 376 ∗ (src ↦ₛ tailBytes) ∗ stackAt sp_call stk_callee) ∗ Frame →
      (∀ sf1 : State,
        sf1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 8156#64 →
        sf1.status = .Running →
        sf1.sp = sp_call →
        CalleeSavedPreserved sm sf1 →
        TraceCalleeSaved sf1 s0 →
        Inv sf1 →
        SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf1
          (((dst ↦ₛ tailBytes) ∗ memRegion src 376 ∗ stackAt sp_call stk_callee) ∗ Frame) post_m) →
      SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm P post_m)
    (hwb_gen : ∀ (tailBytes : List (BitVec 8)),
      Relocatable 376 (fun a => a ↦ₛ tailBytes) →
      ∀ (sm : State) (outA : BitVec 64) (sp_wb : SendEkSpills) (P_wb : SepProp),
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
          stackAt (s0.sp - 4240#64) stk_callee ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp_wb ∗
          (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0)
        (fun sf Pf =>
          (Pf ⊢
            P_wb ∗
            (outA ↦₆₄ sp_wb.b2.w7) ∗
            words63At (outA + 8#64) (writebackWords63 sm sp_wb) ∗
            ((outA + 512#64) ↦ₛ tailBytes) ∗
            memRegion (outA + 888#64) 40 ∗
            ((outA + 928#64) ↦₆₄ sp_wb.b2.w8) ∗
            ((outA + 936#64) ↦₆₄ sm.readReg64 .x20) ∗
            ((outA + 944#64) ↦₁₂₈ sp_wb.q200) ∗
            stackAt s0.sp stk_ret) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace))
    (outA : BitVec 64)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hinv : Inv s)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 7748#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (hx20 : s.readReg64 .x20 = (s0.sp - 4240#64) + 1856#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) stk_callee ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        chunkedHeaderSentAt A ((s0.sp - 4240#64) + 1856#64) outSt ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerSent outSt }) ∗
          stackAt s0.sp stk_ret) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  apply hseq_inv
    (mid_pc := (tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
      bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")) hinv
  states_recv_fetches_range b (Rust.withPanics ext) 7748 464
  states_recv_fetches_range b (Rust.withPanics ext) 8316 56
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat]
    at hpc hseq_inv hcall_memcpy hwb_gen ⊢
  refine SepWP.fold (chunkedHeaderSentAt_extract63_376 A ((s0.sp - 4240#64) + 1856#64) outSt)
    (by sep_focus) ?_
  wp_pull_exists; rename_i w_out tailBytes
  refine SepWP.pure_elim fun ⟨hw62, htail_len⟩ => ?_
  have hrel_tail := Relocatable.of_pointsToBytes tailBytes htail_len
  have hwb := hwb_gen tailBytes hrel_tail
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  have h2360 : (s0.sp - 4240#64) + 1856#64 + 504#64 = (s0.sp - 4240#64) + 2360#64 := by bv_omega
  rw [h2360]
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align hx20 ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 200
  refine SepWP.done rfl (by exact hrun) fun hinv_call => ?_
  refine hcall_memcpy tailBytes hrel_tail (sp0 - 3664#64) (sp0 - 1880#64) (sp0 - 4240#64)
    hinv_call rfl (by exact hrun) (by exact hsp) hfsp_align rfl (by exact htr) rfl
    (by simp only [Reg.x1, arm64_norm, hx20])
    rfl (by sep_focus) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1 hinv1
  have hx19_1 : sf1.readReg64 .x19 = outA :=
    hcs1.1.trans (by simp only [Reg.x19, arm64_norm, hx19])
  have hx20_1 : sf1.readReg64 .x20 = sp0 - 2384#64 :=
    hcs1.2.1.trans (by simp only [Reg.x20, arm64_norm, hx20])
  have hx21_1 : sf1.readReg64 .x21 = w_out.b1.w5 := hcs1.2.2.1
  have hx22_1 : sf1.readReg64 .x22 = w_out.b5.w2 := hcs1.2.2.2.1
  have hx23_1 : sf1.readReg64 .x23 = w_out.b2.w9 := hcs1.2.2.2.2.1
  have hx24_1 : sf1.readReg64 .x24 = w_out.b4.w1 := hcs1.2.2.2.2.2.1
  have hx25_1 : sf1.readReg64 .x25 = w_out.b3.w2 := hcs1.2.2.2.2.2.2.1
  have hx26_1 : sf1.readReg64 .x26 = w_out.b1.w6 := hcs1.2.2.2.2.2.2.2.1
  have hx27_1 : sf1.readReg64 .x27 = w_out.b5.w0 := hcs1.2.2.2.2.2.2.2.2.1
  have hx28_1 : sf1.readReg64 .x28 = w_out.b1.w8 := hcs1.2.2.2.2.2.2.2.2.2.1
  apply hseq_inv (mid_pc := entry + 18996#64) hinv1
  wp_steps
  refine SepWP.done rfl (by exact hrun1) fun hinv2 => ?_
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, w_out.b3.w5, w_out.b3.w1, sp.b0.w3, sp.b0.w4, sp.b0.w5, w_out.b4.w0,
             w_out.b3.w8, w_out.b3.w4, w_out.b3.w3⟩
      b1 := ⟨w_out.b5.w7, w_out.b5.w5, w_out.b3.w9, w_out.b3.w6, w_out.b5.w3, w_out.b3.w7,
             w_out.b0.w0, outSt.uc.epoch, sp.b1.w8, sp.b1.w9⟩
      b2 := ⟨w_out.b4.w7, w_out.b5.w1, w_out.b4.w9, w_out.b4.w3, w_out.b4.w5, w_out.b0.w1,
             w_out.b4.w8, 4#64, noneCap, w_out.b4.w2⟩
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
  have h1880 : s0.sp - 1880#64 = (s0.sp - 4240#64) + 2360#64 := by bv_omega
  have h3664 : s0.sp - 3664#64 = (s0.sp - 4240#64) + 576#64 := by bv_omega
  rw [h1880, h3664]
  have hfold_sp1 :
      (words63At ((s0.sp - 4240#64) + 1856#64) w_out ∗
       memRegion ((s0.sp - 4240#64) + 2360#64) 376) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono_left (words63At_376_entails_memRegion_880
      ((s0.sp - 4240#64) + 1856#64) ((s0.sp - 4240#64) + 2360#64) w_out (by bv_omega))
  refine SepWP.fold
    (F := P_rest ∗
      relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes) ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) stk_callee ∗
      (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
      memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗
      statesRecvSavedCells s0)
    hfold_sp1 ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [show (memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes) ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) stk_callee ∗
          (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0) =
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes)) ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) stk_callee ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗ relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes))
        hinv2 rfl hrun1 hsp1 hsp_align (by simp only [Reg.x19, arm64_norm, hx19_1]) htr1)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_headerSent_entails_resultV1RecvAt A (F := F) outA outSt w_out tailBytes
      w_out.b5.w9 sp.q200
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_left hrec))
    dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
      Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
      Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      Reg.x30]
    simp only [arm64_norm, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, ← hw62]
    ac_rfl

/-- Post-call writeback block `0x57298..0x57464 -> 0x574d0..0x57504 -> 0x59e88..0x59ff0`
    (`+7748 -> s0.x30`) after `<KeysSampled>::recv_ct1_chunk` returns `outSt` at `fsp + 1856#64`. -/
theorem keysSampled_post_call_57298 {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 7748#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (hx20 : s.readReg64 .x20 = (s0.sp - 4240#64) + 1856#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        chunkedHeaderSentAt A ((s0.sp - 4240#64) + 1856#64) outSt ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerSent outSt }) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      sessionMemcpyRegionSpec := Leaves.sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      (b := b) (X := Rust.withPanics ext)
      statesRecv_fnOff (ls_stub% "memcpy") (by decide)).symm hmemcpy
  exact keysSampled_post_call_57298_gen s0 s
    (stk_callee := statesRecvCalleeStackX) (stk_ret := statesRecvStackX) (Inv := fun _ => True)
    (fun _ h => SepWP.seq h (fun _ _ _ _ hw => hw trivial))
    (fun tailBytes hrel dst src sp_call {_sm} {_P} {Frame} {_post_m}
        _ hpc' hrun' hsp' halign' hlr' htr' hx0' hx1' hx2' hsplit hnext =>
      call_memcpy_relocate_cs hmemcpy_raw hrel dst src hpc' hrun' hsp' halign' hlr' htr'
        hx0' hx1' hx2' (hsplit.trans (by ac_rfl))
        (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 =>
          (show (((dst ↦ₛ tailBytes) ∗ memRegion src 376) ∗
                  (stackAt sp_call statesRecvCalleeStackX ∗ Frame)) =
                (((dst ↦ₛ tailBytes) ∗ memRegion src 376 ∗
                  stackAt sp_call statesRecvCalleeStackX) ∗ Frame) by ac_rfl) ▸
            hnext sf1 hpc1 hrun1 hsp1 hcs1 htr1 trivial))
    (fun tailBytes hrel sm outA' sp_wb P_wb _ =>
      @states_recv_writeback_59e88 b ext hmemcpy (F_tail := fun a => a ↦ₛ tailBytes)
        hrel s0 sm outA' sp_wb P_wb)
    outA outSt sp P_rest trivial hpc hrun hsp hsp_align hx19 hx20 htr

/-- `.keysSampled` arm when `msg.epoch > st.uc.epoch` (`+1796 -> s0.x30`, `0x55b58..0x55ca4 -> 0x59fd0..0x59ff0`). -/
theorem keysSampled_arm_gt
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hgt : msg.epoch > st.uc.epoch)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1796#64)
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
        chunkedStatesAt A selfA (.keysSampled st) ∗
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
  have hdrop_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18446744073709515880#64)
      (dropChunkedCt1ReceivedSpec A F) := Leaves.sub_ok_of_addr_eq
    (fnAddr_bwd_eq_recv (d := 35736) (k := 18446744073709515880) (b := b) (X := Rust.withPanics ext)
      statesRecv_fnOff libsignalSessionCode_fnOff_0x474c4 (by decide) rfl).symm
    (drop_chunked_ct1_received_ok_ext hdealloc)
  have hepilogue := @states_recv_epilogue_59fd0 b ext s0
  states_recv_fetches_range b (Rust.withPanics ext) 1796 336
  dsimp only [tripleRatchetProgAtExt, statesRecvName, dropChunkedCt1ReceivedSpec,
    chunkedCt1ReceivedSize, chunkedStatesAt, messageAt, BitVec.ofNat_eq_ofNat] at hpc hdrop_raw hepilogue ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  rw [memRegion_out_960_split_err outA]
  wp_pull_exists; rename_i v0 b8 v16
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (sendEkUnusedAt_split_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i u_ac0
  refine SepWP.fold (chunkedKeysSampledAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw62 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    rw [hw62]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 200
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, sp.b0.w3, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7,
             sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, sp.b1.w3, w.b5.w3, sp.b1.w5, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, sp.b2.w3, w.b4.w5, w.b0.w1, w.b4.w8, sp.b2.w7,
             sp.b2.w8, w.b4.w2⟩
      b3 := ⟨w.b5.w8, w.w62, sp.b3.w2, sp.b3.w3, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
             w.b3.w0, w.b2.w8⟩
      b4 := ⟨w.b2.w6, sp.b4.w1, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, sp.b4.w6, w.b1.w1,
             w.b2.w0, w.b2.w3⟩
      b5 := ⟨w.b0.w9, sp.b5.w1, w.b1.w4, w.b0.w8, w.b1.w7, sp.b5.w5, sp.b5.w6, w.b2.w4,
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
       relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w))) ∗
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
        chunkedCt1ReceivedAt A (selfA + 8#64) (chunkedKeysSampledToCt1Received st) ∗
        memRegion (s0.sp - 4240#64) 4144 :=
    sepConj_mono (words63_keysSampled_entails_ct1ReceivedAt A (selfA + 8#64) st w)
      (Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hfold_unused))))
        (sendEkFrame_entails_memRegion_4144 (s0.sp - 4240#64) sp1))
  refine SepWP.fold
    (F := P_rest ∗
      ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ memRegion (outA + 9#64) 7 ∗
       ((outA + 16#64) ↦₆₄ msg.epoch) ∗ memRegion (outA + 24#64) 936) ∗
      (selfA ↦₆₄ 3#64) ∗
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
  · have hsplit_sp := stackAt_statesRecvCallee_split_dropStack32 (s0.sp - 4240#64)
    refine SepWP.focus_weaken (Entails.of_eq hsplit_sp) (by sep_focus) ?_
    wp_call hdrop_raw ⟨selfA + 8#64, chunkedKeysSampledToCt1Received st⟩
    wp_conv_pre => rw [hsp]
    refine SepWP.focus_weaken (Entails.of_eq hsplit_sp.symm) (by sep_focus) ?_
    wp_steps
    refine SepWP.fold
      (F := P_rest ∗ ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
        A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (sepConj_mono
        (err_epochOutOfRange_entails_resultV1RecvAt A (F := F) outA msg.epoch)
        (self_504_416_entails_memRegion_928 selfA 3#64))
      (by ac_rfl) ?_
    rw [show (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg.epoch))) ∗
          memRegion selfA chunkedStatesSize) ∗
        (P_rest ∗ ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0) =
        (P_rest ∗ resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg.epoch))) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (hepilogue _
        (P_rest ∗ resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg.epoch))) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool)
        rfl (by assumption) (by exact (by assumption : _ = s.sp).trans hsp)
        hsp_align ⟨(by assumption : _ = s.trace).trans htr.1, (by assumption : _ = calleeSavedVRegs _).trans (by simpa only [arm64_norm] using htr.2)⟩)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

set_option maxHeartbeats 1200000 in
/-- Generalised `.keysSampled` arm when `msg.epoch < st.uc.epoch` (`+1796 -> s0.x30`),
    parameterized over caller stack budgets and frame invariant. -/
theorem keysSampled_arm_lt_gen
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) {stk_callee stk_ret : Nat} {Inv : State → Prop}
    (hseq_inv : ∀ {mid_pc : BitVec 64} {s_a : State} {P_a : SepProp}
      {post_a : State → SepProp → Prop},
      Inv s_a →
      SepWP (tripleRatchetProgAtExt b ext) mid_pc s_a P_a
        (fun sm Pm => Inv sm →
          SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm Pm post_a) →
      SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s_a P_a post_a)
    (hwb_gen : ∀ (sm : State) (outA : BitVec 64) (sp_wb : SendEkSpills) (P_wb : SepProp),
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
          stackAt (s0.sp - 4240#64) stk_callee ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp_wb ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0)
        (fun sf Pf =>
          (Pf ⊢
            P_wb ∗
            (outA ↦₆₄ sp_wb.b2.w7) ∗
            words63At (outA + 8#64) (writebackWords63 sm sp_wb) ∗
            memRegion (outA + 512#64) 376 ∗
            memRegion (outA + 888#64) 40 ∗
            ((outA + 928#64) ↦₆₄ sp_wb.b2.w8) ∗
            ((outA + 936#64) ↦₆₄ sm.readReg64 .x20) ∗
            ((outA + 944#64) ↦₁₂₈ sp_wb.q200) ∗
            stackAt s0.sp stk_ret) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace))
    (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hinv : Inv s)
    (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1796#64)
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
        chunkedStatesAt A selfA (.keysSampled st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) stk_callee ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .keysSampled st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp stk_ret) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hlt_nat : msg.epoch.toNat < st.uc.epoch.toNat := BitVec.lt_def.mp hlt
  have hcond1 := epoch_cmp_ct1r_eq_of_lt hlt_nat
  have hcond2 := epoch_cmp_ct1r_bne_1_of_lt hlt_nat
  apply hseq_inv
    (mid_pc := (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64) hinv
  states_recv_fetches_range b (Rust.withPanics ext) 1796 308
  states_recv_fetches_range b (Rust.withPanics ext) 8212 160
  dsimp only [tripleRatchetProgAtExt, statesRecvName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hwb_gen ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (sendEkUnusedAt_split_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i u_ac0
  refine SepWP.fold (chunkedKeysSampledAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw62 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    rw [hw62]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 256
  refine SepWP.done rfl (by exact hrun) fun hinv1 => ?_
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, sp.b0.w3, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7,
             sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, sp.b1.w3, w.b5.w3, w.b3.w7, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, 3#64,
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
      ((selfA ↦₆₄ 3#64) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416) ∗
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
    sepConj_mono (words63At_self_entails_memRegion_928 selfA 3#64 w)
      (sepConj_mono_left hfold_unused)
  refine SepWP.fold
    (F := P_rest ∗
      relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w)) ∗
      ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
      A.pool ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) stk_callee ∗
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
          relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w)) ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) stk_callee ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          statesRecvSavedCells s0) =
        (P_rest ∗
          relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool) ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) stk_callee ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (hwb_gen _ outA sp1
        (P_rest ∗
          relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool)
        hinv1 rfl hrun hsp hsp_align (by simp only [Reg.x19, arm64_norm, hx19]) htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_keysSampled_entails_resultV1RecvAt A (F := F) outA st w
      w.b5.w9 sp.q200
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_left hrec))
    dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
      Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
      Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      Reg.x30]
    simp only [arm64_norm, hx1]
    ac_rfl

/-- `.keysSampled` arm when `msg.epoch < st.uc.epoch`
    (`+1796 -> s0.x30`, `0x55b58..0x55c88 -> 0x57468..0x57504 -> 0x59e88..0x59ff0`). -/
theorem keysSampled_arm_lt
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1796#64)
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
        chunkedStatesAt A selfA (.keysSampled st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .keysSampled st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) :=
  keysSampled_arm_lt_gen s0 s
    (stk_callee := statesRecvCalleeStackX) (stk_ret := statesRecvStackX) (Inv := fun _ => True)
    (fun _ h => SepWP.seq h (fun _ _ _ _ hw => hw trivial))
    (fun sm outA' sp_wb P_wb _ =>
      @states_recv_writeback_59e88 b ext hmemcpy (F_tail := fun a => memRegion a 376)
        (Relocatable.of_memRegion 376) s0 sm outA' sp_wb P_wb)
    outA selfA msgA st msg P_rest trivial hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr

/-! ## 2. `AllocContractsX` Corollaries (`statesRecvCalleeStackXExt` / `statesRecvStackXExt`) -/

/-- Post-call writeback block (`+7748 -> s0.x30`) after `<KeysSampled>::recv_ct1_chunk` returns
    `outSt` at `fsp + 1856#64`, under `AllocContractsX img A ext` at `statesRecvCalleeStackXExt`. -/
theorem keysSampled_post_call_57298_ext {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 7748#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (hx20 : s.readReg64 .x20 = (s0.sp - 4240#64) + 1856#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        chunkedHeaderSentAt A ((s0.sp - 4240#64) + 1856#64) outSt ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerSent outSt }) ∗
          stackAt s0.sp statesRecvStackXExt) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hmemcpy_raw := session_memcpy_region_ok_at_ext_of_alloc hAx statesRecvName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
  exact keysSampled_post_call_57298_gen s0 s
    (stk_callee := statesRecvCalleeStackXExt) (stk_ret := statesRecvStackXExt)
    (Inv := ImgCallInv img)
    (fun hinv' h => SepWP.seq_inImage hinv' h)
    (fun _tailBytes hrel dst src _sp_call {_sm} {_P} {_Frame} {_post_m}
        hin hpc' hrun' hsp' halign' hlr' htr' hx0' hx1' hx2' hsplit hnext =>
      call_memcpy_relocate_cs_inImage_stk_ext (stk := statesRecvCalleeStackXExt) (k_stk := 19552)
        hmemcpy_raw hrel dst src hin hpc' hrun' hsp' halign' hlr' htr' hx0' hx1' hx2'
        (by decide) (by decide) hsplit hnext)
    (fun tailBytes hrel =>
      @states_recv_writeback_59e88_stk_ext img A ext hAx (F_tail := fun a => a ↦ₛ tailBytes) hrel s0)
    outA outSt sp P_rest hinv hpc hrun hsp hsp_align hx19 hx20 htr

/-- `.keysSampled` arm when `msg.epoch > st.uc.epoch` at `statesRecvCalleeStackXExt` (`35936` B). -/
theorem keysSampled_arm_gt_ext
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hgt : msg.epoch > st.uc.epoch)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1796#64)
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
        chunkedStatesAt A selfA (.keysSampled st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg.epoch))) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackXExt) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hpre :
      P_rest ∗
        memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.keysSampled st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 =
      (P_rest ∗ memRegion (s0.sp - 40176#64) 16384) ∗
        memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.keysSampled st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 := by
    rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]; sep_ac_rfl_recv_ext
  rw [hpre]
  refine SepWP.mono
    (keysSampled_arm_gt hdealloc s0 s outA selfA msgA st msg
      (P_rest ∗ memRegion (s0.sp - 40176#64) 16384)
      hgt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
    (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
      ⟨Entails.trans hPf
        (Entails.of_eq (by rw [stackAt_statesRecvStackXExt_eq_X s0.sp]; sep_ac_rfl_recv_ext)),
       hsp_sf, hcs_sf, htr_sf⟩)

/-- `.keysSampled` arm when `msg.epoch < st.uc.epoch` (`+1796 -> s0.x30`) under
    `AllocContractsX img A ext` at `statesRecvCalleeStackXExt` (`35936` B). -/
theorem keysSampled_arm_lt_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hinv : ImgCallInv img s)
    (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 1796#64)
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
        chunkedStatesAt A selfA (.keysSampled st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .keysSampled st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackXExt) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) :=
  keysSampled_arm_lt_gen s0 s
    (stk_callee := statesRecvCalleeStackXExt) (stk_ret := statesRecvStackXExt)
    (Inv := ImgCallInv img)
    (fun hinv' h => SepWP.seq_inImage hinv' h)
    (@states_recv_writeback_59e88_stk_ext img A ext hAx (F_tail := fun a => memRegion a 376)
      (Relocatable.of_memRegion 376) s0)
    outA selfA msgA st msg P_rest hinv hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr

end CryptoVerification.SpqrV1.States.Recv

