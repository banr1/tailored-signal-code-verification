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
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch4Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonPlaced
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.headerSent` Arm, Part 2 (Relocatable)

**Checked by Lean.** Relocatable `[LibsignalPlacement]` post-call writeback blocks,
`call_headerSentRecvCt1Chunk_placed`, `headerSent_arm_eq_ct1_placed`,
`states_recv_arm_headerSent_placed`, and `states_recv_headerSent_placed_ok_ext` (`+780`,
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
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  bv880_toNat_hs
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem sepWPp_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post onPanic : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog target sm P_mid post onPanic) :
    SepWPp prog target s P post onPanic :=
  SepWPp.of_sepWP (CryptoVerification.sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcl' =>
    SepWP.done hpc hrun (SepWPp.weaken_pre hPm (h2 sm hpc hrun hQ hcl'))))

private theorem sepWPp_seq_clean_lscro [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post onPanic : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog target sm P_mid post onPanic) :
    SepWPp prog target s P post onPanic :=
  SepWPp.of_sepWP (sepWP_seq_lscro hcro (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcro' =>
    SepWP.done hpc hrun (SepWPp.weaken_pre hPm (h2 sm hpc hrun hQ hcro'))))

/-! ## 1. `HookSat`-Parameterized `.headerSent` `<` and `eq_other` Arms -/

set_option maxHeartbeats 1200000 in
/-- Relocatable `.headerSent` arm when `msg.epoch < st.uc.epoch` parameterized by `hmemcpy_sat`. -/
theorem headerSent_arm_lt_sat_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = lsmpl.base 332 + 780#64)
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
  have hmemcpy : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (sessionMemcpySpec 4096) := spqr_hook_ok_of_mem hmemcpy_sat
  have hlt_nat : msg.epoch.toNat < st.uc.epoch.toNat := BitVec.lt_def.mp hlt
  have hcond1 := epoch_cmp_ct1r_eq_of_lt hlt_nat
  have hcond2 := epoch_cmp_ct1r_bne_1_of_lt hlt_nat
  dsimp only [chunkedStatesAt]
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedHeaderSentAt_extract63_376 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w tailBytes
  refine SepWP.pure_elim fun ⟨hw62, htail_len⟩ => ?_
  have hrel_tail := Relocatable.of_pointsToBytes tailBytes htail_len
  have hwb := @states_recv_writeback_59e88_sat _ ext hmemcpy_sat (F_tail := fun a => a ↦ₛ tailBytes)
    hrel_tail s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, lsρ, memcpyName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hmemcpy hwb ⊢
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
  rw [stackAt_statesRecvCallee_eq_allocHook (sp0 - 4240#64)]
  dsimp only [allocHookStack]
  refine call_memcpy_relocate_cs_sat (ret_pc := (blkPl_332).base + 10476#64)
    hmemcpy hrel_tail (sp0 - 3664#64) (selfA + 512#64)
    rfl hrun hsp hfsp_align rfl htr rfl (by simp only [Reg.x1, arm64_norm, hx1]) rfl (by sep_focus) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
  have hx19_1 : sf1.readReg64 .x19 = outA := hcs1.1.trans (by simp only [Reg.x19, arm64_norm, hx19])
  have hx20_1 : sf1.readReg64 .x20 = w.b1.w5 := hcs1.2.1
  have hx22_1 : sf1.readReg64 .x22 = w.b0.w0 := hcs1.2.2.2.1
  have hx25_1 : sf1.readReg64 .x25 = w.b0.w1 := hcs1.2.2.2.2.2.2.1
  have hx28_1 : sf1.readReg64 .x28 = w.b1.w6 := hcs1.2.2.2.2.2.2.2.2.2.1
  refine sepWP_seq_cut ((blkPl_332).base + 18996#64) ?_
  wp_steps
  subst hsp0
  refine SepWP.done rfl hrun1 ?_
  let sp1 : SendEkSpills :=
    { b0 := ⟨w.b5.w2, w.b3.w5, w.b3.w1, w.b2.w9, w.b3.w2, w.b4.w1, w.b4.w0, w.b3.w8, w.b3.w4, w.b3.w3⟩
      b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, w.b3.w6, w.b5.w3, w.b3.w7, sp.b1.w6, w.b5.w9, sp.b1.w8, sp.b1.w9⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, sp.b2.w5, w.b4.w8, 4#64, noneCap, w.b4.w2⟩
      b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5, w.b3.w0, w.b2.w8⟩
      b4 := ⟨w.b2.w6, w.b1.w2, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, w.b0.w4, w.b1.w1, w.b2.w0, w.b2.w3⟩
      b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, w.b5.w0, w.b0.w3, w.b2.w4, w.b4.w6, w.b5.w4⟩
      w60 := w.b5.w6, w61 := w.b0.w2, w62 := w.b0.w6
      q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := w.q60 }
  have hfold_self_sp :
      ((selfA ↦₆₄ 4#64) ∗ words63At (selfA + 8#64) w ∗
       memRegion (selfA + 512#64) 376 ∗ memRegion (selfA + 888#64) 40) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion selfA chunkedStatesSize ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1 := by
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
      ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool ∗
      memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
      statesRecvSavedCells s0)
    hfold_self_sp ?_ ?_
  · rw [stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)]
    dsimp only [allocHookStack, sendEkSpillsAt, words63At, words10At, sp1]
    rw [hw62]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [show (memRegion selfA chunkedStatesSize ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool ∗
          memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0) =
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool) ∗
        memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗ (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool)
        rfl hrun1 hsp1 hsp_align (by simp only [Reg.x19, arm64_norm, hx19_1]) htr1)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_headerSent_entails_resultV1RecvAt A (F := F) outA st w tailBytes w.b5.w9 sp.q200
    refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_right (sepConj_mono_left hrec))
    dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
      Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
      Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x30]
    simp only [arm64_norm, hx20_1, hx22_1, hx25_1, hx28_1, ← hw62]; ac_rfl

set_option maxHeartbeats 1200000 in
/-- Relocatable `.headerSent` arm when `msg.epoch = st.uc.epoch` and `∀ c, msg.payload ≠ .ct1 c`
    parameterized by `hmemcpy_sat`. -/
theorem headerSent_arm_eq_other_sat_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (heq : msg.epoch = st.uc.epoch)
    (hct1 : ∀ c, msg.payload ≠ .ct1 c)
    (hpc : s.pc = lsmpl.base 332 + 780#64)
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
  have hmemcpy : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (sessionMemcpySpec 4096) := spqr_hook_ok_of_mem hmemcpy_sat
  have hcond_eq := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hcond_tag1 := messagePayloadTag_eq_5_of_not_ct1 hct1
  have hcond_tag2 := messagePayloadTag_bne_5_of_not_ct1 hct1
  dsimp only [chunkedStatesAt]
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedHeaderSentAt_extract63_376 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w tailBytes
  refine SepWP.pure_elim fun ⟨hw62, htail_len⟩ => ?_
  have hrel_tail := Relocatable.of_pointsToBytes tailBytes htail_len
  have hwb := @states_recv_writeback_59e88_sat _ ext hmemcpy_sat (F_tail := fun a => a ↦ₛ tailBytes)
    hrel_tail s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, lsρ, memcpyName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hmemcpy hwb ⊢
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
  rw [stackAt_statesRecvCallee_eq_allocHook (sp0 - 4240#64)]
  dsimp only [allocHookStack]
  refine call_memcpy_relocate_cs_sat (ret_pc := (blkPl_332).base + 11296#64)
    hmemcpy hrel_tail (sp0 - 3664#64) (selfA + 512#64)
    rfl hrun hsp hfsp_align rfl htr rfl (by simp only [Reg.x1, arm64_norm, hx1]) rfl (by sep_focus) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
  have hx19_1 : sf1.readReg64 .x19 = outA := hcs1.1.trans (by simp only [Reg.x19, arm64_norm, hx19])
  have hx22_1 : sf1.readReg64 .x22 = w.b1.w5 := hcs1.2.2.2.1
  have hx25_1 : sf1.readReg64 .x25 = w.b0.w1 := hcs1.2.2.2.2.2.2.1
  have hx28_1 : sf1.readReg64 .x28 = w.b1.w6 := hcs1.2.2.2.2.2.2.2.2.2.1
  refine sepWP_seq_cut ((blkPl_332).base + 18996#64) ?_
  wp_steps
  subst hsp0
  refine SepWP.done rfl hrun1 ?_
  let sp1 : SendEkSpills :=
    { b0 := ⟨w.b5.w2, w.b3.w5, w.b3.w1, w.b2.w9, w.b3.w2, w.b4.w1, w.b4.w0, w.b3.w8, w.b3.w4, w.b3.w3⟩
      b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, w.b3.w6, w.b5.w3, w.b3.w7, w.b0.w0, w.b5.w9, sp.b1.w8, sp.b1.w9⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, sp.b2.w5, w.b4.w8, 4#64, noneCap, w.b4.w2⟩
      b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5, w.b3.w0, w.b2.w8⟩
      b4 := ⟨w.b2.w6, w.b1.w2, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, w.b0.w4, w.b1.w1, w.b2.w0, w.b2.w3⟩
      b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, w.b5.w0, w.b0.w3, w.b2.w4, w.b4.w6, w.b5.w4⟩
      w60 := w.b5.w6, w61 := w.b0.w2, w62 := w.b0.w6
      q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := w.q60 }
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
      (msgA ↦₆₄ msg.epoch) ∗ A.pool ∗ memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
      statesRecvSavedCells s0)
    hfold_self_sp ?_ ?_
  · rw [stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)]
    dsimp only [allocHookStack, sendEkSpillsAt, words63At, words10At, sp1]
    rw [hw62, heq]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [show (memRegion selfA chunkedStatesSize ∗
          messagePayloadAt spqrPolyApi msgA msg.payload ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
          (msgA ↦₆₄ msg.epoch) ∗ A.pool ∗ memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0) =
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool) ∗
        memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗ (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool)
        rfl hrun1 hsp1 hsp_align (by simp only [Reg.x19, arm64_norm, hx19_1]) htr1)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_headerSent_entails_resultV1RecvAt A (F := F) outA st w tailBytes w.b5.w9 sp.q200
    refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_right (sepConj_mono_left hrec))
    dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
      Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
      Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x30]
    simp only [arm64_norm, hx22_1, hx25_1, hx28_1, ← hw62]; ac_rfl

/-! ## 2. Relocatable Post-Call Writeback Blocks (`0x56848..0x56ad4` and `0x58cac..0x58ecc`) -/

set_option maxHeartbeats 1200000 in
/-- Relocatable post-call writeback block `0x56848..0x569e8 -> 0x56aa4..0x56ad4 -> 0x58e80..0x58ecc -> 0x59e88..0x59ff0`
    (`+5108 -> s0.x30`, Block `332`) when `<HeaderSent>::recv_ct1_chunk` returns `.done outSt` at `fsp + 976#64`. -/
theorem headerSent_post_call_done_56848_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 5108#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (hx21 : s.readReg64 .x21 = (s0.sp - 4240#64) + 976#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        headerSentRecvChunkAt A ((s0.sp - 4240#64) + 976#64) (.done outSt) ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢
          P_rest ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Received outSt }) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hwb := @states_recv_writeback_59e88_sat _ ext hmemcpy_sat (F_tail := fun a => memRegion a 376)
    (Relocatable.of_memRegion 376) s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, headerSentRecvChunkAt, BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  have h984 : ((s0.sp - 4240#64) + 976#64) + 8#64 = (s0.sp - 4240#64) + 984#64 := by bv_omega
  have h1488 : ((s0.sp - 4240#64) + 976#64) + 512#64 = (s0.sp - 4240#64) + 1488#64 := by bv_omega
  rw [h984, h1488]
  refine SepWP.fold (sendEkUnusedAt_split_f10 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i u_f10
  refine SepWP.fold (chunkedCt1ReceivedAt_extract63 A ((s0.sp - 4240#64) + 984#64) outSt)
    (by sep_focus) ?_
  wp_pull_exists; rename_i w_out
  refine SepWP.pure_elim fun _ => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  refine sepWP_seq_cut ((blkPl_332).base + 18996#64) ?_
  generalize hsp0 : s0.sp = sp0 at hsp hx21 hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At, lsLogFilterAddr]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 200
  subst hsp0
  refine SepWP.done rfl hrun ?_
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, w_out.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7, sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w_out.b5.w7, sp.b1.w1, sp.b1.w2, sp.b1.w3, w_out.b5.w3, w_out.b3.w7, w_out.b0.w0, w_out.b5.w9, w_out.b1.w5, w_out.b1.w6⟩
      b2 := ⟨w_out.b4.w7, w_out.b5.w1, w_out.b4.w9, w_out.b4.w3, sp.b2.w4, sp.b2.w5, w_out.b4.w8, 5#64, noneCap, w_out.b4.w2⟩
      b3 := ⟨w_out.b5.w8, w_out.w62, w_out.b1.w8, w_out.b2.w1, w_out.b2.w7, w_out.b0.w7, w_out.b1.w3, w_out.b2.w5, w_out.b3.w0, w_out.b2.w8⟩
      b4 := ⟨w_out.b2.w6, w_out.b1.w2, w_out.b1.w9, w_out.b1.w0, w_out.b2.w2, w_out.b0.w5, w_out.b0.w4, w_out.b1.w1, w_out.b2.w0, w_out.b2.w3⟩
      b5 := ⟨w_out.b0.w9, w_out.b4.w4, w_out.b1.w4, w_out.b0.w8, w_out.b1.w7, w_out.b5.w0, w_out.b0.w3, w_out.b2.w4, w_out.b4.w6, w_out.b5.w4⟩
      w60 := w_out.b5.w6, w61 := w_out.b0.w2, w62 := w_out.b0.w6
      q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := w_out.q60 }
  have hfold_976 :
      (((s0.sp - 4240#64) + 976#64) ↦₆₄ 2#64) ∗
      words63At ((s0.sp - 4240#64) + 984#64) w_out ∗
      memRegion ((s0.sp - 4240#64) + 1488#64) 368 ⊢
        memRegion ((s0.sp - 4240#64) + 976#64) 880 := by
    have h := done_976_entails_memRegion_880 ((s0.sp - 4240#64) + 976#64) w_out
    rw [h984, h1488] at h; exact h
  have hfold_unused := sendEkUnusedAt_rejoin_f10 (s0.sp - 4240#64) w_out.q60
  have hfold_all :
      ((((s0.sp - 4240#64) + 976#64) ↦₆₄ 2#64) ∗
       words63At ((s0.sp - 4240#64) + 984#64) w_out ∗
       memRegion ((s0.sp - 4240#64) + 1488#64) 368) ∗
      (((s0.sp - 4240#64 + 3856#64) ↦₁₂₈ w_out.q60) ∗
       memRegion (s0.sp - 4240#64) 8 ∗ memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
       memRegion (s0.sp - 4240#64 + 952#64) 8 ∗ memRegion (s0.sp - 4240#64 + 2736#64) 1120 ∗
       memRegion (s0.sp - 4240#64 + 3872#64) 272) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono hfold_976 (sepConj_mono_left hfold_unused)
  refine SepWP.fold
    (F := P_rest ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)) ∗
      memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      statesRecvSavedCells s0)
    hfold_all ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, lsLogFilterAddr, sp1]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [show (memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)) ∗
          memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          statesRecvSavedCells s0) =
        (P_rest ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out))) ∗
        memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)))
        rfl hrun hsp hsp_align (by simp only [Reg.x19, arm64_norm, hx19]) htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_ct1Received_entails_resultV1RecvAt A (F := F) outA outSt w_out
      w_out.b5.w9 sp.q200
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hrec)))
    dsimp only [writebackWords63, words63At, words10At, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4,
      Reg.x5, Reg.x6, Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15,
      Reg.x16, Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x30]
    simp only [arm64_norm]; ac_rfl

set_option maxHeartbeats 1200000 in
/-- Relocatable post-call writeback block `0x56848..0x56850 -> 0x58cac..0x58ecc -> 0x59e88..0x59ff0`
    (`+5108 -> s0.x30`, Block `332`) when `<HeaderSent>::recv_ct1_chunk` returns `.stillReceiving outSt` at `fsp + 976#64`. -/
theorem headerSent_post_call_still_56848_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 5108#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (hx21 : s.readReg64 .x21 = (s0.sp - 4240#64) + 976#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        headerSentRecvChunkAt A ((s0.sp - 4240#64) + 976#64) (.stillReceiving outSt) ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
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
  have hmemcpy : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (sessionMemcpySpec 4096) := spqr_hook_ok_of_mem hmemcpy_sat
  rw [lsmpl_base_332_eq] at hpc
  dsimp only [lsProg_332, lsρ, memcpyName, headerSentRecvChunkAt,
    BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  refine SepWP.fold (chunkedHeaderSentAt_extract63_376_tag A ((s0.sp - 4240#64) + 976#64) outSt)
    (by sep_focus) ?_
  wp_pull_exists; rename_i w_out tailBytes
  refine SepWP.pure_elim fun ⟨hw0, hw62, htail_len⟩ => ?_
  have hrel_tail := Relocatable.of_pointsToBytes tailBytes htail_len
  have hwb := @states_recv_writeback_59e88_sat _ ext hmemcpy_sat (F_tail := fun a => a ↦ₛ tailBytes)
    hrel_tail s0
  rw [lsmpl_base_332_eq] at hwb
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hwb
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  have h1480 : ((s0.sp - 4240#64) + 976#64) + 504#64 = s0.sp - 2760#64 := by bv_omega
  rw [h1480]
  generalize hsp0 : s0.sp = sp0 at hsp hx21 hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 200
  rw [stackAt_statesRecvCallee_eq_allocHook (sp0 - 4240#64)]
  dsimp only [allocHookStack]
  refine call_memcpy_relocate_cs_sat (ret_pc := (blkPl_332).base + 14836#64)
    hmemcpy hrel_tail (sp0 - 3664#64) (sp0 - 2760#64)
    rfl hrun hsp hfsp_align rfl htr rfl (by simp only [Reg.x1, arm64_norm, hx21]) rfl (by sep_focus) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
  have hx19_1 : sf1.readReg64 .x19 = outA := hcs1.1.trans (by simp only [Reg.x19, arm64_norm, hx19])
  have hx20_1 : sf1.readReg64 .x20 = w_out.b5.w5 := hcs1.2.1
  have hx22_1 : sf1.readReg64 .x22 = w_out.b0.w1 := hcs1.2.2.2.1
  have hx23_1 : sf1.readReg64 .x23 = w_out.b1.w8 := hcs1.2.2.2.2.1
  have hx24_1 : sf1.readReg64 .x24 = w_out.b3.w1 := hcs1.2.2.2.2.2.1
  have hx25_1 : sf1.readReg64 .x25 = w_out.b3.w4 := hcs1.2.2.2.2.2.2.1
  have hx26_1 : sf1.readReg64 .x26 = w_out.b3.w2 := hcs1.2.2.2.2.2.2.2.1
  have hx27_1 : sf1.readReg64 .x27 = w_out.b3.w3 := hcs1.2.2.2.2.2.2.2.2.1
  have hx28_1 : sf1.readReg64 .x28 = w_out.b5.w2 := hcs1.2.2.2.2.2.2.2.2.2.1
  refine sepWP_seq_cut ((blkPl_332).base + 18996#64) ?_
  wp_steps
  subst hsp0
  refine SepWP.done rfl hrun1 ?_
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, w_out.b3.w5, sp.b0.w2, w_out.b2.w9, sp.b0.w4, w_out.b4.w1, w_out.b4.w0, w_out.b3.w8, sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w_out.b5.w7, sp.b1.w1, w_out.b3.w9, w_out.b3.w6, w_out.b5.w3, w_out.b3.w7, w_out.b0.w0, w_out.b5.w9, w_out.b1.w5, w_out.b1.w6⟩
      b2 := ⟨w_out.b4.w7, w_out.b5.w1, w_out.b4.w9, w_out.b4.w3, w_out.b4.w5, sp.b2.w5, w_out.b4.w8, 4#64, noneCap, w_out.b4.w2⟩
      b3 := ⟨w_out.b5.w8, w_out.w62, w_out.b1.w8, w_out.b2.w1, w_out.b2.w7, w_out.b0.w7, w_out.b1.w3, w_out.b2.w5, w_out.b3.w0, w_out.b2.w8⟩
      b4 := ⟨w_out.b2.w6, w_out.b1.w2, w_out.b1.w9, w_out.b1.w0, w_out.b2.w2, w_out.b0.w5, w_out.b0.w4, w_out.b1.w1, w_out.b2.w0, w_out.b2.w3⟩
      b5 := ⟨w_out.b0.w9, w_out.b4.w4, w_out.b1.w4, w_out.b0.w8, w_out.b1.w7, w_out.b5.w0, w_out.b0.w3, w_out.b2.w4, w_out.b4.w6, w_out.b5.w4⟩
      w60 := w_out.b5.w6, w61 := w_out.b0.w2, w62 := w_out.b0.w6
      q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := w_out.q60 }
  have h3664 : s0.sp - 3664#64 = (s0.sp - 4240#64) + 576#64 := by bv_omega
  have h2760 : s0.sp - 2760#64 = (s0.sp - 4240#64) + 1480#64 := by bv_omega
  rw [h3664, h2760]
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
      relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes) ∗
      memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
    hfold_sp1 ?_ ?_
  · rw [stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)]
    dsimp only [allocHookStack, sendEkSpillsAt, words63At, words10At, sp1, Reg.x23]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm, hx23_1, hw62]
    ac_rfl
  · rw [show (memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes) ∗
          memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0) =
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes)) ∗
        memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗ (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (hwb _ outA sp1
        (P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes))
        rfl hrun1 hsp1 hsp_align (by simp only [Reg.x19, arm64_norm, hx19_1]) htr1)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ => ⟨?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_headerSent_entails_resultV1RecvAt A (F := F) outA outSt w_out tailBytes
      w_out.b5.w9 sp.q200
    refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_right (sepConj_mono_left hrec))
    dsimp only [writebackWords63, words63At, words10At, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4,
      Reg.x5, Reg.x6, Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15,
      Reg.x16, Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x30]
    simp only [arm64_norm, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hw62]
    ac_rfl

/-! ## 3. Relocatable Call Rule and `.headerSent` `eq_ct1` Arm -/

/-- Relocatable framed call rule for `headerSentRecvCt1ChunkPlacedSpec A F` (Block `337`). -/
theorem call_headerSentRecvCt1Chunk_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (headerSentRecvCt1ChunkPlacedSpec A F)))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (outRes : Chunked.SendEk.HeaderSentRecvChunk spqrPolyApi (spqrAuthApi F))
    (hsort : PolyDecoderStrictSorted st.receiving_ct1)
    (hrecv : st.recv_ct1_chunk st.uc.epoch chunk = .ok outRes)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post Q_panic : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 .x1 = stA)
    (hx2 : s.readReg64 .x2 = st.uc.epoch)
    (hx3 : s.readReg64 .x3 = chunkA)
    (hsplit : P = (memRegion outA chunkedHeaderSentSize ∗
      chunkedHeaderSentAt A stA st ∗ chunkAt chunkA chunk ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool ∗ stackAt sp_call headerSentRecvCt1ChunkStack) ∗ Frame)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) →
      Q_panic sf P_f)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((headerSentRecvChunkAt A outA outRes ∗
          memRegion stA chunkedHeaderSentSize ∗ chunkAt chunkA chunk ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool ∗ stackAt sp_call headerSentRecvCt1ChunkStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Q_panic) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨outA, stA, chunkA, st, chunk, outRes⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ => hpanic sf _ fun hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    dsimp only [headerSentRecvCt1ChunkPlacedSpec]
    rw [hsp]
    simp only [sepConj_assoc] at hm ⊢
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hsort, hrecv⟩, hm⟩
  · dsimp only [withLsCodeRoLoaded, headerSentRecvCt1ChunkPlacedSpec] at hmem
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace.1] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [withLsCodeRoLoaded, headerSentRecvCt1ChunkPlacedSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (headerSentRecvChunkAt A outA outRes ∗
          memRegion stA chunkedHeaderSentSize ∗ chunkAt chunkA chunk ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool ∗ stackAt sp_call headerSentRecvCt1ChunkStack) ∗ Frame =
        (headerSentRecvChunkAt A outA outRes ∗
          (memRegion stA chunkedHeaderSentSize ∗
            (chunkAt chunkA chunk ∗ (tokenInitPlacedAt ∗ (reduceTablePlacedAt ∗
              (A.pool ∗ stackAt sp_call headerSentRecvCt1ChunkStack)))))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

set_option maxHeartbeats 1600000 in
/-- Relocatable `.headerSent` arm when `msg.epoch = st.uc.epoch` and `msg.payload = .ct1 chunk`
    (`+780 -> s0.x30`, `0x55760..0x558c0 -> 0x56814..0x56844 -> 0x56848..0x59ff0`, Block `332`). -/
theorem headerSent_arm_eq_ct1_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 337)
      (withLsCodeRoLoaded lsmpl (headerSentRecvCt1ChunkPlacedSpec A F)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (P_rest R : SepProp)
    {Q_post Q_panic : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsort : PolyDecoderStrictSorted st.receiving_ct1)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ct1 chunk)
    (hpc : s.pc = lsmpl.base 332 + 780#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0)
    (hdone : ∀ (sf : State) (Pf : SepProp), sf.pc = s0.readReg64 Reg.lr → sf.status = .Running →
      (Pf ⊢
        P_rest ∗
        resultV1RecvAt A (F := F) outA (States.recv K (.headerSent st) msg) ∗
        memRegion selfA chunkedStatesSize ∗
        messageAt spqrPolyApi msgA msg ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        A.pool ∗
        stackAt s0.sp statesRecvStackX) ∧
      sf.sp = s0.sp ∧
      CalleeSavedPreserved s0 sf ∧
      sf.trace = s0.trace →
      Q_post sf Pf)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) →
      Q_panic sf P_f) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 337) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sm Pm =>
        SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sm Pm Q_post Q_panic) := by
  have hcond_eq := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hmemcpy : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (sessionMemcpySpec 4096) := spqr_hook_ok_of_mem hmemcpy_sat
  have hpost_done := @headerSent_post_call_done_56848_placed _ A F ext hmemcpy_sat s0
  have hpost_still := @headerSent_post_call_still_56848_placed _ A F ext hmemcpy_sat s0
  refine sepWP_seq_lscro hcro (mid := lsmpl.base 337) ?_
  rw [lsmpl_base_332_eq] at hpc hpost_done hpost_still
  dsimp only [lsProg_332, lsρ, memcpyName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hmemcpy hcall hpost_done hpost_still hdone ⊢
  refine SepWP.fold (chunkedHeaderSentAt_pts_length A (selfA + 8#64) st) (by sep_focus) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun hlen_pts => ?_
  obtain ⟨outRes, hrecv, _⟩ := headerSent_recv_ct1_chunk_eq_ok st chunk hlen_pts hsort
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedHeaderSentAt_extract63_376 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w tailBytes
  refine SepWP.pure_elim fun ⟨hw62, _⟩ => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  wp_conv_pre =>
    dsimp only [sendEkSpillsAt, words63At, words10At]
    rw [hw62, heq, hpay, messagePayloadAt_ct1 msgA chunk]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
  wp_steps 120
  subst hsp0
  let sp1 : SendEkSpills :=
    { b0 := ⟨w.b5.w2, w.b3.w5, w.b3.w1, sp.b0.w3, w.b3.w2, w.b4.w1, w.b4.w0, sp.b0.w7, w.b3.w4, w.b3.w3⟩
      b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, w.b3.w6, w.b5.w3, w.b3.w7, sp.b1.w6, w.b5.w9, sp.b1.w8, sp.b1.w9⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, sp.b2.w5, w.b4.w8, sp.b2.w7, sp.b2.w8, w.b4.w2⟩
      b3 := ⟨sp.b3.w0, w.w62, sp.b3.w2, sp.b3.w3, sp.b3.w4, sp.b3.w5, w.b1.w3, w.b2.w5, sp.b3.w8, sp.b3.w9⟩
      b4 := ⟨w.b2.w6, w.b1.w2, sp.b4.w2, w.b1.w0, sp.b4.w4, sp.b4.w5, w.b0.w4, sp.b4.w7, sp.b4.w8, w.b2.w3⟩
      b5 := ⟨sp.b5.w0, w.b4.w4, w.b1.w4, w.b0.w8, sp.b5.w4, w.b5.w0, sp.b5.w6, w.b2.w4, w.b4.w6, sp.b5.w9⟩
      w60 := w.b5.w6, w61 := sp.w61, w62 := w.b0.w6
      q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := sp.q3c0 }
  have hfold_pre_memcpy :
      (words63At (selfA + 8#64) w ∗
       ((selfA + 8#64 + 504#64) ↦ₛ tailBytes) ∗
       relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes)) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
        chunkedHeaderSentAt A (selfA + 8#64) st ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
    sepConj_mono_left (recompose63_376 (selfA + 8#64) w tailBytes)
  refine SepWP.fold
    (F := P_rest ∗ memRegion outA v1RecvSize ∗ (selfA ↦₆₄ 4#64) ∗ memRegion (selfA + 888#64) 40 ∗
      ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 5#8) ∗ memRegion (msgA + 9#64) 1 ∗
        chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
      statesRecvSavedCells s0)
    hfold_pre_memcpy ?_ ?_
  · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
    rw [hw62, heq]
    simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    ac_rfl
  · rw [stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)]
    dsimp only [allocHookStack]
    refine call_memcpy_relocate_cs_sat (ret_pc := (blkPl_332).base + 5084#64)
      hmemcpy (Recv.Relocatable.of_chunkedHeaderSentAt A st)
      ((s0.sp - 4240#64) + 1856#64) (selfA + 8#64)
      rfl hrun hsp hfsp_align rfl htr
      (by simp only [Reg.x0, arm64_norm, hsp])
      (by simp only [Reg.x1, arm64_norm, hx1])
      rfl (by sep_focus) ?_
    intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
    have hx19_1 : sf1.readReg64 .x19 = outA := hcs1.1.trans (by simp only [Reg.x19, arm64_norm, hx19])
    have hx24_1 : sf1.readReg64 .x24 = msgA := hcs1.2.2.2.2.2.1.trans (by simp only [Reg.x24, arm64_norm, hx24])
    have hx25_1 : sf1.readReg64 .x25 = st.uc.epoch := hcs1.2.2.2.2.2.2.1.trans (by simp only [Reg.x25, arm64_norm])
    have hfold_callee :
        memRegion (s0.sp - 4240#64 - 19552#64) 15456 ∗ stackAt (s0.sp - 4240#64) 4096 ⊢
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX :=
      Entails.of_eq (stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)).symm
    refine SepWP.focus_weaken hfold_callee (by sep_focus) ?_
    have hfold_self :
        (selfA ↦₆₄ 4#64) ∗ memRegion (selfA + 8#64) 880 ∗ memRegion (selfA + 888#64) 40 ⊢
          memRegion selfA chunkedStatesSize :=
      self_880_40_entails_memRegion_928 selfA 4#64
    refine SepWP.focus_weaken hfold_self (by sep_focus) ?_
    generalize hsp0 : s0.sp = sp0 at hsp1 hfsp_align ⊢
    wp_steps 10
    subst hsp0
    refine SepWP.done rfl hrun1 (fun hcl_m => ?_)
    refine SepWP.focus_weaken
      (Entails.of_eq (stackAt_statesRecvCallee_split_headerSentRecvCt1 (s0.sp - 4240#64)))
      (by sep_focus) ?_
    refine call_headerSentRecvCt1Chunk_placed hcall
      ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1856#64) (msgA + 10#64)
      st chunk outRes hsort hrecv
      (s0 := s0) (sp_call := s0.sp - 4240#64) (ret_pc := (blkPl_332).base + 5108#64)
      (R := R)
      (Frame :=
        P_rest ∗ memRegion selfA chunkedStatesSize ∗
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 5#8) ∗ memRegion (msgA + 9#64) 1 ∗
          memRegion (msgA + 44#64) 4) ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion outA v1RecvSize ∗
        memRegion ((s0.sp - 4240#64) - 19552#64) 928 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        statesRecvSavedCells s0)
      hcl_m rfl hrun1 hsp1 hfsp_align
      (by simp only [Reg.lr, arm64_norm])
      htr1
      (by simp only [Reg.x0, arm64_norm, hsp1])
      (by simp only [Reg.x1, arm64_norm, hsp1])
      (by simp only [Reg.x2, arm64_norm, hx25_1])
      (by simp only [Reg.x3, arm64_norm, hx24_1])
      (by
        dsimp only [chunkedHeaderSentSize, statesRecvCalleeStackX, headerSentRecvCt1ChunkStack,
          polyDecoderDecodedMessageStack, extHookStack, BitVec.ofNat_eq_ofNat]
        simp only [arm64_norm]
        ac_rfl)
      hpanic
      ?_
    intro sf2 hpc2 hrun2 hsp2 hcs2 htr2
    refine SepWP.focus_weaken
      (Entails.of_eq (stackAt_statesRecvCallee_split_headerSentRecvCt1 (s0.sp - 4240#64)).symm)
      (by sep_focus) ?_
    have hmsg_eq :
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 5#8) ∗ memRegion (msgA + 9#64) 1 ∗
         chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) =
        ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) := by
      rw [hpay, messagePayloadAt_ct1 msgA chunk]
    have hx19_2 : sf2.readReg64 .x19 = outA := hcs2.1.trans (by simp only [Reg.x19, arm64_norm, hx19_1])
    have hx21_2 : sf2.readReg64 .x21 = (s0.sp - 4240#64) + 976#64 :=
      hcs2.2.2.1.trans (by simp only [Reg.x21, arm64_norm, hsp1])
    cases hout : outRes with
    | done outSt =>
      rw [hout] at hrecv
      have hmodel := states_recv_headerSent_eq_ct1_done K st msg chunk outSt heq hpay hrecv
      refine SepWP.weaken_pre (Entails.of_eq ?_)
        (SepWP.mono
          (hpost_done sf2 outA outSt sp1
            (P_rest ∗ memRegion selfA chunkedStatesSize ∗
             ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
             tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
            hpc2 hrun2 hsp2 hsp_align hx19_2 hx21_2 htr2)
          (fun sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            hdone sf Pf hpc_f hrun_f
              ⟨by rw [hmodel]; exact Entails.trans hPf (Entails.of_eq (by ac_rfl)),
               hsp_sf, hcs_sf, htr_sf⟩))
      rw [← hmsg_eq]
      dsimp only [chunkedHeaderSentSize]
      simp only [arm64_norm]; ac_rfl
    | stillReceiving outSt =>
      rw [hout] at hrecv
      have hmodel := states_recv_headerSent_eq_ct1_still K st msg chunk outSt heq hpay hrecv
      refine SepWP.weaken_pre (Entails.of_eq ?_)
        (SepWP.mono
          (hpost_still sf2 outA outSt sp1
            (P_rest ∗ memRegion selfA chunkedStatesSize ∗
             ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
             (lsLogFilterAddr ↦₆₄ 0#64) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool)
            hpc2 hrun2 hsp2 hsp_align hx19_2 hx21_2 htr2)
          (fun sf Pf hpc_f hrun_f ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            hdone sf Pf hpc_f hrun_f
              ⟨by rw [hmodel]; exact Entails.trans hPf (Entails.of_eq (by ac_rfl)),
               hsp_sf, hcs_sf, htr_sf⟩))
      rw [← hmsg_eq]
      dsimp only [chunkedHeaderSentSize]
      simp only [arm64_norm]; ac_rfl

/-! ## 4. Complete Relocatable `.headerSent` Arm (`+780 -> s0.x30`, Block `332`) -/

/-- Complete relocatable `.headerSent` arm of `<States>::recv` (`+780 -> s0.x30`, Block `332`). -/
theorem states_recv_arm_headerSent_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 337)
      (withLsCodeRoLoaded lsmpl (headerSentRecvCt1ChunkPlacedSpec A F)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (R : SepProp)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hinv : statesRecvPreInv (.headerSent st))
    (hpc : s.pc = lsmpl.base 332 + 780#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        statesRecvRoPlacedAt ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantPlacedSpec A F K (.headerSent st) msg).post (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantPlacedSpec A F K (.headerSent st) msg).onPanic (outA, selfA, msgA) s0 sf ∗ R)) := by
  by_cases hgt : msg.epoch > st.uc.epoch
  · refine sepWPp_of_statesRecv_exit_placed s0 s outA selfA msgA (.headerSent st) msg _ R ?_
    rw [states_recv_headerSent_gt K st msg hgt]
    rw [show memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.headerSent st) ∗
          messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 =
        statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.headerSent st) ∗
          messageAt spqrPolyApi msgA msg ∗ A.pool ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 by ac_rfl]
    refine SepWP.mono
      (headerSent_arm_gt_placed hdealloc s0 s outA selfA msgA st msg statesRecvRoPlacedAt
        hgt hcro.1 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · refine sepWPp_of_statesRecv_exit_placed s0 s outA selfA msgA (.headerSent st) msg _ R ?_
      rw [states_recv_headerSent_lt K st msg hlt]
      rw [show memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.headerSent st) ∗
            messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
            statesRecvSavedCells s0 =
          statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.headerSent st) ∗
            messageAt spqrPolyApi msgA msg ∗ A.pool ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
            statesRecvSavedCells s0 by ac_rfl]
      refine SepWP.mono
        (headerSent_arm_lt_sat_placed hmemcpy_sat s0 s outA selfA msgA st msg statesRecvRoPlacedAt
          hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
        (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
          ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)
    · have heq : msg.epoch = st.uc.epoch := by
        have h1 : ¬ (st.uc.epoch < msg.epoch) := hgt
        have h2 : ¬ (msg.epoch < st.uc.epoch) := hlt
        exact BitVec.le_antisymm (BitVec.not_lt.mp h1) (BitVec.not_lt.mp h2)
      cases hpay : msg.payload with
      | ct1 chunk =>
        dsimp only [statesRecvRoPlacedAt, unchunkedSendCt2PlacedRoAt]
        rw [show memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.headerSent st) ∗
              messageAt spqrPolyApi msgA msg ∗
              (statesRecvJumpTablePlacedAt ∗
                ((lsLogFilterAddr ↦₆₄ 0#64) ∗ ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel)) ∗
                tokenInitPlacedAt ∗ reduceTablePlacedAt) ∗
              A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 =
            (statesRecvJumpTablePlacedAt ∗ ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel)) ∗
              memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.headerSent st) ∗
              messageAt spqrPolyApi msgA msg ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
              tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 by ac_rfl]
        refine SepWPp.of_sepWP
          (headerSent_arm_eq_ct1_placed (K := K) hcall hmemcpy_sat s0 s outA selfA msgA st msg chunk
            (statesRecvJumpTablePlacedAt ∗ ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel)) R
            hcro hinv heq hpay hpc hrun hsp hsp_align hx1 hx19 hx24 htr
            (fun sf Pf _ _ ⟨hPf, hspf, hcs, htrf⟩ => ?_)
            (fun sf Pf hpan hmem_f => ?_))
        · refine ⟨fun hmem_f => ?_, hspf, hcs⟩
          dsimp only [statesRecvVariantPlacedSpec]
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨htrf, Satisfies.mono (sepConj_mono_left ?_) hmem_f⟩
          refine Entails.trans hPf (Entails.of_eq ?_)
          dsimp only [statesRecvRoPlacedAt, unchunkedSendCt2PlacedRoAt]; ac_rfl
        · have hpan' := hpan hmem_f
          dsimp only [statesRecvVariantPlacedSpec, statesRecvOnPanic]
          rw [sepConj_assoc, satisfies_pure_sepConj] at hpan' ⊢
          exact ⟨⟨Or.inr hpan'.1.1, hpan'.1.2⟩, hpan'.2⟩
      | none | hdr _ | ek _ | ekCt1Ack _ | ct1Ack _ | ct2 _ =>
        have hct1 : ∀ c, msg.payload ≠ .ct1 c := by intro c hc; rw [hpay] at hc; cases hc
        refine sepWPp_of_statesRecv_exit_placed s0 s outA selfA msgA (.headerSent st) msg _ R ?_
        rw [states_recv_headerSent_eq_other K st msg heq hct1]
        rw [show memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.headerSent st) ∗
              messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
              statesRecvSavedCells s0 =
            statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.headerSent st) ∗
              messageAt spqrPolyApi msgA msg ∗ A.pool ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
              statesRecvSavedCells s0 by ac_rfl]
        refine SepWP.mono
          (headerSent_arm_eq_other_sat_placed hmemcpy_sat s0 s outA selfA msgA st msg statesRecvRoPlacedAt
            heq hct1 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
          (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

/-- Top-level relocatable `subroutine_ok` theorem for `<States>::recv` (Block `332`)
    on the `.headerSent` variant. -/
theorem states_recv_headerSent_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : StatesRecvPlacedContracts A F K ext)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl (statesRecvVariantPlacedSpec A F K (.headerSent st) msg)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcro0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [statesRecvVariantPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hinv⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗ (memRegion outA v1RecvSize ∗
      chunkedStatesAt A selfA (.headerSent st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  have hpro := states_recv_prologue_placed (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.headerSent st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool) hsp0_align hpc0 hrun0
  refine sepWPp_seq_clean_lscro hcro0 hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩ hcro1
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  dsimp only [chunkedStatesAt]
  have hdisp := states_recv_dispatch_placed (ext := ext) s1 (s0.sp - 4240#64) selfA 4#64
    (chunkedHeaderSentAt A (selfA + 8#64) st ∗ memRegion (selfA + 888#64) 40 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
     statesRecvSavedCells s0)
    (by unfold ValidStatesTag; decide) hpc1 hrun1 hsp1 hx1_1
  refine sepWPp_seq_clean_lscro hcro1 (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx2_2, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩ hcro2
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  have hpre2 :
      (selfA ↦₆₄ 4#64) ∗ statesRecvRoPlacedAt ∗
      (chunkedHeaderSentAt A (selfA + 8#64) st ∗ memRegion (selfA + 888#64) 40 ∗
       memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
       stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
       statesRecvSavedCells s0) ⊢
      memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.headerSent st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0 := by
    dsimp only [chunkedStatesAt]; exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre2 ?_
  exact states_recv_arm_headerSent_placed (K := K) hC.hdealloc_sat hC.headerSentRecvCt1Chunk_ok
    hC.hmemcpy_sat s0 s2 outA selfA msgA st msg R hcro2 hinv hpc2 hrun2 hsp2 hsp0_align
    hx1_2 hx19_2 hx24_2 (htr2.trans htr1)

end LibsignalBinary.Proofs.SpqrV1.States.Recv

namespace CryptoVerification.SpqrV1.States.Recv

export LibsignalBinary.Proofs.SpqrV1.States.Recv (
  headerSent_arm_lt_sat_placed
  headerSent_arm_eq_other_sat_placed
  headerSent_post_call_done_56848_placed
  headerSent_post_call_still_56848_placed
  call_headerSentRecvCt1Chunk_placed
  headerSent_arm_eq_ct1_placed
  states_recv_arm_headerSent_placed
  states_recv_headerSent_placed_ok_ext
)

end CryptoVerification.SpqrV1.States.Recv
