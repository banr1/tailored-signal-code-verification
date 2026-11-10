/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymBasePlaced
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch5Placed
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ct1Sampled` Arm, Part 2 (Relocatable)

Relocatable `[LibsignalPlacement]` proofs on `lsProg_332` for the shared `Ok(V1Recv)` store
block (`+18996 -> +19324`) and state-copy paths (`+10500` and `+12144`).
-/

@[expose] public section

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv

open Std
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
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
open CryptoVerification.SpqrV1.States.Recv

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Shared `Ok` Return Store Block (`+18996 -> +19324`, `0x59e88 -> 0x59fd0`) -/

set_option maxHeartbeats 800000 in
theorem ct1Sampled_epilogue_store_part1_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (fsp outA : BitVec 64)
    (k : EpilogueStoreStack)
    (c0_out c1_out c2_out c3_out : Words16)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 18996#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 19280#64) s_in
      (epilogueStoreStackPart1At fsp k ∗
        wordsAt outA c0_out.toList ∗
        wordsAt (outA + 128#64) c1_out.toList ∗
        wordsAt (outA + 256#64) c2_out.toList ∗
        wordsAt (outA + 384#64) c3_out.toList ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          epilogueStoreStackPart1At fsp k ∗
          wordsAt outA (epilogueSplit928 s_in k).c0.toList ∗
          wordsAt (outA + 128#64) (epilogueSplit928 s_in k).c1.toList ∗
          wordsAt (outA + 256#64) (epilogueSplit928 s_in k).c2.toList ∗
          wordsAt (outA + 384#64) (epilogueSplit928 s_in k).c3.toList ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x0 = outA + 512#64 ∧
        sf.readReg64 .x1 = fsp + 576#64 ∧
        sf.readReg64 .x2 = 376#64 ∧
        sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp hx19
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  dsimp only [epilogueStoreStackPart1At, epilogueSplit928, Words16.toList]
  simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_done

theorem ct1Sampled_epilogue_store_part2_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s_mid : State) (fsp outA v20 : BitVec 64)
    (k : EpilogueStoreStack)
    (tail_out : Words5) (v928 v936 v944 v952 : BitVec 64)
    (Rest : SepProp)
    (hmid : k.mid.length = 376)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_mid.pc = (blkPl_332).base + 19280#64)
    (hrun : s_mid.status = .Running)
    (hsp : s_mid.sp = fsp)
    (hx0 : s_mid.readReg64 .x0 = outA + 512#64)
    (hx1 : s_mid.readReg64 .x1 = fsp + 576#64)
    (hx2 : s_mid.readReg64 .x2 = 376#64)
    (hx19 : s_mid.readReg64 .x19 = outA)
    (hx20 : s_mid.readReg64 .x20 = v20) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 19324#64) s_mid
      (epilogueStoreStackPart2At fsp k ∗
        memRegion (outA + 512#64) 376 ∗
        wordsAt (outA + 888#64) tail_out.toList ∗
        ((outA + 928#64) ↦₆₄ v928) ∗
        ((outA + 936#64) ↦₆₄ v936) ∗
        ((outA + 944#64) ↦₆₄ v944) ∗
        ((outA + 952#64) ↦₆₄ v952) ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          epilogueStoreStackPart2At fsp k ∗
          ((outA + 512#64) ↦ₛ k.mid) ∗
          wordsAt (outA + 888#64) [k.w210, k.w218, k.w220, k.w228, k.w230] ∗
          ((outA + 928#64) ↦₆₄ k.we8) ∗
          ((outA + 936#64) ↦₆₄ v20) ∗
          ((outA + 944#64) ↦₆₄ k.w200) ∗
          ((outA + 952#64) ↦₆₄ k.w208) ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        TraceCalleeSaved sf s_mid) := by
  subst hsp hx19 hx20
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec :=
    spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_mid.sp
  rw [hsplit, ← hmid]
  dsimp only [lsProg_332, lsρ, spqrMemcpySym, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  dsimp only [epilogueStoreStackPart2At, Words5.toList, sessionMemcpySpec, allocHookStack] at hmemcpy_raw ⊢
  simp only [wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_call hmemcpy_raw (s_mid.readReg64 .x19 + 512#64, s_mid.sp + 576#64, k.mid)
  wp_steps
  wp_done

theorem ct1Sampled_epilogue_store_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s_in : State) (fsp outA : BitVec 64)
    (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hmid : k.mid.length = 376)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 18996#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 19324#64) s_in
      (epilogueStoreStackPart1At fsp k ∗
        epilogueStoreStackPart2At fsp k ∗
        memRegion outA chunkedStatesSize ∗
        memRegion (outA + 928#64) 32 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          epilogueStoreStackPart1At fsp k ∗
          epilogueStoreStackPart2At fsp k ∗
          split928At outA (epilogueSplit928 s_in k) ∗
          ((outA + 928#64) ↦₆₄ k.we8) ∗
          ((outA + 936#64) ↦₆₄ (s_in.readReg64 .x20)) ∗
          ((outA + 944#64) ↦₆₄ k.w200) ∗
          ((outA + 952#64) ↦₆₄ k.w208) ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        TraceCalleeSaved sf s_in) := by
  have hpre :
      epilogueStoreStackPart1At fsp k ∗
      epilogueStoreStackPart2At fsp k ∗
      memRegion outA chunkedStatesSize ∗
      memRegion (outA + 928#64) 32 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      Rest ⊢
      ∃∗ d_out : Split928, ∃∗ v928 : BitVec 64, ∃∗ v936 : BitVec 64,
      ∃∗ v944 : BitVec 64, ∃∗ v952 : BitVec 64,
        epilogueStoreStackPart1At fsp k ∗
        wordsAt outA d_out.c0.toList ∗
        wordsAt (outA + 128#64) d_out.c1.toList ∗
        wordsAt (outA + 256#64) d_out.c2.toList ∗
        wordsAt (outA + 384#64) d_out.c3.toList ∗
        (epilogueStoreStackPart2At fsp k ∗
          memRegion (outA + 512#64) 376 ∗
          wordsAt (outA + 888#64) d_out.tail.toList ∗
          ((outA + 928#64) ↦₆₄ v928) ∗
          ((outA + 936#64) ↦₆₄ v936) ∗
          ((outA + 944#64) ↦₆₄ v944) ∗
          ((outA + 952#64) ↦₆₄ v952) ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (memRegion_928_entails_split928 outA)
        (sepConj_mono_left (memRegion_32_entails_words4 (outA + 928#64)))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply Entails.sepExists_elim; intro v952
    apply Entails.sepExists_elim; intro v944
    apply Entails.sepExists_elim; intro v936
    apply Entails.sepExists_elim; intro v928
    apply Entails.sepExists_elim; intro d_out
    refine Entails.sepExists_right d_out (Entails.sepExists_right v928
      (Entails.sepExists_right v936 (Entails.sepExists_right v944
        (Entails.sepExists_right v952 ?_))))
    rw [show epilogueStoreStackPart1At fsp k ∗
        (epilogueStoreStackPart2At fsp k ∗
          ((⌜d_out.mid.length = 376⌝ ∗ split928At outA d_out) ∗
            ((((outA + 928#64) ↦₆₄ v928) ∗ ((outA + 936#64) ↦₆₄ v936) ∗
              ((outA + 944#64) ↦₆₄ v944) ∗ ((outA + 952#64) ↦₆₄ v952)) ∗
            (stackAt fsp statesRecvCalleeStackX ∗ Rest)))) =
        ⌜d_out.mid.length = 376⌝ ∗
        ((outA + 512#64) ↦ₛ d_out.mid) ∗
        (epilogueStoreStackPart1At fsp k ∗
          wordsAt outA d_out.c0.toList ∗
          wordsAt (outA + 128#64) d_out.c1.toList ∗
          wordsAt (outA + 256#64) d_out.c2.toList ∗
          wordsAt (outA + 384#64) d_out.c3.toList ∗
          (epilogueStoreStackPart2At fsp k ∗
            wordsAt (outA + 888#64) d_out.tail.toList ∗
            ((outA + 928#64) ↦₆₄ v928) ∗
            ((outA + 936#64) ↦₆₄ v936) ∗
            ((outA + 944#64) ↦₆₄ v944) ∗
            ((outA + 952#64) ↦₆₄ v952) ∗
            stackAt fsp statesRecvCalleeStackX ∗
            Rest)) by
      dsimp only [split928At]; ac_rfl]
    apply Entails.pure_left; intro hd_mid
    refine Entails.trans (sepConj_mono_left
      (pointsToBytes_entails_memRegion_376 (outA + 512#64) d_out.mid hd_mid)) ?_
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro d_out
  apply ProofLib.SepWP.exists_left; intro v928
  apply ProofLib.SepWP.exists_left; intro v936
  apply ProofLib.SepWP.exists_left; intro v944
  apply ProofLib.SepWP.exists_left; intro v952
  refine SepWP.seq (ct1Sampled_epilogue_store_part1_placed s_in fsp outA k
    d_out.c0 d_out.c1 d_out.c2 d_out.c3 _ hfsp_align hpc hrun hsp hx19) ?_
  intro s_mid P_mid hpc_mid hrun_mid ⟨hP_mid, hsp_mid, hx0_mid, hx1_mid, hx2_mid, hx19_mid, hx20_mid, htr_mid⟩
  have hP_mid' : P_mid ⊢
      epilogueStoreStackPart2At fsp k ∗
      memRegion (outA + 512#64) 376 ∗
      wordsAt (outA + 888#64) d_out.tail.toList ∗
      ((outA + 928#64) ↦₆₄ v928) ∗
      ((outA + 936#64) ↦₆₄ v936) ∗
      ((outA + 944#64) ↦₆₄ v944) ∗
      ((outA + 952#64) ↦₆₄ v952) ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (epilogueStoreStackPart1At fsp k ∗
        wordsAt outA (epilogueSplit928 s_in k).c0.toList ∗
        wordsAt (outA + 128#64) (epilogueSplit928 s_in k).c1.toList ∗
        wordsAt (outA + 256#64) (epilogueSplit928 s_in k).c2.toList ∗
        wordsAt (outA + 384#64) (epilogueSplit928 s_in k).c3.toList ∗
        Rest) :=
    Entails.trans hP_mid (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hP_mid' ?_
  refine SepWP.mono
    (ct1Sampled_epilogue_store_part2_placed hmemcpy s_mid fsp outA (s_in.readReg64 .x20) k
      d_out.tail v928 v936 v944 v952 _ hmid hfsp_align hpc_mid hrun_mid
      hsp_mid hx0_mid hx1_mid hx2_mid hx19_mid hx20_mid) ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, htr_f⟩
  refine ⟨?_, hsp_f, htr_f.trans htr_mid⟩
  refine Entails.trans hPf ?_
  dsimp only [split928At, epilogueSplit928, Words5.toList]
  exact Entails.of_eq (by ac_rfl)

/-! ## 2. State-Copy Paths (`+10500 -> +18996` and `+12144 -> +18996`) -/

set_option maxHeartbeats 1200000 in
theorem ct1Sampled_copy_lt_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s_in : State) (fsp stA outA : BitVec 64)
    (d : Split928) (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hmid : d.mid.length = 376)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 10500#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = stA)
    (hx12 : s_in.readReg64 .x12 = d.c0.w0)
    (hx19 : s_in.readReg64 .x19 = outA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 18996#64) s_in
      (split928At stA d ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ k.we8) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        memRegion (fsp + 576#64) 376 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          split928At stA d ∗
          copyScratchStackAt fsp (copyLtScratch sc d) ∗
          epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        epilogueRegsEqSplit928 sf d ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp hx1 hx19
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec :=
    spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_in.sp
  rw [hsplit, ← hmid]
  dsimp only [lsProg_332, lsρ, spqrMemcpySym, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  dsimp only [split928At, copyScratchStackAt, epilogueStoreStackPart1At, epilogueStoreStackPart2At,
    copyLtScratch, epilogueStackOfSplit928, epilogueRegsEqSplit928, EpilogueStoreStack.tail,
    noneCap, Words16.toList, Words5.toList, sessionMemcpySpec, allocHookStack] at hmemcpy_raw ⊢
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_call hmemcpy_raw (s_in.sp + 576#64, s_in.readReg64 .x1 + 512#64, d.mid)
  wp_steps
  wp_done

set_option maxHeartbeats 1200000 in
theorem ct1Sampled_copy_other_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s_in : State) (fsp stA outA : BitVec 64)
    (d : Split928) (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hmid : d.mid.length = 376)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 12144#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = stA)
    (hx12 : s_in.readReg64 .x12 = d.c0.w0)
    (hx19 : s_in.readReg64 .x19 = outA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 18996#64) s_in
      (split928At stA d ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ k.we8) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        memRegion (fsp + 576#64) 376 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          split928At stA d ∗
          copyScratchStackAt fsp (copyOtherScratch sc d) ∗
          epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        epilogueRegsEqSplit928 sf d ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp hx1 hx19
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec :=
    spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_in.sp
  rw [hsplit, ← hmid]
  dsimp only [lsProg_332, lsρ, spqrMemcpySym, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  dsimp only [split928At, copyScratchStackAt, epilogueStoreStackPart1At, epilogueStoreStackPart2At,
    copyOtherScratch, epilogueStackOfSplit928, epilogueRegsEqSplit928, EpilogueStoreStack.tail,
    noneCap, Words16.toList, Words5.toList, sessionMemcpySpec, allocHookStack] at hmemcpy_raw ⊢
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_call hmemcpy_raw (s_in.sp + 576#64, s_in.readReg64 .x1 + 512#64, d.mid)
  wp_steps
  wp_done

end LibsignalBinary.Proofs.SpqrV1.States.Recv

namespace CryptoVerification.SpqrV1.States.Recv

export LibsignalBinary.Proofs.SpqrV1.States.Recv (
  ct1Sampled_epilogue_store_part1_placed
  ct1Sampled_epilogue_store_part2_placed
  ct1Sampled_epilogue_store_placed
  ct1Sampled_copy_lt_placed
  ct1Sampled_copy_other_placed
)

end CryptoVerification.SpqrV1.States.Recv
