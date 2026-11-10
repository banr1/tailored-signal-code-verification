/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart4
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch4Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch5Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ct1Sampled` Arm, Part 4 (Relocatable)

Relocatable `[LibsignalPlacement]` `ack` branch at `+13968` and `outMsg = none` Paths 4a
(`ack = false`) and 4b (`ack = true`).
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

/-! ## 1. Branch on `w22` (`ack`) at `+13968` -/

theorem ct1Sampled_none_branch_no_ack_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (Rest : SepProp)
    (hpc : s_in.pc = (blkPl_332).base + 13968#64)
    (hrun : s_in.status = .Running)
    (hx22 : s_in.readReg64 .x22 = 0#64) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 16184#64) s_in
      Rest
      (fun sf Pf =>
        (Pf ⊢ Rest) ∧
        sf = s_in.setPC ((blkPl_332).base + 16184#64)) := by
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  wp_done

theorem ct1Sampled_none_branch_ack_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (Rest : SepProp)
    (hpc : s_in.pc = (blkPl_332).base + 13968#64)
    (hrun : s_in.status = .Running)
    (hx22 : s_in.readReg64 .x22 = 1#64) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 13972#64) s_in
      Rest
      (fun sf Pf =>
        (Pf ⊢ Rest) ∧
        sf = s_in.setPC ((blkPl_332).base + 13972#64)) := by
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  wp_done

/-! ## 2. Path 4a (`outMsg = none, ack = false`): `+16184 -> +16596 -> +18996` -/

set_option maxHeartbeats 1600000 in
theorem ct1Sampled_copy_none_no_ack_part1_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s_in : State) (fsp stA : BitVec 64)
    (c0 c1 c2 c3 : Words16) (w512 w520 : BitVec 64) (d400 : Split400)
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (v976 v984 v992 vc90 vc98 v4096 v4104 v4112 : BitVec 64)
    (Rest : SepProp)
    (hmid352 : d400.mid352.length = 352)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 16184#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64) :
    let d := mkSplit928From528And400 c0 c1 c2 c3 w512 w520 d400
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 16596#64) s_in
      (wordsAt stA c0.toList ∗
        wordsAt (stA + 128#64) c1.toList ∗
        wordsAt (stA + 256#64) c2.toList ∗
        wordsAt (stA + 384#64) c3.toList ∗
        ((stA + 512#64) ↦₆₄ w512) ∗
        ((stA + 520#64) ↦₆₄ w520) ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗
        split400At (fsp + 2752#64) d400 ∗
        memRegion (fsp + 1872#64) 400 ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 976#64) ↦₆₄ v976) ∗
        ((fsp + 984#64) ↦₆₄ v984) ∗
        ((fsp + 992#64) ↦₆₄ v992) ∗
        memRegion (fsp + 1000#64) 392 ∗
        ((fsp + 3216#64) ↦₆₄ vc90) ∗
        ((fsp + 3224#64) ↦₆₄ vc98) ∗
        ((fsp + 4096#64) ↦₆₄ v4096) ∗
        ((fsp + 4104#64) ↦₆₄ v4104) ∗
        ((fsp + 4112#64) ↦₆₄ v4112) ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          wordsAt stA c0.toList ∗
          wordsAt (stA + 128#64) c1.toList ∗
          wordsAt (stA + 256#64) c2.toList ∗
          wordsAt (stA + 384#64) c3.toList ∗
          ((stA + 512#64) ↦₆₄ w512) ∗
          ((stA + 520#64) ↦₆₄ w520) ∗
          ((fsp + 232#64) ↦₆₄ stA) ∗
          memRegion (fsp + 2752#64) 400 ∗
          memRegion (fsp + 1872#64) 400 ∗
          copyScratchStackAt fsp (copyFullScratch sc d) ∗
          epilogueStoreStackPart1At fsp
            { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
              we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
          mid376At (fsp + 976#64) w512 w520 d400.w0 d400.mid352 ∗
          wordsAt (fsp + 1352#64) d400.tail.toList ∗
          ((fsp + 3216#64) ↦₆₄ c3.w13) ∗
          ((fsp + 3224#64) ↦₆₄ c3.w14) ∗
          memRegion (fsp + 4096#64) 24 ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x29 = fsp + 4144#64 ∧
        TraceCalleeSaved sf s_in) := by
  intro d
  subst hsp
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec :=
    spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_in.sp
  have h400_len := d400.toBytes_length hmid352
  have h392_len := d400.tailBytes_length hmid352
  have h1872_split :
      ((s_in.sp + 1872#64) ↦ₛ d400.toBytes) =
        ((s_in.sp + 1872#64) ↦₆₄ d400.w0) ∗ ((s_in.sp + 1880#64) ↦ₛ d400.tailBytes) := by
    rw [← split400At_eq_pointsToBytes (s_in.sp + 1872#64) d400 hmid352,
        split400At_eq_w0_tailBytes (s_in.sp + 1872#64) d400 hmid352]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h2752_split :
      ((s_in.sp + 2752#64) ↦ₛ d400.toBytes) =
        ((s_in.sp + 2752#64) ↦₆₄ d400.w0) ∗ ((s_in.sp + 2760#64) ↦ₛ d400.tailBytes) := by
    rw [← split400At_eq_pointsToBytes (s_in.sp + 2752#64) d400 hmid352,
        split400At_eq_w0_tailBytes (s_in.sp + 2752#64) d400 hmid352]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h1000_split :
      ((s_in.sp + 1000#64) ↦ₛ d400.tailBytes) =
        ((s_in.sp + 1000#64) ↦ₛ d400.mid352) ∗ wordsAt (s_in.sp + 1352#64) d400.tail.toList := by
    dsimp only [Split400.tailBytes]
    rw [pointsToBytes_append (s_in.sp + 1000#64) d400.mid352 (wordsBytes d400.tail.toList),
        hmid352, ← wordsAt_eq_pointsToBytes]
    have ha : (s_in.sp + 1000#64) + BitVec.ofNat 64 352 = s_in.sp + 1352#64 := by bv_omega
    rw [ha]
  rw [split400At_eq_pointsToBytes (s_in.sp + 2752#64) d400 hmid352]
  refine SepWP.mono (post := fun sf Pf =>
      (Pf ⊢
        wordsAt stA c0.toList ∗
        wordsAt (stA + 128#64) c1.toList ∗
        wordsAt (stA + 256#64) c2.toList ∗
        wordsAt (stA + 384#64) c3.toList ∗
        ((stA + 512#64) ↦₆₄ w512) ∗
        ((stA + 520#64) ↦₆₄ w520) ∗
        ((s_in.sp + 232#64) ↦₆₄ stA) ∗
        (((s_in.sp + 2752#64) ↦₆₄ d400.w0) ∗ ((s_in.sp + 2760#64) ↦ₛ d400.tailBytes)) ∗
        (((s_in.sp + 1872#64) ↦₆₄ d400.w0) ∗ ((s_in.sp + 1880#64) ↦ₛ d400.tailBytes)) ∗
        copyScratchStackAt s_in.sp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At s_in.sp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        mid376At (s_in.sp + 976#64) w512 w520 d400.w0 d400.mid352 ∗
        wordsAt (s_in.sp + 1352#64) d400.tail.toList ∗
        ((s_in.sp + 3216#64) ↦₆₄ c3.w13) ∗
        ((s_in.sp + 3224#64) ↦₆₄ c3.w14) ∗
        (((s_in.sp + 4096#64) ↦₆₄ w512) ∗
          ((s_in.sp + 4104#64) ↦₆₄ w520) ∗
          ((s_in.sp + 4112#64) ↦₆₄ d400.w0)) ∗
        stackAt s_in.sp statesRecvCalleeStackX ∗
        Rest) ∧
      sf.sp = s_in.sp ∧
      sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
      sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
      sf.readReg64 .x29 = s_in.sp + 4144#64 ∧
      TraceCalleeSaved sf s_in) ?_ (fun sf Pf _ _ ⟨hPf, hrest⟩ => ⟨Entails.trans hPf ?_, hrest⟩)
  · rw [hsplit, ← h400_len, ← h392_len]
    dsimp only [lsProg_332, lsρ, spqrMemcpySym, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
    dsimp only [d, mkSplit928From528And400, copyScratchStackAt, copyFullScratch,
      epilogueStoreStackPart1At, epilogueStackOfSplit928, mid376At, Words16.toList,
      sessionMemcpySpec, allocHookStack] at hmemcpy_raw ⊢
    simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd, hx29]
    wp_steps
    wp_call hmemcpy_raw (s_in.sp + 1872#64, s_in.sp + 2752#64, d400.toBytes)
    refine SepWP.focus_weaken (Entails.of_eq h1872_split) (by sep_focus) ?_
    refine SepWP.focus_weaken (Entails.of_eq h2752_split) (by sep_focus) ?_
    wp_steps
    wp_call hmemcpy_raw (s_in.sp + 1000#64, s_in.sp + 2760#64, d400.tailBytes)
    refine SepWP.focus_weaken (Entails.of_eq h1000_split) (by sep_focus) ?_
    wp_done
  · have h2752_mr :
        ((s_in.sp + 2752#64) ↦₆₄ d400.w0) ∗ ((s_in.sp + 2760#64) ↦ₛ d400.tailBytes) ⊢
        memRegion (s_in.sp + 2752#64) 400 := by
      rw [← h2752_split, ← h400_len]
      exact ProofLib.pointsToBytes_entails_memRegion _ _
    have h1872_mr :
        ((s_in.sp + 1872#64) ↦₆₄ d400.w0) ∗ ((s_in.sp + 1880#64) ↦ₛ d400.tailBytes) ⊢
        memRegion (s_in.sp + 1872#64) 400 := by
      rw [← h1872_split, ← h400_len]
      exact ProofLib.pointsToBytes_entails_memRegion _ _
    have h4096_mr :
        ((s_in.sp + 4096#64) ↦₆₄ w512) ∗
          ((s_in.sp + 4104#64) ↦₆₄ w520) ∗
          ((s_in.sp + 4112#64) ↦₆₄ d400.w0) ⊢
        memRegion (s_in.sp + 4096#64) 24 := by
      rw [ProofLib.memRegion_split' (b := s_in.sp + 4096#64) (n := 8) (k := 16)
            (b' := s_in.sp + 4104#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s_in.sp + 4104#64) (n := 8) (k := 8)
            (b' := s_in.sp + 4112#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (ProofLib.pointsTo64_entails_memRegion _ _))
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono h2752_mr (sepConj_mono h1872_mr (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h4096_mr)))))))))))))))

set_option maxHeartbeats 1600000 in
theorem ct1Sampled_copy_none_no_ack_part2_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s_in : State) (fsp stA outA : BitVec 64)
    (c0 c1 c2 c3 : Words16) (w512 w520 : BitVec 64) (d400 : Split400)
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (c_ca0 : Words5)
    (Rest : SepProp)
    (htag : c0.w0 = 0#64 ∨ c0.w0 = 1#64)
    (hmid352 : d400.mid352.length = 352)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 16596#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx23 : s_in.readReg64 .x23 = c0.w0) :
    let d := mkSplit928From528And400 c0 c1 c2 c3 w512 w520 d400
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 18996#64) s_in
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        memRegion (fsp + 576#64) 376 ∗
        mid376At (fsp + 976#64) w512 w520 d400.w0 d400.mid352 ∗
        wordsAt (fsp + 1352#64) d400.tail.toList ∗
        ((fsp + 3216#64) ↦₆₄ c3.w13) ∗
        ((fsp + 3224#64) ↦₆₄ c3.w14) ∗
        wordsAt (fsp + 3232#64) c_ca0.toList ∗
        memRegion (fsp + 3272#64) 376 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          copyScratchStackAt fsp (copyFullScratch sc d) ∗
          epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          memRegion (fsp + 976#64) 376 ∗
          memRegion (fsp + 1352#64) 40 ∗
          memRegion (fsp + 3216#64) 16 ∗
          memRegion (fsp + 3232#64) 40 ∗
          memRegion (fsp + 3272#64) 376 ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        epilogueRegsEqSplit928 sf d ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  intro d
  subst hsp hx19
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec :=
    spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_in.sp
  have hmid376_len : (mid376Bytes w512 w520 d400.w0 d400.mid352).length = 376 :=
    mid376Bytes_length w512 w520 d400.w0 hmid352
  rw [mid376At_eq_pointsToBytes (s_in.sp + 976#64) w512 w520 d400.w0 d400.mid352]
  change SepWP (lsProg_332 (Rust.withPanics ext))
    ((blkPl_332).base + 18996#64) s_in
    (copyScratchStackAt s_in.sp (copyFullScratch sc d) ∗
      epilogueStoreStackPart1At s_in.sp
        { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
          we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
      ((s_in.sp + 232#64) ↦₆₄ stA) ∗
      ((s_in.sp + 512#64) ↦₆₄ k.w200) ∗
      ((s_in.sp + 520#64) ↦₆₄ k.w208) ∗
      wordsAt (s_in.sp + 528#64) k.tail.toList ∗
      memRegion (s_in.sp + 576#64) 376 ∗
      ((s_in.sp + 976#64) ↦ₛ d.mid) ∗
      wordsAt (s_in.sp + 1352#64) d.tail.toList ∗
      ((s_in.sp + 3216#64) ↦₆₄ c3.w13) ∗
      ((s_in.sp + 3224#64) ↦₆₄ c3.w14) ∗
      wordsAt (s_in.sp + 3232#64) c_ca0.toList ∗
      memRegion (s_in.sp + 3272#64) 376 ∗
      stackAt s_in.sp statesRecvCalleeStackX ∗
      Rest) _
  refine SepWP.mono (post := fun sf Pf =>
      (Pf ⊢
        copyScratchStackAt s_in.sp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At s_in.sp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
        epilogueStoreStackPart2At s_in.sp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
        ((s_in.sp + 976#64) ↦ₛ d.mid) ∗
        wordsAt (s_in.sp + 1352#64) d.tail.toList ∗
        (((s_in.sp + 3216#64) ↦₆₄ c3.w13) ∗ ((s_in.sp + 3224#64) ↦₆₄ c3.w14)) ∗
        wordsAt (s_in.sp + 3232#64) d.tail.toList ∗
        ((s_in.sp + 3272#64) ↦ₛ d.mid) ∗
        stackAt s_in.sp statesRecvCalleeStackX ∗
        Rest) ∧
      epilogueRegsEqSplit928 sf d ∧
      sf.sp = s_in.sp ∧
      sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
      sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
      TraceCalleeSaved sf s_in) ?_ (fun sf Pf _ _ ⟨hPf, hrest⟩ => ⟨Entails.trans hPf ?_, hrest⟩)
  · rw [hsplit, show (376 : Nat) = (mid376Bytes w512 w520 d400.w0 d400.mid352).length from hmid376_len.symm]
    dsimp only [lsProg_332, lsρ, spqrMemcpySym, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
    dsimp only [d, mkSplit928From528And400, copyScratchStackAt, copyFullScratch,
      epilogueStoreStackPart1At, epilogueStoreStackPart2At, epilogueStackOfSplit928,
      epilogueRegsEqSplit928, EpilogueStoreStack.tail, noneCap, Words16.toList, Words5.toList,
      sessionMemcpySpec, allocHookStack] at hmemcpy_raw ⊢
    simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx23]
    rcases htag with h0 | h0 <;> rw [h0]
    · wp_steps
      wp_call hmemcpy_raw (s_in.sp + 3272#64, s_in.sp + 976#64, mid376Bytes w512 w520 d400.w0 d400.mid352)
      wp_steps
      wp_call hmemcpy_raw (s_in.sp + 576#64, s_in.sp + 3272#64, mid376Bytes w512 w520 d400.w0 d400.mid352)
      wp_steps
      wp_done
    · wp_steps
      wp_call hmemcpy_raw (s_in.sp + 3272#64, s_in.sp + 976#64, mid376Bytes w512 w520 d400.w0 d400.mid352)
      wp_steps
      wp_call hmemcpy_raw (s_in.sp + 576#64, s_in.sp + 3272#64, mid376Bytes w512 w520 d400.w0 d400.mid352)
      wp_steps
      wp_done
  · have h976_mr := pointsToBytes_entails_memRegion_376 (s_in.sp + 976#64) d.mid hmid376_len
    have h1352_mr := wordsAt_entails_memRegion d.tail.toList (s_in.sp + 1352#64) 40 rfl
    have h3216_mr :
        ((s_in.sp + 3216#64) ↦₆₄ c3.w13) ∗ ((s_in.sp + 3224#64) ↦₆₄ c3.w14) ⊢
        memRegion (s_in.sp + 3216#64) 16 := by
      rw [ProofLib.memRegion_split' (b := s_in.sp + 3216#64) (n := 8) (k := 8)
            (b' := s_in.sp + 3224#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (ProofLib.pointsTo64_entails_memRegion _ _)
    have h3232_mr := wordsAt_entails_memRegion d.tail.toList (s_in.sp + 3232#64) 40 rfl
    have h3272_mr := pointsToBytes_entails_memRegion_376 (s_in.sp + 3272#64) d.mid hmid376_len
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono h976_mr (sepConj_mono h1352_mr (sepConj_mono h3216_mr
        (sepConj_mono h3232_mr (sepConj_mono_left h3272_mr)))))))

/-! ## 3. Path 4b (`outMsg = none, ack = true`): `+13972 -> +16596 -> +17192 -> +18996` -/

set_option maxHeartbeats 1600000 in
theorem ct1Sampled_copy_none_ack_part1_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s_in : State) (fsp stA : BitVec 64)
    (vecs : List (List GF16)) (hvecs_len : vecs.length = NUM_POLYS)
    (c_uc : Words16) (c_dec : Words50)
    (bs352_mid : List (BitVec 8)) (tail5_mid : Words5)
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (v976 v984 v992 vc90 vc98 : BitVec 64)
    (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 13972#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) :
    let d := mkSplit928Ct1Acknowledged c_uc c_dec bs352_mid tail5_mid
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 16596#64) s_in
      (vecGF16ListOf A (stA + 8#64) vecs ∗
        wordsAt (stA + 400#64) c_uc.toList ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗
        words50At (fsp + 2752#64) c_dec ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 976#64) ↦₆₄ v976) ∗
        ((fsp + 984#64) ↦₆₄ v984) ∗
        ((fsp + 992#64) ↦₆₄ v992) ∗
        ((fsp + 3216#64) ↦₆₄ vc90) ∗
        ((fsp + 3224#64) ↦₆₄ vc98) ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          memRegion (stA + 8#64) 384 ∗
          wordsAt (stA + 400#64) c_uc.toList ∗
          ((fsp + 232#64) ↦₆₄ stA) ∗
          memRegion (fsp + 2752#64) 400 ∗
          copyScratchStackAt fsp (copyFullScratch sc d) ∗
          epilogueStoreStackPart1At fsp
            { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
              we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
          ((fsp + 976#64) ↦₆₄ c_dec.c2.w15) ∗
          ((fsp + 984#64) ↦₆₄ c_dec.w48) ∗
          ((fsp + 992#64) ↦₆₄ c_dec.w49) ∗
          ((fsp + 3216#64) ↦₆₄ c_dec.c2.w12) ∗
          ((fsp + 3224#64) ↦₆₄ c_dec.c2.w13) ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x23 = 2#64 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  intro d
  subst hsp
  have hsplit := stackAt_statesRecvCallee_eq_dropGluePoly16' s_in.sp
  refine SepWP.mono (post := fun sf Pf =>
      (Pf ⊢
        memRegion (stA + 8#64) 384 ∗
        wordsAt (stA + 400#64) c_uc.toList ∗
        ((s_in.sp + 232#64) ↦₆₄ stA) ∗
        words50At (s_in.sp + 2752#64) c_dec ∗
        copyScratchStackAt s_in.sp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At s_in.sp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((s_in.sp + 976#64) ↦₆₄ c_dec.c2.w15) ∗
        ((s_in.sp + 984#64) ↦₆₄ c_dec.w48) ∗
        ((s_in.sp + 992#64) ↦₆₄ c_dec.w49) ∗
        ((s_in.sp + 3216#64) ↦₆₄ c_dec.c2.w12) ∗
        ((s_in.sp + 3224#64) ↦₆₄ c_dec.c2.w13) ∗
        A.pool ∗
        stackAt s_in.sp statesRecvCalleeStackX ∗
        Rest) ∧
      sf.sp = s_in.sp ∧
      sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
      sf.readReg64 .x23 = 2#64 ∧
      sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
      sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
      sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
      TraceCalleeSaved sf s_in) ?_ (fun sf Pf _ _ ⟨hPf, hrest⟩ => ⟨Entails.trans hPf ?_, hrest⟩)
  · rw [hsplit]
    refine ct1Sampled_seq_clean_lscl hcl (mid := lsmpl.base 265)
      (P_mid := vecGF16ListOf A (stA + 8#64) vecs ∗
        wordsAt (stA + 400#64) c_uc.toList ∗
        ((s_in.sp + 232#64) ↦₆₄ stA) ∗
        words50At (s_in.sp + 2752#64) c_dec ∗
        copyScratchStackAt s_in.sp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At s_in.sp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((s_in.sp + 976#64) ↦₆₄ c_dec.c2.w15) ∗
        ((s_in.sp + 984#64) ↦₆₄ c_dec.w48) ∗
        ((s_in.sp + 992#64) ↦₆₄ c_dec.w49) ∗
        ((s_in.sp + 3216#64) ↦₆₄ c_dec.c2.w12) ∗
        ((s_in.sp + 3224#64) ↦₆₄ c_dec.c2.w13) ∗
        A.pool ∗
        memRegion (s_in.sp - 19552#64) 15424 ∗
        stackAt s_in.sp dropGluePoly16Stack ∗
        Rest)
      (Q := fun sm => sm.sp = s_in.sp ∧
        sm.readReg64 .x0 = stA + 8#64 ∧
        sm.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sm.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sm.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sm.readReg64 .x29 = s_in.readReg64 .x29 ∧
        sm.readReg64 .x30 = (blkPl_332).base + 14416#64 ∧
        TraceCalleeSaved sm s_in) ?_ ?_
    · dsimp only [lsProg_332, d, mkSplit928Ct1Acknowledged, copyScratchStackAt, copyFullScratch,
        epilogueStoreStackPart1At, epilogueStackOfSplit928, words50At, Words16.toList,
        BitVec.ofNat_eq_ofNat]
        at hpc ⊢
      simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd]
      wp_steps
      wp_done
    · intro sm hpcm hrunm hclm ⟨hspm, hx0m, hx19m, hx24m, hx28m, hx29m, hx30m, htrm⟩
      have hdrop := drop_glue_poly16_mem_on
        (callerProg := lsProg_332 (Rust.withPanics ext)) hdealloc hclm
      dsimp only [lsProg_332, withMemEq, dropGluePoly16Spec, polyArrayBytes, BitVec.ofNat_eq_ofNat]
        at hpcm hdrop ⊢
      rw [← hspm]
      wp_call hdrop ⟨stA + 8#64, vecs⟩
      wp_steps
      rw [hspm]
      wp_done
  · have h2752_mr := words50At_entails_memRegion (s_in.sp + 2752#64) c_dec
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h2752_mr)))

theorem ct1Sampled_copy_none_ack_part2a_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s_in : State) (fsp : BitVec 64)
    (w0 w8 w16 : BitVec 64) (bs352_976 : List (BitVec 8))
    (c_1352 c_ca0 : Words5)
    (Rest : SepProp)
    (h976_len : bs352_976.length = 352)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 16596#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx23 : s_in.readReg64 .x23 = 2#64)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 17192#64) s_in
      (mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗
        wordsAt (fsp + 1352#64) c_1352.toList ∗
        wordsAt (fsp + 3232#64) c_ca0.toList ∗
        memRegion (fsp + 3272#64) 376 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗
          wordsAt (fsp + 1352#64) c_1352.toList ∗
          wordsAt (fsp + 3232#64) c_1352.toList ∗
          mid376At (fsp + 3272#64) w0 w8 w16 bs352_976 ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x28 = fsp + 3272#64 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec :=
    spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_in.sp
  have hmid376_len : (mid376Bytes w0 w8 w16 bs352_976).length = 376 :=
    mid376Bytes_length w0 w8 w16 h976_len
  rw [mid376At_eq_pointsToBytes (s_in.sp + 976#64) w0 w8 w16 bs352_976,
      mid376At_eq_pointsToBytes (s_in.sp + 3272#64) w0 w8 w16 bs352_976,
      hsplit, ← hmid376_len]
  dsimp only [lsProg_332, lsρ, spqrMemcpySym, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  dsimp only [Words5.toList, sessionMemcpySpec, allocHookStack] at hmemcpy_raw ⊢
  simp only [wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx23, hx28]
  wp_steps
  wp_call hmemcpy_raw (s_in.sp + 3272#64, s_in.sp + 976#64, mid376Bytes w0 w8 w16 bs352_976)
  wp_steps
  wp_done

set_option maxHeartbeats 1600000 in
theorem ct1Sampled_copy_none_ack_part2b_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (fsp stA outA : BitVec 64)
    (c_uc : Words16) (c_dec : Words50)
    (bs352_976 bs352_576 : List (BitVec 8))
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (v576 v584 v592 vf10 vf18 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 17192#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64) :
    let d := mkSplit928Ct1Acknowledged c_uc c_dec bs352_576 k.tail
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 18996#64) s_in
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
        mid376At (fsp + 976#64) c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352_976 ∗
        ((fsp + 3216#64) ↦₆₄ c_dec.c2.w12) ∗
        ((fsp + 3224#64) ↦₆₄ c_dec.c2.w13) ∗
        mid376At (fsp + 3272#64) c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352_976 ∗
        ((fsp + 3856#64) ↦₆₄ vf10) ∗
        ((fsp + 3864#64) ↦₆₄ vf18) ∗
        statesRecvRoPlacedAt ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          copyScratchStackAt fsp (copyFullScratch sc d) ∗
          epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          mid376At (fsp + 976#64) c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352_976 ∗
          ((fsp + 3216#64) ↦₆₄ c_dec.c2.w12) ∗
          ((fsp + 3224#64) ↦₆₄ c_dec.c2.w13) ∗
          mid376At (fsp + 3272#64) c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352_976 ∗
          ((fsp + 3856#64) ↦₆₄ c_dec.c2.w12) ∗
          ((fsp + 3864#64) ↦₆₄ c_dec.c2.w13) ∗
          statesRecvRoPlacedAt ∗
          Rest) ∧
        epilogueRegsEqSplit928 sf d ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  intro d
  subst hsp hx19
  dsimp only [lsProg_332, statesRecvRoPlacedAt, Unchunked.unchunkedSendCt2PlacedRoAt,
    lsLogFilterAddr, BitVec.ofNat_eq_ofNat] at hpc ⊢
  dsimp only [epilogueStoreStackPart2At]
  rw [show (epilogueStackOfSplit928 d noneCap k.w200 k.w208).mid =
      mid376Bytes c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352_576 from rfl,
      ← mid376At_eq_pointsToBytes (s_in.sp + 576#64) c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352_576]
  dsimp only [d, mkSplit928Ct1Acknowledged, copyScratchStackAt, copyFullScratch,
    epilogueStoreStackPart1At, epilogueStackOfSplit928, epilogueRegsEqSplit928,
    EpilogueStoreStack.tail, mid376At, noneCap, Words16.toList, Words5.toList]
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx28]
  wp_steps
  wp_done

end LibsignalBinary.Proofs.SpqrV1.States.Recv

namespace CryptoVerification.SpqrV1.States.Recv

export LibsignalBinary.Proofs.SpqrV1.States.Recv (
  ct1Sampled_none_branch_no_ack_placed
  ct1Sampled_none_branch_ack_placed
  ct1Sampled_copy_none_no_ack_part1_placed
  ct1Sampled_copy_none_no_ack_part2_placed
  ct1Sampled_copy_none_ack_part1_placed
  ct1Sampled_copy_none_ack_part2a_placed
  ct1Sampled_copy_none_ack_part2b_placed
)

end CryptoVerification.SpqrV1.States.Recv
