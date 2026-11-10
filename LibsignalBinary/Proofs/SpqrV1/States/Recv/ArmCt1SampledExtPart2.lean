/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Sampled` Arm (`AllocContractsX`, Part 2)

**Checked by Lean.** `AllocContractsX img A ext` counterparts of the `memcpy`-dependent epilogue
store (`ct1Sampled_epilogue_store_ext`) and state-copy blocks (`ct1Sampled_copy_{lt,other}_ext`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

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
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible]
  libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
  statesRecvSavedCells statesRecvJumpTableAt
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_4240_add_4144 sp_sub_4240_add_3856 sp_sub_4240_add_3272

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv")
  (ls_stub% "memcpy")

private theorem ct1s2_stackAt_statesRecvCallee_eq_extHook (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 3168 ∗ stackAt fsp extHookStack :=
  ProofLib.stackAt_split_bottom fsp extHookStack 3168 (by decide)

private theorem ct1s2_memcpy_region_ok_at_statesRecv_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      ((withStack sessionMemcpyRegionSpec extHookStack).inImage img) :=
  hA.session_memcpy_region_ok_at statesRecvName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))

local macro "ct1s2_steps_to_memcpy " entry:term:max hinv:ident hcall:ident : tactic =>
  `(tactic| (
    apply SepWP.seq_inImage
      (mid := $entry + bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")) $hinv
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm]) fun $hcall => ?_))

/-- Part 2 of shared `Ok` return store block (`+19280 -> +19324`, `0x59fa4 -> 0x59fd0`)
    under `AllocContractsX`. -/
theorem ct1Sampled_epilogue_store_part2_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (s_mid : State) (fsp outA v20 : BitVec 64)
    (k : EpilogueStoreStack)
    (tail_out : Words5) (v928 v936 v944 v952 : BitVec 64)
    (Rest : SepProp)
    (hmid : k.mid.length = 376)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_mid.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 19280#64)
    (hrun : s_mid.status = .Running)
    (hsp : s_mid.sp = fsp)
    (hx0 : s_mid.readReg64 .x0 = outA + 512#64)
    (hx1 : s_mid.readReg64 .x1 = fsp + 576#64)
    (hx2 : s_mid.readReg64 .x2 = 376#64)
    (hx19 : s_mid.readReg64 .x19 = outA)
    (hx20 : s_mid.readReg64 .x20 = v20)
    (hinv : ImgCallInv img s_mid) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 19324#64) s_mid
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
  have hmemcpy_raw := ct1s2_memcpy_region_ok_at_statesRecv_ext hA
  have hsplit := ct1s2_stackAt_statesRecvCallee_eq_extHook s_mid.sp
  states_recv_fetches_range img.base (Rust.withPanics ext) 19280 44
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat]
    at hpc hmemcpy_raw hsplit ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  rw [hsplit]
  dsimp only [epilogueStoreStackPart2At, Words5.toList]
  simp only [wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_call_inImage hmemcpy_raw hinv ⟨s_mid.readReg64 .x19 + 512#64, s_mid.sp + 576#64, k.mid⟩
  wp_steps
  wp_done

/-- Full shared `Ok` return store block (`+18996 -> +19324`, `0x59e88 -> 0x59fd0`)
    under `AllocContractsX`. -/
theorem ct1Sampled_epilogue_store_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (s_in : State) (fsp outA : BitVec 64)
    (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hmid : k.mid.length = 376)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hinv : ImgCallInv img s_in) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 19324#64) s_in
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
  let Rest0 := stackAt fsp statesRecvCalleeStackX ∗ Rest
  have hpre :
      epilogueStoreStackPart1At fsp k ∗
      epilogueStoreStackPart2At fsp k ∗
      memRegion outA chunkedStatesSize ∗
      memRegion (outA + 928#64) 32 ∗
      Rest0 ⊢
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
          Rest0) := by
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
            Rest0))) =
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
            Rest0)) by
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
  refine SepWP.seq_inImage hinv
    (SepWP.mono
      (ct1Sampled_epilogue_store_part1 s_in fsp outA k
        d_out.c0 d_out.c1 d_out.c2 d_out.c3 _ hfsp_align hpc hrun hsp hx19) ?_)
  intro s_mid P_mid hpc_mid hrun_mid
    ⟨hP_mid, hsp_mid, hx0_mid, hx1_mid, hx2_mid, hx19_mid, hx20_mid, htr_mid⟩ hinv_mid
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
    Entails.trans hP_mid (Entails.of_eq (by dsimp only [Rest0]; ac_rfl))
  refine SepWP.weaken_pre hP_mid' ?_
  refine SepWP.mono
    (ct1Sampled_epilogue_store_part2_ext hA s_mid fsp outA (s_in.readReg64 .x20) k
      d_out.tail v928 v936 v944 v952 _ hmid hfsp_align hpc_mid hrun_mid
      hsp_mid hx0_mid hx1_mid hx2_mid hx19_mid hx20_mid hinv_mid) ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, htr_f⟩
  refine ⟨?_, hsp_f, htr_f.trans htr_mid⟩
  refine Entails.trans hPf ?_
  dsimp only [split928At, epilogueSplit928, Words5.toList]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1200000 in
/-- Path 2 (`msg.epoch < st.uc.epoch`) state-copy block (`+10500 -> +18996`)
    under `AllocContractsX`. -/
theorem ct1Sampled_copy_lt_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (s_in : State) (fsp stA outA : BitVec 64)
    (d : Split928) (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hmid : d.mid.length = 376)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 10500#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = stA)
    (hx12 : s_in.readReg64 .x12 = d.c0.w0)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hinv : ImgCallInv img s_in) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64) s_in
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
  have hmemcpy_raw := ct1s2_memcpy_region_ok_at_statesRecv_ext hA
  have hsplit := ct1s2_stackAt_statesRecvCallee_eq_extHook s_in.sp
  states_recv_fetches_range img.base (Rust.withPanics ext) 10500 428
  states_recv_fetches_range img.base (Rust.withPanics ext) 12584 28
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat]
    at hpc hmemcpy_raw hsplit ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  rw [hsplit]
  dsimp only [split928At, copyScratchStackAt, epilogueStoreStackPart1At, epilogueStoreStackPart2At,
    copyLtScratch, epilogueStackOfSplit928, epilogueRegsEqSplit928, EpilogueStoreStack.tail,
    noneCap, Words16.toList, Words5.toList]
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd]
  ct1s2_steps_to_memcpy entry hinv hinv_call
  wp_call_inImage hmemcpy_raw hinv_call ⟨s_in.sp + 576#64, s_in.readReg64 .x1 + 512#64, d.mid⟩
  wp_steps
  wp_done

set_option maxHeartbeats 1200000 in
/-- Path 3 (`msg.epoch == st.uc.epoch`, non-`ek`/`ekCt1Ack`) state-copy block (`+12144 -> +18996`)
    under `AllocContractsX`. -/
theorem ct1Sampled_copy_other_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (s_in : State) (fsp stA outA : BitVec 64)
    (d : Split928) (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hmid : d.mid.length = 376)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 12144#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = stA)
    (hx12 : s_in.readReg64 .x12 = d.c0.w0)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hinv : ImgCallInv img s_in) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64) s_in
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
  have hmemcpy_raw := ct1s2_memcpy_region_ok_at_statesRecv_ext hA
  have hsplit := ct1s2_stackAt_statesRecvCallee_eq_extHook s_in.sp
  states_recv_fetches_range img.base (Rust.withPanics ext) 12144 468
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat]
    at hpc hmemcpy_raw hsplit ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  rw [hsplit]
  dsimp only [split928At, copyScratchStackAt, epilogueStoreStackPart1At, epilogueStoreStackPart2At,
    copyOtherScratch, epilogueStackOfSplit928, epilogueRegsEqSplit928, EpilogueStoreStack.tail,
    noneCap, Words16.toList, Words5.toList]
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd]
  ct1s2_steps_to_memcpy entry hinv hinv_call
  wp_call_inImage hmemcpy_raw hinv_call ⟨s_in.sp + 576#64, s_in.readReg64 .x1 + 512#64, d.mid⟩
  wp_steps
  wp_done

end CryptoVerification.SpqrV1.States.Recv
