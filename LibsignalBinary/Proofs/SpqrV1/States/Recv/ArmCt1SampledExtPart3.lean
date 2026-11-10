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
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Sampled` Arm (`AllocContractsX`, Part 3)

**Checked by Lean.** `AllocContractsX` and `AddChunkOkX` counterparts of the shared epilogue,
unchanged return paths (`msg.epoch < st.uc.epoch` and non-`ek`), `recv_ek_chunk` prefix copy,
and `PolyDecoder::add_chunk` + `decoded_message` call sequence.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalSpqrV1.PolyDecoder
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
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
  sp_sub_4240_add_2752 sp_sub_4240_add_3696 sp_sub_4240_add_3832
  sp_sub_4240_add_3840 sp_sub_4240_add_3848

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv")
  (ls_stub% "memcpy")

private theorem ct1s3_stackAt_statesRecvCallee_eq_extHook (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 3168 ∗ stackAt fsp extHookStack :=
  ProofLib.stackAt_split_bottom fsp extHookStack 3168 (by decide)

private theorem ct1s3_memcpy_region_ok_at_statesRecv_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      ((withStack sessionMemcpyRegionSpec extHookStack).inImage img) :=
  hA.session_memcpy_region_ok_at statesRecvName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))

local macro "ct1s3_steps_to_memcpy " entry:term:max hinv:ident hcall:ident : tactic =>
  `(tactic| (
    apply SepWP.seq_inImage
      (mid := $entry + bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")) $hinv
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm]) fun $hcall => ?_))

private theorem ct1s3_epilogue_store_part2_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (s_mid : State) (fsp outA v20 : BitVec 64)
    (k : EpilogueStoreStack) (tail_out : Words5) (v928 v936 v944 v952 : BitVec 64) (Rest : SepProp)
    (hmid : k.mid.length = 376) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_mid.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 19280#64)
    (hrun : s_mid.status = .Running) (hsp : s_mid.sp = fsp)
    (hx0 : s_mid.readReg64 .x0 = outA + 512#64) (hx1 : s_mid.readReg64 .x1 = fsp + 576#64)
    (hx2 : s_mid.readReg64 .x2 = 376#64) (hx19 : s_mid.readReg64 .x19 = outA)
    (hx20 : s_mid.readReg64 .x20 = v20) (hinv : ImgCallInv img s_mid) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 19324#64) s_mid
      (epilogueStoreStackPart2At fsp k ∗ memRegion (outA + 512#64) 376 ∗
        wordsAt (outA + 888#64) tail_out.toList ∗ ((outA + 928#64) ↦₆₄ v928) ∗
        ((outA + 936#64) ↦₆₄ v936) ∗ ((outA + 944#64) ↦₆₄ v944) ∗ ((outA + 952#64) ↦₆₄ v952) ∗
        stackAt fsp statesRecvCalleeStackX ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ epilogueStoreStackPart2At fsp k ∗ ((outA + 512#64) ↦ₛ k.mid) ∗
          wordsAt (outA + 888#64) [k.w210, k.w218, k.w220, k.w228, k.w230] ∗
          ((outA + 928#64) ↦₆₄ k.we8) ∗ ((outA + 936#64) ↦₆₄ v20) ∗
          ((outA + 944#64) ↦₆₄ k.w200) ∗ ((outA + 952#64) ↦₆₄ k.w208) ∗
          stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
        sf.sp = fsp ∧ TraceCalleeSaved sf s_mid) := by
  subst hsp hx19 hx20
  have hmemcpy_raw := ct1s3_memcpy_region_ok_at_statesRecv_ext hA
  have hsplit := ct1s3_stackAt_statesRecvCallee_eq_extHook s_mid.sp
  states_recv_fetches_range img.base (Rust.withPanics ext) 19280 44
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw hsplit ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches; rw [hsplit]
  dsimp only [epilogueStoreStackPart2At, Words5.toList]
  simp only [wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_call_inImage hmemcpy_raw hinv ⟨s_mid.readReg64 .x19 + 512#64, s_mid.sp + 576#64, k.mid⟩
  wp_steps; wp_done

private theorem ct1s3_epilogue_store_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (s_in : State) (fsp outA : BitVec 64)
    (k : EpilogueStoreStack) (Rest : SepProp)
    (hmid : k.mid.length = 376) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64)
    (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp) (hx19 : s_in.readReg64 .x19 = outA)
    (hinv : ImgCallInv img s_in) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 19324#64) s_in
      (epilogueStoreStackPart1At fsp k ∗ epilogueStoreStackPart2At fsp k ∗
        memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
        stackAt fsp statesRecvCalleeStackX ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ epilogueStoreStackPart1At fsp k ∗ epilogueStoreStackPart2At fsp k ∗
          split928At outA (epilogueSplit928 s_in k) ∗ ((outA + 928#64) ↦₆₄ k.we8) ∗
          ((outA + 936#64) ↦₆₄ (s_in.readReg64 .x20)) ∗ ((outA + 944#64) ↦₆₄ k.w200) ∗
          ((outA + 952#64) ↦₆₄ k.w208) ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
        sf.sp = fsp ∧ TraceCalleeSaved sf s_in) := by
  let Rest0 := stackAt fsp statesRecvCalleeStackX ∗ Rest
  have hpre :
      epilogueStoreStackPart1At fsp k ∗ epilogueStoreStackPart2At fsp k ∗
      memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗ Rest0 ⊢
      ∃∗ d_out : Split928, ∃∗ v928 : BitVec 64, ∃∗ v936 : BitVec 64,
      ∃∗ v944 : BitVec 64, ∃∗ v952 : BitVec 64,
        epilogueStoreStackPart1At fsp k ∗ wordsAt outA d_out.c0.toList ∗
        wordsAt (outA + 128#64) d_out.c1.toList ∗ wordsAt (outA + 256#64) d_out.c2.toList ∗
        wordsAt (outA + 384#64) d_out.c3.toList ∗
        (epilogueStoreStackPart2At fsp k ∗ memRegion (outA + 512#64) 376 ∗
          wordsAt (outA + 888#64) d_out.tail.toList ∗ ((outA + 928#64) ↦₆₄ v928) ∗
          ((outA + 936#64) ↦₆₄ v936) ∗ ((outA + 944#64) ↦₆₄ v944) ∗ ((outA + 952#64) ↦₆₄ v952) ∗
          Rest0) := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (memRegion_928_entails_split928 outA)
        (sepConj_mono_left (memRegion_32_entails_words4 (outA + 928#64)))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply Entails.sepExists_elim; intro v952; apply Entails.sepExists_elim; intro v944
    apply Entails.sepExists_elim; intro v936; apply Entails.sepExists_elim; intro v928
    apply Entails.sepExists_elim; intro d_out
    refine Entails.sepExists_right d_out (Entails.sepExists_right v928
      (Entails.sepExists_right v936 (Entails.sepExists_right v944 (Entails.sepExists_right v952 ?_))))
    rw [show epilogueStoreStackPart1At fsp k ∗ (epilogueStoreStackPart2At fsp k ∗
          ((⌜d_out.mid.length = 376⌝ ∗ split928At outA d_out) ∗
            ((((outA + 928#64) ↦₆₄ v928) ∗ ((outA + 936#64) ↦₆₄ v936) ∗
              ((outA + 944#64) ↦₆₄ v944) ∗ ((outA + 952#64) ↦₆₄ v952)) ∗ Rest0))) =
        ⌜d_out.mid.length = 376⌝ ∗ ((outA + 512#64) ↦ₛ d_out.mid) ∗
        (epilogueStoreStackPart1At fsp k ∗ wordsAt outA d_out.c0.toList ∗
          wordsAt (outA + 128#64) d_out.c1.toList ∗ wordsAt (outA + 256#64) d_out.c2.toList ∗
          wordsAt (outA + 384#64) d_out.c3.toList ∗
          (epilogueStoreStackPart2At fsp k ∗ wordsAt (outA + 888#64) d_out.tail.toList ∗
            ((outA + 928#64) ↦₆₄ v928) ∗ ((outA + 936#64) ↦₆₄ v936) ∗
            ((outA + 944#64) ↦₆₄ v944) ∗ ((outA + 952#64) ↦₆₄ v952) ∗ Rest0)) by
      dsimp only [split928At]; ac_rfl]
    apply Entails.pure_left; intro hd_mid
    refine Entails.trans (sepConj_mono_left
      (pointsToBytes_entails_memRegion_376 (outA + 512#64) d_out.mid hd_mid)) ?_
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro d_out; apply ProofLib.SepWP.exists_left; intro v928
  apply ProofLib.SepWP.exists_left; intro v936; apply ProofLib.SepWP.exists_left; intro v944
  apply ProofLib.SepWP.exists_left; intro v952
  refine SepWP.seq_inImage hinv
    (SepWP.mono (ct1Sampled_epilogue_store_part1 s_in fsp outA k
      d_out.c0 d_out.c1 d_out.c2 d_out.c3 _ hfsp_align hpc hrun hsp hx19) ?_)
  intro s_mid P_mid hpc_mid hrun_mid
    ⟨hP_mid, hsp_mid, hx0_mid, hx1_mid, hx2_mid, hx19_mid, hx20_mid, htr_mid⟩ hinv_mid
  have hP_mid' : P_mid ⊢
      epilogueStoreStackPart2At fsp k ∗ memRegion (outA + 512#64) 376 ∗
      wordsAt (outA + 888#64) d_out.tail.toList ∗ ((outA + 928#64) ↦₆₄ v928) ∗
      ((outA + 936#64) ↦₆₄ v936) ∗ ((outA + 944#64) ↦₆₄ v944) ∗ ((outA + 952#64) ↦₆₄ v952) ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (epilogueStoreStackPart1At fsp k ∗ wordsAt outA (epilogueSplit928 s_in k).c0.toList ∗
        wordsAt (outA + 128#64) (epilogueSplit928 s_in k).c1.toList ∗
        wordsAt (outA + 256#64) (epilogueSplit928 s_in k).c2.toList ∗
        wordsAt (outA + 384#64) (epilogueSplit928 s_in k).c3.toList ∗ Rest) :=
    Entails.trans hP_mid (Entails.of_eq (by dsimp only [Rest0]; ac_rfl))
  refine SepWP.weaken_pre hP_mid' ?_
  refine SepWP.mono (ct1s3_epilogue_store_part2_ext hA s_mid fsp outA (s_in.readReg64 .x20) k
    d_out.tail v928 v936 v944 v952 _ hmid hfsp_align hpc_mid hrun_mid
    hsp_mid hx0_mid hx1_mid hx2_mid hx19_mid hx20_mid hinv_mid) ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, htr_f⟩
  refine ⟨Entails.trans hPf ?_, hsp_f, htr_f.trans htr_mid⟩
  dsimp only [split928At, epilogueSplit928, Words5.toList]; exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1200000 in
private theorem ct1s3_copy_lt_ext
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
  have hmemcpy_raw := ct1s3_memcpy_region_ok_at_statesRecv_ext hA
  have hsplit := ct1s3_stackAt_statesRecvCallee_eq_extHook s_in.sp
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
  ct1s3_steps_to_memcpy entry hinv hinv_call
  wp_call_inImage hmemcpy_raw hinv_call ⟨s_in.sp + 576#64, s_in.readReg64 .x1 + 512#64, d.mid⟩
  wp_steps
  wp_done

set_option maxHeartbeats 1200000 in
private theorem ct1s3_copy_other_ext
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
  have hmemcpy_raw := ct1s3_memcpy_region_ok_at_statesRecv_ext hA
  have hsplit := ct1s3_stackAt_statesRecvCallee_eq_extHook s_in.sp
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
  ct1s3_steps_to_memcpy entry hinv hinv_call
  wp_call_inImage hmemcpy_raw hinv_call ⟨s_in.sp + 576#64, s_in.readReg64 .x1 + 512#64, d.mid⟩
  wp_steps
  wp_done

/-! ## 1. Shared Epilogue & Paths 2 / 3 (`+18996`, `+10500`, `+12144`) -/

set_option maxHeartbeats 800000 in
/-- Shared `+18996 -> s0.x30` epilogue under `AllocContractsX` at `statesRecvCalleeStackX`. -/
theorem ct1Sampled_store_and_epilogue_same_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (s0 s4 : State) (fsp stA outA w200 w208 : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (d : Split928) (sc' : CopyScratchStack) (Rest : SepProp)
    (htag : d.c0.w0 = polyEncoderTagVal st.sending_ct1) (hmid : d.mid.length = 376)
    (hregs4 : epilogueRegsEqSplit928 s4 d)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc4 : s4.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64)
    (hrun4 : s4.status = .Running) (hsp4 : s4.sp = fsp) (hx19_4 : s4.readReg64 .x19 = outA)
    (htr4 : TraceCalleeSaved s4 s0) (hinv4 : ImgCallInv img s4) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s4
      (split928At stA d ∗ copyScratchStackAt fsp sc' ∗
        epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap w200 w208) ∗
        epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap w200 w208) ∗
        (relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
          memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168 ∗
          stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗ Rest))
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled st }) ∗
          memRegion stA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX ∗ Rest) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let k' := epilogueStackOfSplit928 d noneCap w200 w208
  have hmid' : k'.mid.length = 376 := hmid
  have hP4' :
      split928At stA d ∗ copyScratchStackAt fsp sc' ∗
        epilogueStoreStackPart1At fsp k' ∗ epilogueStoreStackPart2At fsp k' ∗
        (relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
          memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168 ∗
          stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗ Rest) ⊢
      epilogueStoreStackPart1At fsp k' ∗ epilogueStoreStackPart2At fsp k' ∗
      memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (split928At stA d ∗ relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
        copyScratchStackAt fsp sc' ∗ memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 3168 ∗ statesRecvSavedCells s0 ∗ Rest) := Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hP4' ?_
  refine SepWP.seq (ct1s3_epilogue_store_ext hA s4 fsp outA k' _
    hmid' hfsp_align hpc4 hrun4 hsp4 hx19_4 hinv4) ?_
  intro s5 P5 hpc5 hrun5 ⟨hP5, hsp5, htr5⟩
  have heq_split : epilogueSplit928 s4 k' = d :=
    epilogueSplit928_of_eq s4 d noneCap w200 w208 hregs4
  have hP5' : P5 ⊢
      stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0 ∗
      (resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled st }) ∗
        memRegion stA chunkedStatesSize ∗ Rest) := by
    refine Entails.trans hP5 ?_; rw [heq_split]
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
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168) ∗
      statesRecvSavedCells s0 ∗
      (((split928At outA d ∗ relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes) ∗
        (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ s4.readReg64 .x20) ∗
          ((outA + 944#64) ↦₆₄ w200) ∗ ((outA + 952#64) ↦₆₄ w208))) ∗
        split928At stA d ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono hstk
      (sepConj_mono_right (sepConj_mono (sepConj_mono hst_out hkey) (sepConj_mono_left hst_in))))
  subst hfsp; refine SepWP.weaken_pre hP5' ?_
  refine SepWP.mono
    (ct1Sampled_epilogue_19324 s0 s5 _ hsp0_align hpc5 hrun5 hsp5 (htr5.trans htr4)) ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

theorem ct1Sampled_store_and_epilogue_same_extStack
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (s0 s4 : State) (fsp stA outA w200 w208 : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (d : Split928) (sc' : CopyScratchStack) (Rest : SepProp)
    (htag : d.c0.w0 = polyEncoderTagVal st.sending_ct1) (hmid : d.mid.length = 376)
    (hregs4 : epilogueRegsEqSplit928 s4 d)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc4 : s4.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64)
    (hrun4 : s4.status = .Running) (hsp4 : s4.sp = fsp) (hx19_4 : s4.readReg64 .x19 = outA)
    (htr4 : TraceCalleeSaved s4 s0) (hinv4 : ImgCallInv img s4) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s4
      (split928At stA d ∗ copyScratchStackAt fsp sc' ∗
        epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap w200 w208) ∗
        epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap w200 w208) ∗
        (relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
          memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168 ∗
          stackAt fsp statesRecvCalleeStackXExt ∗ statesRecvSavedCells s0 ∗ Rest))
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled st }) ∗
          memRegion stA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackXExt ∗ Rest) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  subst hfsp
  refine SepWP.weaken_pre ?_ (SepWP.mono
    (ct1Sampled_store_and_epilogue_same_ext hA s0 s4 (s0.sp - 4240#64) stA outA w200 w208 st d sc'
      (memRegion (s0.sp - 40176#64) 16384 ∗ Rest)
      htag hmid hregs4 hfsp_align hsp0_align rfl hpc4 hrun4 hsp4 hx19_4 htr4 hinv4) ?_)
  · rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]; exact Entails.of_eq (by ac_rfl)
  · intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
    rw [stackAt_statesRecvStackXExt_eq_X s0.sp]; exact Entails.of_eq (by ac_rfl)

/-- Complete Path 2 (`msg.epoch < st.uc.epoch`, `+10500 -> s0.x30`) under `AllocContractsX`. -/
theorem ct1Sampled_path_lt_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (s0 s3 : State) (fsp stA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc3 : s3.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 10500#64)
    (hrun3 : s3.status = .Running) (hsp3 : s3.sp = fsp) (hx1_3 : s3.readReg64 .x1 = stA)
    (hx12_3 : s3.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19_3 : s3.readReg64 .x19 = outA) (_hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64)
    (htr3 : TraceCalleeSaved s3 s0) (hinv3 : ImgCallInv img s3) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s3
      (((stA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ chunkedCt1SampledBodyAt A (stA + 8#64) st) ∗
        memRegion outA v1RecvSize ∗ memRegion fsp 4144 ∗
        stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled st }) ∗
          memRegion stA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX ∗ Rest) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine SepWP.weaken_pre (copy_pre_entails s0 fsp stA outA st Rest) ?_
  apply ProofLib.SepWP.exists_left; intro d; apply ProofLib.SepWP.exists_left; intro sc
  apply ProofLib.SepWP.exists_left; intro k
  wp_focus_pure; intro htag; wp_focus_pure; intro hmid
  have hord :
      split928At stA d ∗ copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ k.we8) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        (relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
          memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168 ∗
          stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗ Rest) ⊢
      split928At stA d ∗ copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ k.we8) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
          memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168 ∗
          statesRecvSavedCells s0 ∗ Rest) := Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hord ?_
  refine SepWP.seq_inImage hinv3 (SepWP.mono (ct1s3_copy_lt_ext hA s3 fsp stA outA d sc k _
    hmid hfsp_align hpc3 hrun3 hsp3 hx1_3 (hx12_3.trans htag.symm) hx19_3 hinv3) ?_)
  intro s4 P4 hpc4 hrun4 ⟨hP4, hregs4, hsp4, hx19_4, _, htr4⟩ hinv4
  exact SepWP.weaken_pre (Entails.trans hP4 (Entails.of_eq (by ac_rfl)))
    (ct1Sampled_store_and_epilogue_same_ext hA s0 s4 fsp stA outA k.w200 k.w208 st d
      (copyLtScratch sc d) Rest htag hmid hregs4 hfsp_align hsp0_align hfsp
      hpc4 hrun4 hsp4 hx19_4 (htr4.trans htr3) hinv4)

theorem ct1Sampled_path_lt_extStack
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (s0 s3 : State) (fsp stA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc3 : s3.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 10500#64)
    (hrun3 : s3.status = .Running) (hsp3 : s3.sp = fsp) (hx1_3 : s3.readReg64 .x1 = stA)
    (hx12_3 : s3.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19_3 : s3.readReg64 .x19 = outA) (hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64)
    (htr3 : TraceCalleeSaved s3 s0) (hinv3 : ImgCallInv img s3) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s3
      (((stA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ chunkedCt1SampledBodyAt A (stA + 8#64) st) ∗
        memRegion outA v1RecvSize ∗ memRegion fsp 4144 ∗
        stackAt fsp statesRecvCalleeStackXExt ∗ statesRecvSavedCells s0 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled st }) ∗
          memRegion stA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackXExt ∗ Rest) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  subst hfsp
  refine SepWP.weaken_pre ?_ (SepWP.mono
    (ct1Sampled_path_lt_ext hA s0 s3 (s0.sp - 4240#64) stA outA st
      (memRegion (s0.sp - 40176#64) 16384 ∗ Rest)
      hfsp_align hsp0_align rfl hpc3 hrun3 hsp3 hx1_3 hx12_3 hx19_3 hx29_3 htr3 hinv3) ?_)
  · rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]; exact Entails.of_eq (by ac_rfl)
  · intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
    rw [stackAt_statesRecvStackXExt_eq_X s0.sp]; exact Entails.of_eq (by ac_rfl)

/-- Complete Path 3 from `+12144` (`msg.epoch == st.uc.epoch` non-`ek`/`ekCt1Ack`) under `AllocContractsX`. -/
theorem ct1Sampled_path_other_from_12144_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (s0 s3 : State) (fsp stA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc3 : s3.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 12144#64)
    (hrun3 : s3.status = .Running) (hsp3 : s3.sp = fsp) (hx1_3 : s3.readReg64 .x1 = stA)
    (hx12_3 : s3.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19_3 : s3.readReg64 .x19 = outA) (_hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64)
    (htr3 : TraceCalleeSaved s3 s0) (hinv3 : ImgCallInv img s3) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s3
      (((stA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ chunkedCt1SampledBodyAt A (stA + 8#64) st) ∗
        memRegion outA v1RecvSize ∗ memRegion fsp 4144 ∗
        stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled st }) ∗
          memRegion stA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX ∗ Rest) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine SepWP.weaken_pre (copy_pre_entails s0 fsp stA outA st Rest) ?_
  apply ProofLib.SepWP.exists_left; intro d; apply ProofLib.SepWP.exists_left; intro sc
  apply ProofLib.SepWP.exists_left; intro k
  wp_focus_pure; intro htag; wp_focus_pure; intro hmid
  have hord :
      split928At stA d ∗ copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ k.we8) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        (relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
          memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168 ∗
          stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗ Rest) ⊢
      split928At stA d ∗ copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ k.we8) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
          memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168 ∗
          statesRecvSavedCells s0 ∗ Rest) := Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hord ?_
  refine SepWP.seq_inImage hinv3 (SepWP.mono (ct1s3_copy_other_ext hA s3 fsp stA outA d sc k _
    hmid hfsp_align hpc3 hrun3 hsp3 hx1_3 (hx12_3.trans htag.symm) hx19_3 hinv3) ?_)
  intro s4 P4 hpc4 hrun4 ⟨hP4, hregs4, hsp4, hx19_4, _, htr4⟩ hinv4
  exact SepWP.weaken_pre (Entails.trans hP4 (Entails.of_eq (by ac_rfl)))
    (ct1Sampled_store_and_epilogue_same_ext hA s0 s4 fsp stA outA k.w200 k.w208 st d
      (copyOtherScratch sc d) Rest htag hmid hregs4 hfsp_align hsp0_align hfsp
      hpc4 hrun4 hsp4 hx19_4 (htr4.trans htr3) hinv4)

theorem ct1Sampled_path_other_from_12144_extStack
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (s0 s3 : State) (fsp stA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc3 : s3.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 12144#64)
    (hrun3 : s3.status = .Running) (hsp3 : s3.sp = fsp) (hx1_3 : s3.readReg64 .x1 = stA)
    (hx12_3 : s3.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19_3 : s3.readReg64 .x19 = outA) (hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64)
    (htr3 : TraceCalleeSaved s3 s0) (hinv3 : ImgCallInv img s3) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s3
      (((stA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ chunkedCt1SampledBodyAt A (stA + 8#64) st) ∗
        memRegion outA v1RecvSize ∗ memRegion fsp 4144 ∗
        stackAt fsp statesRecvCalleeStackXExt ∗ statesRecvSavedCells s0 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled st }) ∗
          memRegion stA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackXExt ∗ Rest) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  subst hfsp
  refine SepWP.weaken_pre ?_ (SepWP.mono
    (ct1Sampled_path_other_from_12144_ext hA s0 s3 (s0.sp - 4240#64) stA outA st
      (memRegion (s0.sp - 40176#64) 16384 ∗ Rest)
      hfsp_align hsp0_align rfl hpc3 hrun3 hsp3 hx1_3 hx12_3 hx19_3 hx29_3 htr3 hinv3) ?_)
  · rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]; exact Entails.of_eq (by ac_rfl)
  · intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
    rw [stackAt_statesRecvStackXExt_eq_X s0.sp]; exact Entails.of_eq (by ac_rfl)

/-! ## 2. `recv_ek_chunk` Common Prefix Copy (`+11404 -> +11472`) & `add_chunk` + `decoded_message` (`+11472 -> +11496`) -/

set_option maxHeartbeats 1200000 in
/-- Copies `st.uc` (`128`B) to `fsp + 3696`, stores `stA` to `fsp + 232`, and `memcpy`s
    `st.receiving_ek` (`400`B) to `fsp + 2752` (`+11404 -> +11472`) under `AllocContractsX`. -/
theorem ct1Sampled_recv_ek_prefix_copy_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (s_in : State) (fsp stA ve8 : BitVec 64)
    (c_uc : Words16) (dec : PolyDecoder) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11404#64)
    (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp) (hx1 : s_in.readReg64 .x1 = stA)
    (hinv : ImgCallInv img s_in) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11472#64) s_in
      (wordsAt (stA + 400#64) c_uc.toList ∗ polyDecoderAt A (stA + 528#64) dec ∗
        ((fsp + 232#64) ↦₆₄ ve8) ∗ memRegion (fsp + 2752#64) 400 ∗ memRegion (fsp + 3696#64) 128 ∗
        stackAt fsp statesRecvCalleeStackX ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ wordsAt (stA + 400#64) c_uc.toList ∗ wordsAt (fsp + 3696#64) c_uc.toList ∗
          polyDecoderAt A (fsp + 2752#64) dec ∗ ((fsp + 232#64) ↦₆₄ stA) ∗
          memRegion (stA + 528#64) 400 ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
        sf.sp = fsp ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧ sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧ sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧ sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧ TraceCalleeSaved sf s_in) := by
  have hrel_dec : Relocatable 400 (fun a => polyDecoderAt A a dec) :=
    Relocatable.of_polyDecoderAt A dec
  have hpre :
      wordsAt (stA + 400#64) c_uc.toList ∗ polyDecoderAt A (stA + 528#64) dec ∗
        ((fsp + 232#64) ↦₆₄ ve8) ∗ memRegion (fsp + 2752#64) 400 ∗ memRegion (fsp + 3696#64) 128 ∗
        stackAt fsp statesRecvCalleeStackX ∗ Rest ⊢
      ∃∗ c_dst : Words16, ∃∗ bs_dec : List (BitVec 8),
        ⌜bs_dec.length = 400⌝ ∗ wordsAt (stA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_dst.toList ∗ ((fsp + 232#64) ↦₆₄ ve8) ∗
        ((stA + 528#64) ↦ₛ bs_dec) ∗ memRegion (fsp + 2752#64) 400 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (relocatedHeap (fun a => polyDecoderAt A a dec) bs_dec ∗ Rest) := by
    refine Entails.trans (sepConj_mono_right
      (sepConj_mono (hrel_dec (stA + 528#64)) (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (memRegion_128_entails_words16 (fsp + 3696#64))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro c_dst; apply Entails.sepExists_elim; intro bs_dec
    exact Entails.sepExists_right c_dst (Entails.sepExists_right bs_dec (Entails.of_eq (by ac_rfl)))
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro c_dst; apply ProofLib.SepWP.exists_left; intro bs_dec
  wp_focus_pure; intro hlen_dec; subst hsp hx1
  have hmemcpy_raw := ct1s3_memcpy_region_ok_at_statesRecv_ext hA
  have hsplit := ct1s3_stackAt_statesRecvCallee_eq_extHook s_in.sp
  refine SepWP.mono (post := fun sf Pf =>
      (Pf ⊢ wordsAt (s_in.readReg64 .x1 + 400#64) c_uc.toList ∗
        wordsAt (s_in.sp + 3696#64) c_uc.toList ∗ ((s_in.sp + 2752#64) ↦ₛ bs_dec) ∗
        ((s_in.sp + 232#64) ↦₆₄ s_in.readReg64 .x1) ∗ ((s_in.readReg64 .x1 + 528#64) ↦ₛ bs_dec) ∗
        stackAt s_in.sp statesRecvCalleeStackX ∗
        (relocatedHeap (fun a => polyDecoderAt A a dec) bs_dec ∗ Rest)) ∧
      sf.sp = s_in.sp ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
      sf.readReg64 .x20 = s_in.readReg64 .x20 ∧ sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
      sf.readReg64 .x22 = s_in.readReg64 .x22 ∧ sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
      sf.readReg64 .x24 = s_in.readReg64 .x24 ∧ sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
      sf.readReg64 .x29 = s_in.readReg64 .x29 ∧ TraceCalleeSaved sf s_in)
    ?_ (fun sf Pf _ _ ⟨hPf, hrest⟩ => ⟨Entails.trans hPf ?_, hrest⟩)
  · states_recv_fetches_range img.base (Rust.withPanics ext) 11404 68
    dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat]
      at hpc hmemcpy_raw hsplit ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::recv" = entry
    examples_hide_fetches; rw [hsplit]; dsimp only [Words16.toList]
    simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd]
    ct1s3_steps_to_memcpy entry hinv hinv_call
    wp_call_inImage hmemcpy_raw hinv_call ⟨s_in.sp + 2752#64, s_in.readReg64 .x1 + 528#64, bs_dec⟩
    wp_done
  · have hdec := relocatedHeap_recompose (fun a => polyDecoderAt A a dec) bs_dec (s_in.sp + 2752#64)
    have hdec_in : ((s_in.readReg64 .x1 + 528#64) ↦ₛ bs_dec) ⊢
        memRegion (s_in.readReg64 .x1 + 528#64) 400 := by
      rw [← hlen_dec]; exact ProofLib.pointsToBytes_entails_memRegion _ _
    refine Entails.trans (Entails.of_eq (show _ =
      wordsAt (s_in.readReg64 .x1 + 400#64) c_uc.toList ∗
      wordsAt (s_in.sp + 3696#64) c_uc.toList ∗
      (((s_in.sp + 2752#64) ↦ₛ bs_dec) ∗ relocatedHeap (fun a => polyDecoderAt A a dec) bs_dec) ∗
      ((s_in.sp + 232#64) ↦₆₄ s_in.readReg64 .x1) ∗ ((s_in.readReg64 .x1 + 528#64) ↦ₛ bs_dec) ∗
      stackAt s_in.sp statesRecvCalleeStackX ∗ Rest by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hdec (sepConj_mono_right (sepConj_mono_left hdec_in))))

theorem ct1Sampled_recv_ek_prefix_copy_extStack
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (s0 s_in : State) (fsp stA ve8 : BitVec 64)
    (c_uc : Words16) (dec : PolyDecoder) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hfsp : fsp = s0.sp - 4240#64)
    (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11404#64)
    (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp) (hx1 : s_in.readReg64 .x1 = stA)
    (hinv : ImgCallInv img s_in) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11472#64) s_in
      (wordsAt (stA + 400#64) c_uc.toList ∗ polyDecoderAt A (stA + 528#64) dec ∗
        ((fsp + 232#64) ↦₆₄ ve8) ∗ memRegion (fsp + 2752#64) 400 ∗ memRegion (fsp + 3696#64) 128 ∗
        stackAt fsp statesRecvCalleeStackXExt ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ wordsAt (stA + 400#64) c_uc.toList ∗ wordsAt (fsp + 3696#64) c_uc.toList ∗
          polyDecoderAt A (fsp + 2752#64) dec ∗ ((fsp + 232#64) ↦₆₄ stA) ∗
          memRegion (stA + 528#64) 400 ∗ stackAt fsp statesRecvCalleeStackXExt ∗ Rest) ∧
        sf.sp = fsp ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧ sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧ sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧ sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧ TraceCalleeSaved sf s_in) := by
  subst hfsp
  refine SepWP.weaken_pre ?_ (SepWP.mono
    (ct1Sampled_recv_ek_prefix_copy_ext hA s_in (s0.sp - 4240#64) stA ve8 c_uc dec
      (memRegion (s0.sp - 40176#64) 16384 ∗ Rest) hfsp_align hpc hrun hsp hx1 hinv) ?_)
  · rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]; exact Entails.of_eq (by ac_rfl)
  · intro sf Pf _ _ ⟨hPf, hrest⟩
    refine ⟨Entails.trans hPf ?_, hrest⟩
    rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]; exact Entails.of_eq (by ac_rfl)

/-- Stack-grown callee spec (`35936` B = `statesRecvCalleeStackXExt`), definitionally equal (`rfl`)
    to `ct1sGrowToCalleeExt` (`ArmCt1SampledExtDefs`) and `DispatchExt.Spec.growToCalleeExt`. -/
def ct1s3GrowToCalleeExt {α : Type} (oldStack : Nat) (spec : Spec α) : Spec α where
  pre := fun x s =>
    spec.pre x s ∗
      memRegion (s.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
        (statesRecvCalleeStackXExt - oldStack)
  post := fun x s0 sf =>
    spec.post x s0 sf ∗
      memRegion (s0.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
        (statesRecvCalleeStackXExt - oldStack)
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom := spec.onOom

private theorem ct1s3_addChunk_addr_ok {α : Type} {b : BitVec 64}
    {ext : String → Option (State → State)} {spec : Spec α}
    (h : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr addChunkName) spec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 94156#64) spec := by
  refine CryptoVerification.SpqrV1.Drop.sub_ok_of_addr_eq ?_ h
  dsimp only [tripleRatchetProgAtExt, statesRecvName, addChunkName]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv",
      ls_lemma% fnOff "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk"]
  bv_omega

private theorem ct1s3_polyDecodedMsg_addr_ok {α : Type} {b : BitVec 64}
    {ext : String → Option (State → State)} {spec : Spec α}
    (h : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr polyDecoderDecodedMessageName) spec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 91948#64) spec := by
  refine CryptoVerification.SpqrV1.Drop.sub_ok_of_addr_eq ?_ h
  dsimp only [tripleRatchetProgAtExt, statesRecvName, polyDecoderDecodedMessageName]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv",
      ls_lemma% fnOff "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"]
  bv_omega

private theorem ct1s3_stackAt_statesRecvCalleeExt_eq_addChunkX (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackXExt =
      memRegion (fsp - 35936#64) 19456 ∗ stackAt fsp addChunkStackX :=
  ProofLib.stackAt_split_bottom fsp addChunkStackX 19456 (by decide)

private theorem ct1s3_stackAt_statesRecvCalleeExt_eq_ct1sGrow (fsp : BitVec 64) (oldStack : Nat)
    (hle : oldStack ≤ statesRecvCalleeStackXExt) :
    stackAt fsp statesRecvCalleeStackXExt =
      stackAt fsp oldStack ∗
        memRegion (fsp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
          (statesRecvCalleeStackXExt - oldStack) := by
  have h1 : oldStack + (statesRecvCalleeStackXExt - oldStack) = statesRecvCalleeStackXExt :=
    Nat.add_sub_of_le hle
  have h2 : oldStack + (statesRecvCalleeStackXExt - oldStack) ≤ 2 ^ 64 := by
    rw [h1]; decide
  have h := ProofLib.stackAt_split_bottom fsp oldStack (statesRecvCalleeStackXExt - oldStack) h2
  rw [h1] at h
  rw [h, sepConj_comm]

private theorem ct1s3_call_addChunkX_inImage_statesRecv {img : Obj.Image} {A : RustAlloc} {P_pan : Prop}
    {prog : Program} {entry ret_pc next_pc : BitVec 64}
    {s0 s : State}
    (hcall : subroutine_ok prog entry ((addChunkSpecX A).inImage img))
    (hinv : ImgCallInv img s)
    (decA chunkA : BitVec 64) (dec : PolyDecoder) (chunk : Chunk)
    (hsorted : PolyDecoderStrictSorted dec)
    {sp_call : BitVec 64} {P Frame R : SepProp}
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
      ImgCallInv img sf → PolyDecoderStrictSorted (addChunkTotal dec chunk) →
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
  refine SepWPp.call_inImage (spec := addChunkSpecX A) (x := ⟨decA, chunkA, dec, chunk⟩)
    (F := Frame) hcall hinv hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
    (h_no_oom := fun _ _ _ h => (not_satisfies_false_sepConj h).elim)
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
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hinv_sf hsorted'

private theorem ct1s3_call_decodedMessage_inImage_statesRecv {img : Obj.Image} {A : RustAlloc}
    {b : BitVec 64} {P_pan : Prop} {prog : Program} {entry ret_pc next_pc : BitVec 64}
    {s0 s : State}
    (hcall : subroutine_ok prog entry
      ((ct1s3GrowToCalleeExt polyDecoderDecodedMessageStack
        (polyDecoderDecodedMessageSpec A b)).inImage img))
    (hinv : ImgCallInv img s)
    (hb : b &&& 0xfff#64 = 0#64)
    (outA decA : BitVec 64) (dec : PolyDecoder) (outMsg : Option Bytes)
    (hsorted : PolyDecoderStrictSorted dec)
    (hdec : spqrPolyApi.decoded_message dec = .ok outMsg)
    {sp_call : BitVec 64} {P Frame R : SepProp}
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
      A.pool ∗ stackAt sp_call statesRecvCalleeStackXExt) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      ImgCallInv img sf →
      SepWP prog next_pc sf
        ((optVecU8At A outA outMsg ∗ polyDecoderAt A decA dec ∗
          tokenInitAt b ∗ reduceTableAt b ∗
          A.pool ∗ stackAt sp_call statesRecvCalleeStackXExt) ∗ Frame)
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
  refine SepWPp.call_inImage
    (spec := ct1s3GrowToCalleeExt polyDecoderDecodedMessageStack (polyDecoderDecodedMessageSpec A b))
    (x := ⟨outA, decA, dec, outMsg⟩) (F := Frame) hcall hinv
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => (not_satisfies_false_sepConj h).elim)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
    (h_no_oom := fun _ _ _ h => (not_satisfies_false_sepConj h).elim)
  · intro R' hm
    rw [hsplit, ct1s3_stackAt_statesRecvCalleeExt_eq_ct1sGrow sp_call polyDecoderDecodedMessageStack (by decide)] at hm
    dsimp only [ct1s3GrowToCalleeExt, polyDecoderDecodedMessageSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hb, hx8, hx0, hsorted, hdec⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩
  · dsimp only [ct1s3GrowToCalleeExt, polyDecoderDecodedMessageSpec] at hmem
    exact Satisfies.mono (sepConj_mono_left (onPanic_alloc_entails_statesRecv htrace.1)) hmem
  · dsimp only [ct1s3GrowToCalleeExt, polyDecoderDecodedMessageSpec]
    rw [hsp, sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP (mid := next_pc)
    refine SepWP.weaken_pre
      (Entails.of_eq (by
        rw [ct1s3_stackAt_statesRecvCalleeExt_eq_ct1sGrow sp_call polyDecoderDecodedMessageStack (by decide)]
        ac_rfl))
      (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
        ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hinv_sf)

set_option maxHeartbeats 1200000 in
/-- Calls `PolyDecoder::add_chunk` and `PolyDecoder::decoded_message` (`+11472 -> +11496`) under
    `AddChunkOkX` and `.inImage img` at `statesRecvCalleeStackXExt` (`35936` B). -/
theorem ct1Sampled_recv_ek_add_and_decode_ext
    {img : Obj.Image} {A : RustAlloc} {P_pan : Prop}
    {ext : String → Option (State → State)}
    (hadd_call : AddChunkOkX img A ext)
    (hdec_call : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderDecodedMessageName)
      ((ct1s3GrowToCalleeExt polyDecoderDecodedMessageStack
        (polyDecoderDecodedMessageSpec A img.base)).inImage img))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (s0 s_in : State) (fsp msgA : BitVec 64)
    (dec : PolyDecoder) (chunk : Chunk) (outMsg : Option Bytes)
    (hsorted : PolyDecoderStrictSorted dec)
    (hdec_msg : spqrPolyApi.decoded_message (addChunkTotal dec chunk) = .ok outMsg)
    (Rest R : SepProp)
    {post : State → SepProp → Prop}
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11472#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx24 : s_in.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s_in s0)
    (hinv : ImgCallInv img s_in)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11496#64 →
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
      ImgCallInv img sf →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11496#64) sf
        (optVecU8At A (fsp + 3832#64) outMsg ∗
          polyDecoderAt A (fsp + 2752#64) (addChunkTotal dec chunk) ∗
          chunkAt (msgA + 10#64) chunk ∗
          statesRecvRoAt img.base ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackXExt ∗
          Rest)
        (fun sm Pm =>
          SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)))) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 94156#64) s_in
      (memRegion (fsp + 3832#64) 24 ∗
        polyDecoderAt A (fsp + 2752#64) dec ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoAt img.base ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackXExt ∗
        Rest)
      (fun sm Pm =>
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) := by
  subst hsp hx24
  have hadd_raw := ct1s3_addChunk_addr_ok hadd_call
  have hdec_raw := ct1s3_polyDecodedMsg_addr_ok hdec_call
  have hsplit_add := ct1s3_stackAt_statesRecvCalleeExt_eq_addChunkX s_in.sp
  states_recv_fetches_range img.base (Rust.withPanics ext) 11472 24
  dsimp only [tripleRatchetProgAtExt, statesRecvName, statesRecvRoAt, BitVec.ofNat_eq_ofNat]
    at hpc hadd_raw hdec_raw hsplit_add hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  rw [hsplit_add]
  wp_steps
  refine ct1s3_call_addChunkX_inImage_statesRecv (P_pan := P_pan) hadd_raw
    (imgCallInv_of_mem_eq hinv (by simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm]))
    (s_in.sp + 2752#64) (s_in.readReg64 .x24 + 10#64) dec chunk hsorted
    (s0 := s0) (ret_pc := entry + 11484#64) (next_pc := entry + 91948#64) (sp_call := s_in.sp)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [arm64_norm]) hfsp_align
    (by simp only [arm64_norm]) (by simp only [TraceCalleeSaved, arm64_norm, htr.1, htr.2])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 hinv1 hsorted' => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, _, _, _, hx28_1, hfp_1, _⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx28_1 hfp_1
  refine SepWP.focus_weaken (Entails.of_eq hsplit_add.symm) (by sep_focus) ?_
  wp_steps
  refine ct1s3_call_decodedMessage_inImage_statesRecv (P_pan := P_pan) hdec_raw
    (imgCallInv_of_mem_eq hinv1 (by simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm]))
    hb (s_in.sp + 3832#64) (s_in.sp + 2752#64) (addChunkTotal dec chunk) outMsg hsorted' hdec_msg
    (s0 := s0) (ret_pc := entry + 11496#64) (next_pc := entry + 11496#64) (sp_call := s_in.sp)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [arm64_norm, hsp1]) hfsp_align
    (by simp only [arm64_norm]) (by simp only [TraceCalleeSaved, arm64_norm, htr1.1, htr1.2])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 hinv2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, _, _, _, hx28_2, hfp_2, _⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx28_1, hfp_1]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx28_2 hfp_2
  exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sf2 hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx28_2 hfp_2 htr2 hinv2 hsorted')

end CryptoVerification.SpqrV1.States.Recv
