/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchExt
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledExtPart2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledExtPart5
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart6
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart7
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart8
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart9
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Sampled` Arm (`AllocContractsX`, Part 9)

Lifts Path 5b (`outMsg = some decoded, recv_ek = .ok uc_ek, ack = false`) and the Path 5c tail
(`+11696 -> s0.x30`, `ack = true`) to `AllocContractsX`, `DeallocOkExt`, and `.inImage img`
at `statesRecvCalleeStackXExt` (`35936` B).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
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
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_4240_add_4144

private theorem ct1s9_stackAt_fsp_calleeExt_eq_X (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackXExt =
      memRegion (fsp - 35936#64) 16384 ∗ stackAt fsp statesRecvCalleeStackX :=
  ProofLib.stackAt_split_bottom fsp statesRecvCalleeStackX 16384 (by decide)

private theorem ct1s9_fsp_sub_35936 (sp : BitVec 64) :
    (sp - 4240#64) - 35936#64 = sp - 40176#64 := by bv_omega

private theorem ct1s9_stackAt_statesRecvCallee_eq_extHook (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 3168 ∗ stackAt fsp extHookStack :=
  ProofLib.stackAt_split_bottom fsp extHookStack 3168 (by decide)

private theorem ct1s9_memcpy_region_ok_at_statesRecv_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      ((withStack sessionMemcpyRegionSpec extHookStack).inImage img) :=
  hA.session_memcpy_region_ok_at statesRecvName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))

/-- Common `outMsg = some decoded` call step (`+11496 -> +11528`) under `.inImage img`
    at `statesRecvCalleeStackXExt` (`35936` B). -/
theorem ct1Sampled_some_to_11528_ax
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hrecv_ek : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentRecvEkName)
      ((growToCalleeExt unchunkedRecvEkStack
        (unchunkedCt1SentRecvEkSpec A F K)).inImage img))
    (s_in : State) (fsp : BitVec 64) (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (c_uc : Words16) (decoded : Bytes)
    (res : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))) (Rest : SepProp)
    (hres : uc.recv_ek K uc.epoch decoded = StatesResult.ofError res)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11496#64)
    (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp) (hx20 : s_in.readReg64 .x20 = uc.epoch)
    (hinv : ImgCallInv img s_in) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11528#64) s_in
      (optVecU8At A (fsp + 3832#64) (some decoded) ∗ wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a uc) (wordsBytes c_uc.toList) ∗
        memRegion (fsp + 976#64) 1776 ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackXExt ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          unchunkedCt1SentRecvEkResAt A (fsp + 1856#64) res ∗
          memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
          memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3832#64) 24 ∗
          A.pool ∗ stackAt fsp statesRecvCalleeStackXExt ∗ Rest) ∧
        sf.sp = fsp ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = uc.epoch ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧ sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧ sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  refine SepWP.seq_inImage hinv
    (SepWP.mono (ct1Sampled_recv_ek_decode_branch_some s_in fsp decoded _ hfsp_align hpc hrun hsp) ?_)
  intro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx28_1, hx29_1, htr1⟩ hinv1
  refine SepWP.weaken_pre hP1 ?_
  have hpre1 :
      vecU8 A (fsp + 3832#64) decoded ∗
        (wordsAt (fsp + 3696#64) c_uc.toList ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A a uc) (wordsBytes c_uc.toList) ∗
          memRegion (fsp + 976#64) 1776 ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackXExt ∗ Rest) ⊢
      memRegion (fsp + 1856#64) 128 ∗ unchunkedCt1SentAt A (fsp + 3696#64) uc ∗
        vecU8 A (fsp + 3832#64) decoded ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackXExt ∗
        (memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗ Rest) := by
    have huc := Relocatable.reconstruct_128 (fun a => unchunkedCt1SentAt A a uc) (fsp + 3696#64) c_uc
    rw [ProofLib.memRegion_split' (b := fsp + 976#64) (n := 880) (k := 896) (b' := fsp + 1856#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 128) (k := 768) (b' := fsp + 1984#64) rfl (by bv_omega) (by decide)]
    refine Entails.trans (Entails.of_eq (show _ =
      memRegion (fsp + 1856#64) 128 ∗
      (wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a uc) (wordsBytes c_uc.toList)) ∗
      vecU8 A (fsp + 3832#64) decoded ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackXExt ∗
      (memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_left huc)
  refine SepWP.weaken_pre hpre1 (SepWP.mono
    (ct1Sampled_call_recv_ek_ext hrecv_ek s1 fsp uc decoded res _
      hres hfsp_align hpc1 hrun1 hsp1 (hx20_1.trans hx20) hinv1) ?_)
  intro sf Pf _ _ ⟨hPf, hsp_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx28_f, hx29_f, htr_f⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f,
    hx19_f.trans hx19_1, hx20_f, hx21_f.trans hx21_1, hx22_f.trans hx22_1,
    hx23_f.trans hx23_1, hx24_f.trans hx24_1, hx28_f.trans hx28_1, hx29_f.trans hx29_1,
    htr_f.trans htr1⟩

private theorem ct1s9_copy_some_ack_part2a_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (s_in : State) (fsp w0 w8 w16 : BitVec 64)
    (bs352_976 : List (BitVec 8)) (c_1352 c_ca0 : Words5) (Rest : SepProp)
    (h976_len : bs352_976.length = 352) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 16596#64)
    (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp)
    (hx23 : s_in.readReg64 .x23 = 4#64) (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
    (hinv : ImgCallInv img s_in) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 16800#64) s_in
      (mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗ wordsAt (fsp + 1352#64) c_1352.toList ∗
        wordsAt (fsp + 3232#64) c_ca0.toList ∗ memRegion (fsp + 3272#64) 376 ∗
        stackAt fsp statesRecvCalleeStackX ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗ wordsAt (fsp + 1352#64) c_1352.toList ∗
          wordsAt (fsp + 3232#64) c_1352.toList ∗ mid376At (fsp + 3272#64) w0 w8 w16 bs352_976 ∗
          stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
        sf.sp = fsp ∧ sf.readReg64 .x8 = 3#64 ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x28 = fsp + 3272#64 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hmemcpy_raw := ct1s9_memcpy_region_ok_at_statesRecv_ext hA
  have hsplit := ct1s9_stackAt_statesRecvCallee_eq_extHook s_in.sp
  have _hmid376_len : (mid376Bytes w0 w8 w16 bs352_976).length = 376 :=
    mid376Bytes_length w0 w8 w16 h976_len
  rw [mid376At_eq_pointsToBytes (s_in.sp + 976#64) w0 w8 w16 bs352_976,
      mid376At_eq_pointsToBytes (s_in.sp + 3272#64) w0 w8 w16 bs352_976]
  states_recv_fetches_range img.base (Rust.withPanics ext) 16596 64
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat]
    at hpc hmemcpy_raw hsplit ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  rw [hsplit]
  dsimp only [Words5.toList]
  simp only [wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_call_inImage hmemcpy_raw hinv ⟨s_in.sp + 3272#64, s_in.sp + 976#64, mid376Bytes w0 w8 w16 bs352_976⟩
  wp_steps
  wp_done

/-! ## 1. Path 5b (`outMsg = some decoded, recv_ek = .ok uc_ek, ack = false`: `+11496 -> s0.x30`) -/

set_option maxHeartbeats 2400000 in
/-- Path 5b from `+11496 -> s0.x30` (`outMsg = some decoded`, `recv_ek = .ok uc_ek`, `ack = false`)
    under `AllocContractsX` + `DeallocOkExt` at `statesRecvCalleeStackXExt` (`35936` B). -/
theorem ct1Sampled_path_some_ok_no_ack_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hrecv_ek : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentRecvEkName)
      ((growToCalleeExt unchunkedRecvEkStack
        (unchunkedCt1SentRecvEkSpec A F K)).inImage img))
    (s0 s_in : State) (fsp selfA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (dec' : PolyDecoder) (c_uc : Words16) (decoded : Bytes)
    (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp) (hres : st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11496#64)
    (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp) (hx19 : s_in.readReg64 .x19 = outA)
    (hx20 : s_in.readReg64 .x20 = st.uc.epoch) (hx21 : s_in.readReg64 .x21 = fsp + 3856#64)
    (hx22 : s_in.readReg64 .x22 = 0#64) (hx23 : s_in.readReg64 .x23 = polyEncoderTagVal st.sending_ct1)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64) (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (htr : TraceCalleeSaved s_in s0) (hinv : ImgCallInv img s_in) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s_in
      (optVecU8At A (fsp + 3832#64) (some decoded) ∗ polyDecoderAt A (fsp + 2752#64) dec' ∗
        polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 1776 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗ statesRecvRoAt img.base ∗ A.pool ∗
        stackAt fsp statesRecvCalleeStackXExt ∗ statesRecvSavedCells s0 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekReceivedCt1Sampled { uc := uc_ek, sending_ct1 := st.sending_ct1 } }) ∗
          memRegion selfA chunkedStatesSize ∗ statesRecvRoAt img.base ∗ A.pool ∗
          stackAt s0.sp statesRecvStackXExt ∗ Rest) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let b := img.base
  have hpre0 :
      optVecU8At A (fsp + 3832#64) (some decoded) ∗ polyDecoderAt A (fsp + 2752#64) dec' ∗
        polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 1776 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗ A.pool ∗
        stackAt fsp statesRecvCalleeStackXExt ∗ statesRecvSavedCells s0 ∗ Rest ⊢
      optVecU8At A (fsp + 3832#64) (some decoded) ∗ wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (fsp + 976#64) 1776 ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackXExt ∗
        (polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
          wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
          copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
          ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗ wordsAt (fsp + 528#64) k.tail.toList ∗
          memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
          memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗ statesRecvSavedCells s0 ∗ Rest) :=
    Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre0 ?_
  refine SepWP.seq_inImage hinv
    (SepWP.mono
      (ct1Sampled_some_to_11528_ax hrecv_ek s_in fsp st.uc c_uc decoded (.ok uc_ek) _
        hres hfsp_align hpc hrun hsp hx20 hinv) ?_)
  intro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, hx19_1, _, hx21_1, hx22_1, hx23_1, _, hx28_1, hx29_1, htr1⟩ hinv1
  refine SepWP.weaken_pre hP1 ?_
  let RestE : SepProp := memRegion (fsp - 35936#64) 16384 ∗ Rest
  have hpre1 :
      unchunkedCt1SentRecvEkResAt A (fsp + 1856#64) (.ok uc_ek) ∗
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
        memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3832#64) 24 ∗
        A.pool ∗ stackAt fsp statesRecvCalleeStackXExt ∗
        (polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
          wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
          copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
          ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗
          ((fsp + 520#64) ↦₆₄ k.w208) ∗ wordsAt (fsp + 528#64) k.tail.toList ∗
          memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 3152#64) 544 ∗
          memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
          memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗ statesRecvSavedCells s0 ∗ Rest) ⊢
      ∃∗ c_ek : Words16,
        ⌜c_ek.w0.toNat < 2 ^ 63⌝ ∗
        wordsAt (fsp + 1856#64) c_ek.toList ∗ memRegion (fsp + 3856#64) 128 ∗
        copyScratchStackAt fsp sc ∗
        (relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (wordsBytes c_ek.toList) ∗
          polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
          wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
          epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
          ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
          memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
          memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
          memRegion (fsp + 3984#64) 160 ∗ memRegion outA v1RecvSize ∗
          statesRecvRoAt b ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
          statesRecvSavedCells s0 ∗ RestE) := by
    dsimp only [unchunkedCt1SentRecvEkResAt, RestE]
    rw [ct1s9_stackAt_fsp_calleeExt_eq_X fsp,
        ProofLib.memRegion_split' (b := fsp + 3856#64) (n := 128) (k := 160) (b' := fsp + 3984#64) rfl (by bv_omega) (by decide)]
    refine Entails.trans (sepConj_mono_left
      (unchunkedCt1SentEkReceivedAt_extract_words16 A (fsp + 1856#64) uc_ek)) ?_
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro c_ek
    exact Entails.sepExists_right c_ek (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre1 ?_
  apply ProofLib.SepWP.exists_left; intro c_ek
  wp_focus_pure; intro hw0_ek
  refine SepWP.seq_inImage hinv1
    (SepWP.mono (ct1Sampled_recv_ek_ok_copy_sc s1 fsp sc c_ek _ hw0_ek hfsp_align hpc1 hrun1 hsp1) ?_)
  intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx8_2, hx9_2, hx10_2, hx19_2, _, hx21_2, hx22_2, hx23_2, _, _, hx28_2, hx29_2, htr2⟩ hinv2
  refine SepWP.weaken_pre hP2 ?_
  refine SepWP.seq_inImage hinv2
    (SepWP.mono (ct1Sampled_ok_branch_no_ack_eq s2 _ hpc2 hrun2 (hx22_2.trans (hx22_1.trans hx22))) ?_)
  intro s3 P3 hpc3 hrun3 ⟨hP3, hs3⟩ hinv3
  refine SepWP.weaken_pre hP3 ?_
  have hsp3 : s3.sp = fsp := by rw [hs3]; exact hsp2
  have hx8_3 : s3.readReg64 .x8 = c_ek.w0 := by rw [hs3, State.readReg64_setPC, hx8_2]
  have hx9_3 : s3.readReg64 .x9 = c_ek.w2 := by rw [hs3, State.readReg64_setPC, hx9_2]
  have hx10_3 : s3.readReg64 .x10 = c_ek.w3 := by rw [hs3, State.readReg64_setPC, hx10_2]
  have hx19_3 : s3.readReg64 .x19 = outA := by rw [hs3, State.readReg64_setPC, hx19_2, hx19_1, hx19]
  have hx21_3 : s3.readReg64 .x21 = fsp + 3856#64 := by rw [hs3, State.readReg64_setPC, hx21_2, hx21_1, hx21]
  have hx23_3 : s3.readReg64 .x23 = polyEncoderTagVal st.sending_ct1 := by rw [hs3, State.readReg64_setPC, hx23_2, hx23_1, hx23]
  have hx28_3 : s3.readReg64 .x28 = fsp + 3272#64 := by rw [hs3, State.readReg64_setPC, hx28_2, hx28_1, hx28]
  have hx29_3 : s3.readReg64 .x29 = fsp + 4144#64 := by rw [hs3, State.readReg64_setPC, hx29_2, hx29_1, hx29]
  have htr3 : TraceCalleeSaved s3 s0 := by rw [hs3]; exact htr2.trans (htr1.trans htr)
  have hpre3 :
      wordsAt (fsp + 1856#64) c_ek.toList ∗ wordsAt (fsp + 3856#64) c_ek.toList ∗
        copyScratchStackAt fsp { sc with wb0 := c_ek.w1 } ∗
        (relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (wordsBytes c_ek.toList) ∗
          polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
          wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
          epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
          ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
          memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
          memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
          memRegion (fsp + 3984#64) 160 ∗ memRegion outA v1RecvSize ∗
          statesRecvRoAt b ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
          statesRecvSavedCells s0 ∗ RestE) ⊢
      ∃∗ c_enc : Words50, ∃∗ vecs_dec : List (List Pt),
      ∃∗ v576 : BitVec 64, ∃∗ v584 : BitVec 64, ∃∗ v592 : BitVec 64, ∃∗ bs352_576 : List (BitVec 8),
      ∃∗ v976 : BitVec 64, ∃∗ v984 : BitVec 64, ∃∗ v992 : BitVec 64, ∃∗ bs352_976 : List (BitVec 8),
      ∃∗ c_1352 : Words5, ∃∗ vc90 : BitVec 64, ∃∗ vc98 : BitVec 64, ∃∗ c_ca0 : Words5,
      ∃∗ v4096 : BitVec 64, ∃∗ v4104 : BitVec 64, ∃∗ v4112 : BitVec 64,
        ⌜c_enc.c0.w0 = polyEncoderTagVal st.sending_ct1⌝ ∗ ⌜vecs_dec.length = NUM_POLYS⌝ ∗
        ⌜bs352_576.length = 352⌝ ∗ ⌜bs352_976.length = 352⌝ ∗
        words50At selfA c_enc ∗ wordsAt (fsp + 3856#64) c_ek.toList ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
        vecPtListOf A (fsp + 2752#64) vecs_dec ∗ memRegion (fsp + 3136#64) 16 ∗
        copyScratchStackAt fsp { sc with wb0 := c_ek.w1 } ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 976#64) ↦₆₄ v976) ∗ ((fsp + 984#64) ↦₆₄ v984) ∗ ((fsp + 992#64) ↦₆₄ v992) ∗
        ((fsp + 3216#64) ↦₆₄ vc90) ∗ ((fsp + 3224#64) ↦₆₄ vc98) ∗
        ((fsp + 4096#64) ↦₆₄ v4096) ∗ ((fsp + 4104#64) ↦₆₄ v4104) ∗ ((fsp + 4112#64) ↦₆₄ v4112) ∗
        A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
        (((fsp + 1000#64) ↦ₛ bs352_976) ∗ wordsAt (fsp + 1352#64) c_1352.toList ∗
          wordsAt (fsp + 3232#64) c_ca0.toList ∗ memRegion (fsp + 3272#64) 376 ∗
          ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗ mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
          statesRecvRoAt b ∗
          (wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
            relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (wordsBytes c_ek.toList) ∗
            relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
            memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
            (memRegion (fsp + 1392#64) 1360 ∗ memRegion (fsp + 3152#64) 64 ∗
              memRegion (fsp + 3648#64) 48 ∗ memRegion (fsp + 3696#64) 128 ∗
              memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
              memRegion (fsp + 3984#64) 112 ∗ memRegion (fsp + 4120#64) 24) ∗
            memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗ RestE)) := by
    refine Entails.trans (Entails.of_eq (show _ =
      polyEncoderAt A selfA st.sending_ct1 ∗ polyDecoderAt A (fsp + 2752#64) dec' ∗
      (wordsAt (fsp + 1856#64) c_ek.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
        memRegion (fsp + 3984#64) 160) ∗
      (wordsAt (fsp + 3856#64) c_ek.toList ∗
        copyScratchStackAt fsp { sc with wb0 := c_ek.w1 } ∗
        relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (wordsBytes c_ek.toList) ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
        epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗ memRegion outA v1RecvSize ∗
        statesRecvRoAt b ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗ RestE) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono (polyEncoderAt_extract_words50 A selfA st.sending_ct1)
      (sepConj_mono (polyDecoderAt_entails_vecs_tail A (fsp + 2752#64) dec')
        (sepConj_mono_left (memRegion_some_ok_no_ack_split fsp c_ek)))) ?_
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v576; apply Entails.sepExists_elim; intro v584
    apply Entails.sepExists_elim; intro v592; apply Entails.sepExists_elim; intro bs352_576
    apply Entails.sepExists_elim; intro v976; apply Entails.sepExists_elim; intro v984
    apply Entails.sepExists_elim; intro v992; apply Entails.sepExists_elim; intro bs352_976
    apply Entails.sepExists_elim; intro c_1352; apply Entails.sepExists_elim; intro vc90
    apply Entails.sepExists_elim; intro vc98; apply Entails.sepExists_elim; intro c_ca0
    apply Entails.sepExists_elim; intro v4096; apply Entails.sepExists_elim; intro v4104
    apply Entails.sepExists_elim; intro v4112; apply Entails.sepExists_elim; intro vecs_dec
    apply Entails.sepExists_elim; intro c_enc
    refine Entails.sepExists_right c_enc (Entails.sepExists_right vecs_dec
      (Entails.sepExists_right v576 (Entails.sepExists_right v584
        (Entails.sepExists_right v592 (Entails.sepExists_right bs352_576
          (Entails.sepExists_right v976 (Entails.sepExists_right v984
            (Entails.sepExists_right v992 (Entails.sepExists_right bs352_976
              (Entails.sepExists_right c_1352 (Entails.sepExists_right vc90
                (Entails.sepExists_right vc98 (Entails.sepExists_right c_ca0
                  (Entails.sepExists_right v4096 (Entails.sepExists_right v4104
                    (Entails.sepExists_right v4112 ?_))))))))))))))))
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre3 ?_
  apply ProofLib.SepWP.exists_left; intro c_enc; apply ProofLib.SepWP.exists_left; intro vecs_dec
  apply ProofLib.SepWP.exists_left; intro v576; apply ProofLib.SepWP.exists_left; intro v584
  apply ProofLib.SepWP.exists_left; intro v592; apply ProofLib.SepWP.exists_left; intro bs352_576
  apply ProofLib.SepWP.exists_left; intro v976; apply ProofLib.SepWP.exists_left; intro v984
  apply ProofLib.SepWP.exists_left; intro v992; apply ProofLib.SepWP.exists_left; intro bs352_976
  apply ProofLib.SepWP.exists_left; intro c_1352; apply ProofLib.SepWP.exists_left; intro vc90
  apply ProofLib.SepWP.exists_left; intro vc98; apply ProofLib.SepWP.exists_left; intro c_ca0
  apply ProofLib.SepWP.exists_left; intro v4096; apply ProofLib.SepWP.exists_left; intro v4104
  apply ProofLib.SepWP.exists_left; intro v4112
  wp_focus_pure; intro hc_enc_tag; wp_focus_pure; intro hvecs_dec
  wp_focus_pure; intro hbs576; wp_focus_pure; intro hbs976
  refine SepWP.seq_inImage hinv3
    (SepWP.mono
      (ct1Sampled_copy_some_no_ack_part1 hdealloc s3 fsp selfA vecs_dec hvecs_dec
        c_enc c_ek bs352_576 k.tail sc k v976 v984 v992 vc90 vc98 v4096 v4104 v4112 _
        hfsp_align hpc3 hrun3 hsp3 hx8_3 hx9_3 hx10_3 hx21_3 (hx23_3.trans hc_enc_tag.symm) hx29_3) ?_)
  intro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, hx19_4, hx23_4, _, hx28_4, _, htr4⟩ hinv4
  let d := mkSplit928EkReceivedCt1Sampled c_enc c_ek bs352_576 k.tail
  have hP4' : P4 ⊢
      mid376At (fsp + 976#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_976 ∗
      wordsAt (fsp + 1352#64) c_1352.toList ∗ wordsAt (fsp + 3232#64) c_ca0.toList ∗
      memRegion (fsp + 3272#64) 376 ∗ stackAt fsp statesRecvCalleeStackX ∗
      (memRegion (fsp + 3856#64) 128 ∗ copyScratchStackAt fsp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d selfA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
        ((fsp + 3216#64) ↦₆₄ c_ek.w10) ∗ ((fsp + 3224#64) ↦₆₄ c_ek.w11) ∗ statesRecvRoAt b ∗
        (words50At selfA c_enc ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          memRegion (selfA + 528#64) 400 ∗ memRegion (fsp + 2752#64) 400 ∗
          memRegion (fsp + 4096#64) 24 ∗ A.pool ∗
          relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (wordsBytes c_ek.toList) ∗
          relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
          (memRegion (fsp + 1392#64) 1360 ∗ memRegion (fsp + 3152#64) 64 ∗
            memRegion (fsp + 3648#64) 48 ∗ memRegion (fsp + 3696#64) 128 ∗
            memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
            memRegion (fsp + 3984#64) 112 ∗ memRegion (fsp + 4120#64) 24) ∗
          memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗ RestE)) := by
    refine Entails.trans hP4 ?_
    dsimp only [mid376At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hP4' ?_
  refine SepWP.seq_inImage hinv4
    (SepWP.mono
      (ct1Sampled_copy_some_no_ack_part2a_ext hA s4 fsp c_ek.w13 c_ek.w14 c_ek.w15
        bs352_976 c_1352 c_ca0 _ hbs976 hfsp_align hpc4 hrun4 hsp4 hx23_4 (hx28_4.trans hx28_3) hinv4) ?_)
  intro s5 P5 hpc5 hrun5 ⟨hP5, hsp5, hx8_5, hx19_5, hx28_5, _, htr5⟩ hinv5
  have hP5' : P5 ⊢
      ∃∗ vf10 : BitVec 64, ∃∗ vf18 : BitVec 64,
        copyScratchStackAt fsp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d selfA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
        mid376At (fsp + 976#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_976 ∗
        ((fsp + 3216#64) ↦₆₄ c_ek.w10) ∗ ((fsp + 3224#64) ↦₆₄ c_ek.w11) ∗
        mid376At (fsp + 3272#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_976 ∗
        ((fsp + 3856#64) ↦₆₄ vf10) ∗ ((fsp + 3864#64) ↦₆₄ vf18) ∗ statesRecvRoAt b ∗
        (wordsAt (fsp + 1352#64) c_1352.toList ∗ wordsAt (fsp + 3232#64) c_1352.toList ∗
          words50At selfA c_enc ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          memRegion (selfA + 528#64) 400 ∗ memRegion (fsp + 2752#64) 400 ∗
          A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
          relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (wordsBytes c_ek.toList) ∗
          relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
          (memRegion (fsp + 1392#64) 1360 ∗ memRegion (fsp + 3152#64) 64 ∗
            memRegion (fsp + 3648#64) 48 ∗ memRegion (fsp + 3696#64) 128 ∗
            memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
            memRegion (fsp + 3872#64) 272) ∗
          memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗ RestE) := by
    refine Entails.trans hP5 ?_
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (memRegion_128_split_two_words (fsp + 3856#64)))))))) ?_
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro vf10; apply Entails.sepExists_elim; intro vf18
    refine Entails.sepExists_right vf10 (Entails.sepExists_right vf18 ?_)
    rw [memRegion_3872_split fsp]
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hP5' ?_
  apply ProofLib.SepWP.exists_left; intro vf10; apply ProofLib.SepWP.exists_left; intro vf18
  refine SepWP.seq_inImage hinv5
    (SepWP.mono
      (ct1Sampled_copy_some_no_ack_part2b hb s5 fsp selfA outA c_enc c_ek bs352_976 bs352_576
        sc k v576 v584 v592 vf10 vf18 _ hfsp_align hpc5 hrun5 hsp5 hx8_5
        (hx19_5.trans (hx19_4.trans hx19_3)) hx28_5) ?_)
  intro s6 P6 hpc6 hrun6 ⟨hP6, hregs6, hsp6, hx19_6, _, htr6⟩ hinv6
  let k' := epilogueStackOfSplit928 d noneCap k.w200 k.w208
  have hmid' : k'.mid.length = 376 := by
    dsimp only [k', epilogueStackOfSplit928, d]
    exact mkSplit928EkReceivedCt1Sampled_mid_length c_enc c_ek k.tail hbs576
  have hP6' : P6 ⊢
      epilogueStoreStackPart1At fsp k' ∗ epilogueStoreStackPart2At fsp k' ∗
      memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 3168 ∗ memRegion selfA chunkedStatesSize ∗
        relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (wordsBytes c_ek.toList) ∗
        relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
        statesRecvRoAt b ∗ A.pool ∗ statesRecvSavedCells s0 ∗ RestE) := by
    refine Entails.trans ?_ (Entails.of_eq (show
      epilogueStoreStackPart1At fsp k' ∗ epilogueStoreStackPart2At fsp k' ∗
      memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 3168 ∗ memRegion selfA chunkedStatesSize ∗
        relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (wordsBytes c_ek.toList) ∗
        relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
        statesRecvRoAt b ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗ RestE) = _ by ac_rfl))
    refine Entails.trans hP6 ?_
    simp only [memRegion_out_960_split_states_key]
    have hself :
        words50At selfA c_enc ∗ wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ⊢
        memRegion selfA chunkedStatesSize :=
      Entails.trans (sepConj_mono_right (sepConj_mono_left (words16_entails_memRegion_128 (selfA + 400#64) c_uc)))
        (words50_128_400_entails_memRegion_928 selfA c_enc)
    have hstk3168 := memRegion_none_ack_join fsp c_ek.w13 c_ek.w14 c_ek.w15
      c_ek.w10 c_ek.w11 c_ek.w10 c_ek.w11 hbs976 c_1352 c_1352
    refine Entails.trans (Entails.of_eq (show _ =
      epilogueStoreStackPart1At fsp k' ∗ epilogueStoreStackPart2At fsp k' ∗
      memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        (mid376At (fsp + 976#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_976 ∗
          wordsAt (fsp + 1352#64) c_1352.toList ∗ memRegion (fsp + 2752#64) 400 ∗
          ((fsp + 3216#64) ↦₆₄ c_ek.w10) ∗ ((fsp + 3224#64) ↦₆₄ c_ek.w11) ∗
          wordsAt (fsp + 3232#64) c_1352.toList ∗
          mid376At (fsp + 3272#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_976 ∗
          ((fsp + 3856#64) ↦₆₄ c_ek.w10) ∗ ((fsp + 3864#64) ↦₆₄ c_ek.w11) ∗
          (memRegion (fsp + 1392#64) 1360 ∗ memRegion (fsp + 3152#64) 64 ∗
            memRegion (fsp + 3648#64) 48 ∗ memRegion (fsp + 3696#64) 128 ∗
            memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
            memRegion (fsp + 3872#64) 272)) ∗
        (words50At selfA c_enc ∗ wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400) ∗
        relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (wordsBytes c_ek.toList) ∗
        relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
        statesRecvRoAt b ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗ RestE) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hstk3168 (sepConj_mono_left hself))))))))
  refine SepWP.weaken_pre hP6' ?_
  refine SepWP.seq
    (ct1Sampled_epilogue_store_ext hA s6 fsp outA k' _ hmid' hfsp_align hpc6 hrun6 hsp6 hx19_6 hinv6) ?_
  intro s7 P7 hpc7 hrun7 ⟨hP7, hsp7, htr7⟩
  have heq_split : epilogueSplit928 s6 k' = d :=
    epilogueSplit928_of_eq s6 d noneCap k.w200 k.w208 hregs6
  have hP7' : P7 ⊢
      stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0 ∗
      (resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekReceivedCt1Sampled { uc := uc_ek, sending_ct1 := st.sending_ct1 } }) ∗
        memRegion selfA chunkedStatesSize ∗ statesRecvRoAt b ∗ A.pool ∗ RestE) := by
    refine Entails.trans hP7 ?_
    simp only [heq_split]
    have hstk := copyScratch_and_epilogueStack_entails_memRegion_4144 fsp (copyFullScratch sc d) k' hmid'
    have hst_out := split928At_reconstruct_ekReceivedCt1Sampled (A := A) (F := F) outA st.sending_ct1 uc_ek
      c_enc c_ek bs352_576 k.tail hc_enc_tag hbs576
    have hkey := optEpochSecretAt_none_of_words4 A (outA + 928#64) (s6.readReg64 .x20) k.w200 k.w208
    dsimp only [resultV1RecvAt, v1RecvAt, k', epilogueStackOfSplit928] at hstk hkey ⊢
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hkey
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt fsp statesRecvCalleeStackX ∗
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
        epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168) ∗
      statesRecvSavedCells s0 ∗
      (((split928At outA d ∗
          relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
          relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (wordsBytes c_ek.toList)) ∗
        (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ s6.readReg64 .x20) ∗
          ((outA + 944#64) ↦₆₄ k.w200) ∗ ((outA + 952#64) ↦₆₄ k.w208))) ∗
        memRegion selfA chunkedStatesSize ∗ statesRecvRoAt b ∗ A.pool ∗ RestE) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono hstk
      (sepConj_mono_right (sepConj_mono_left (sepConj_mono hst_out hkey))))
  subst hfsp
  refine SepWP.weaken_pre hP7' ?_
  refine SepWP.mono
    (ct1Sampled_epilogue_19324 s0 s7 _ hsp0_align hpc7 hrun7 hsp7
      (htr7.trans (htr6.trans (htr5.trans (htr4.trans htr3))))) ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
  dsimp only [RestE, b]
  rw [ct1s9_fsp_sub_35936 s0.sp, stackAt_statesRecvStackXExt_eq_X s0.sp]
  exact Entails.of_eq (by ac_rfl)

/-! ## 2. Path 5c Tail (`outMsg = some decoded, recv_ek = .ok uc_ek, ack = true`: `+11696 -> s0.x30`) -/

set_option maxHeartbeats 2400000 in
private theorem ct1Sampled_some_ok_ack_from_11696_core
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64) (hA : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext) (s0 s_in : State) (fsp selfA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) (dec' : PolyDecoder) (c_uc : Words16)
    (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) (outEnc : PolyEncoder)
    (g_uc : AuthWords) (ct2Cap ct2Ptr macCap macPtr : BitVec 64)
    (sc1 : CopyScratchStack) (k : EpilogueStoreStack) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11696#64)
    (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA) (hx20 : s_in.readReg64 .x20 = macCap)
    (hx25 : s_in.readReg64 .x25 = ct2Cap) (hx26 : s_in.readReg64 .x26 = ct2Ptr)
    (hx27 : s_in.readReg64 .x27 = macPtr) (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (htr : TraceCalleeSaved s_in s0) (hinv : ImgCallInv img s_in) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s_in
      ((polyEncoderAt A (fsp + 1856#64) outEnc ∗
        wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
        relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
          (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
        vecCapPtrDealloc A ct2Cap ct2Ptr ∗ vecCapPtrDealloc A macCap macPtr ∗
        memRegion (fsp + 3856#64) 128 ∗ memRegion (fsp + 3992#64) 104 ∗
        unchunkedSendCt2RoAt img.base ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX) ∗
        (polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
          wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
          copyScratchStackAt fsp sc1 ∗ epilogueStoreStackPart1At fsp k ∗
          ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2312#64) 440 ∗
          memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
          memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
          memRegion (fsp + 3984#64) 8 ∗ memRegion (fsp + 4096#64) 48 ∗
          memRegion outA v1RecvSize ∗
          (statesRecvJumpTableAt img.base ∗ tokenInitAt img.base ∗ reduceTableAt img.base) ∗
          statesRecvSavedCells s0 ∗ Rest))
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct2Sampled { uc := outUc, sending_ct2 := outEnc } }) ∗
          memRegion selfA chunkedStatesSize ∗ statesRecvRoAt img.base ∗ A.pool ∗
          stackAt s0.sp statesRecvStackX ∗ Rest) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let b := img.base
  have hpre0 :
      (polyEncoderAt A (fsp + 1856#64) outEnc ∗
        wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
        relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
          (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
        vecCapPtrDealloc A ct2Cap ct2Ptr ∗ vecCapPtrDealloc A macCap macPtr ∗
        memRegion (fsp + 3856#64) 128 ∗ memRegion (fsp + 3992#64) 104 ∗
        unchunkedSendCt2RoAt b ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX) ∗
      (polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
        copyScratchStackAt fsp sc1 ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2312#64) 440 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
        memRegion (fsp + 3984#64) 8 ∗ memRegion (fsp + 4096#64) 48 ∗
        memRegion outA v1RecvSize ∗
        (statesRecvJumpTableAt b ∗ tokenInitAt b ∗ reduceTableAt b) ∗
        statesRecvSavedCells s0 ∗ Rest) ⊢
      ∃∗ c_enc : Words50,
        words50At (fsp + 1856#64) c_enc ∗
        wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
        copyScratchStackAt fsp sc1 ∗ epilogueStoreStackPart1At fsp k ∗
        (vecCapPtrDealloc A macCap macPtr ∗ vecCapPtrDealloc A ct2Cap ct2Ptr ∗
          A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
          polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
          wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
          ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2312#64) 440 ∗
          memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
          memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
          memRegion (fsp + 3856#64) 128 ∗ memRegion (fsp + 3984#64) 8 ∗
          memRegion (fsp + 3992#64) 104 ∗ memRegion (fsp + 4096#64) 48 ∗
          relocatedHeap (fun a => polyEncoderAt A a outEnc) c_enc.toBytes ∗
          relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
            (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
          memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗ statesRecvSavedCells s0 ∗ Rest) := by
    rw [statesRecvRoAt_eq_unchunkedSendCt2 b]
    refine Entails.trans (sepConj_mono_left (sepConj_mono_left
      (Relocatable.extract_400 (Relocatable.of_polyEncoderAt A outEnc) (fsp + 1856#64)))) ?_
    simp only [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro c_enc
    exact Entails.sepExists_right c_enc (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre0 ?_
  apply ProofLib.SepWP.exists_left; intro c_enc
  refine SepWP.seq_inImage hinv
    (SepWP.mono (ct1Sampled_copy_some_ack_stage s_in fsp selfA c_enc g_uc outUc.epoch sc1 k _
      hfsp_align hpc hrun hsp hx29) ?_)
  intro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, _, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, htr1⟩ hinv1
  let d0 := mkSplit928Ct2Sampled c_enc g_uc outUc.epoch 0#64 k.wf8 k.w3c0 k.w3c8 k.w100 k.mid k.tail
  have hP1' : P1 ⊢
      vecCapPtrDealloc A macCap macPtr ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
      (vecCapPtrDealloc A ct2Cap ct2Ptr ∗ words50At (fsp + 1856#64) c_enc ∗
        wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
        copyScratchStackAt fsp
          { (copyFullScratchCt2 sc1 d0) with
            c0 := { (copyFullScratchCt2 sc1 d0).c0 with w12 := sc1.c0.w12 }, w88 := sc1.w88 } ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d0 selfA k.w200 k.w208) with
            we0 := k.we0, w118 := k.w118, w1e0 := k.w1e0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2312#64) 440 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
        memRegion (fsp + 3856#64) 128 ∗ memRegion (fsp + 3984#64) 8 ∗
        memRegion (fsp + 3992#64) 104 ∗ memRegion (fsp + 4096#64) 48 ∗
        relocatedHeap (fun a => polyEncoderAt A a outEnc) c_enc.toBytes ∗
        relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
          (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
        memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗ statesRecvSavedCells s0 ∗ Rest) :=
    Entails.trans hP1 (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hP1' ?_
  refine SepWP.seq_inImage hinv1
    (SepWP.mono (ct1Sampled_dealloc_mac_12072 hdealloc s1 fsp macCap macPtr _
      hfsp_align hpc1 hrun1 hsp1 (hx1_1.trans hx20) (hx27_1.trans hx27)) ?_)
  intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, _, hx25_2, hx26_2, hx28_2, hx29_2, htr2⟩ hinv2
  have hP2' : P2 ⊢
      vecCapPtrDealloc A ct2Cap ct2Ptr ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
      (words50At (fsp + 1856#64) c_enc ∗
        wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
        copyScratchStackAt fsp
          { (copyFullScratchCt2 sc1 d0) with
            c0 := { (copyFullScratchCt2 sc1 d0).c0 with w12 := sc1.c0.w12 }, w88 := sc1.w88 } ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d0 selfA k.w200 k.w208) with
            we0 := k.we0, w118 := k.w118, w1e0 := k.w1e0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2312#64) 440 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
        memRegion (fsp + 3856#64) 128 ∗ memRegion (fsp + 3984#64) 8 ∗
        memRegion (fsp + 3992#64) 104 ∗ memRegion (fsp + 4096#64) 48 ∗
        relocatedHeap (fun a => polyEncoderAt A a outEnc) c_enc.toBytes ∗
        relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
          (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
        memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗ statesRecvSavedCells s0 ∗ Rest) :=
    Entails.trans hP2 (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hP2' ?_
  refine SepWP.seq_inImage hinv2
    (SepWP.mono (ct1Sampled_dealloc_ct2_12088 hdealloc s2 fsp ct2Cap ct2Ptr _
      hfsp_align hpc2 hrun2 hsp2 (hx25_2.trans (hx25_1.trans hx25)) (hx26_2.trans (hx26_1.trans hx26))) ?_)
  intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, _, hx28_3, hx29_3, htr3⟩ hinv3
  have hP3' : P3 ⊢
      ∃∗ vecs_enc : List (List GF16), ∃∗ vecs_dec : List (List Pt),
      ∃∗ v576 : BitVec 64, ∃∗ v584 : BitVec 64, ∃∗ v592 : BitVec 64, ∃∗ bs352_576 : List (BitVec 8),
      ∃∗ v976 : BitVec 64, ∃∗ v984 : BitVec 64, ∃∗ v992 : BitVec 64, ∃∗ bs352_976 : List (BitVec 8),
      ∃∗ c_1352 : Words5, ∃∗ c_ca0 : Words5,
        ⌜vecs_enc.length = NUM_POLYS⌝ ∗ ⌜vecs_dec.length = NUM_POLYS⌝ ∗
        ⌜bs352_576.length = 352⌝ ∗ ⌜bs352_976.length = 352⌝ ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ vecGF16ListOf A (selfA + 8#64) vecs_enc ∗
        vecPtListOf A (fsp + 2752#64) vecs_dec ∗ memRegion (fsp + 3136#64) 16 ∗
        copyScratchStackAt fsp
          { (copyFullScratchCt2 sc1 d0) with
            c0 := { (copyFullScratchCt2 sc1 d0).c0 with w12 := sc1.c0.w12 }, w88 := sc1.w88 } ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d0 selfA k.w200 k.w208) with
            we0 := k.we0, w118 := k.w118, w1e0 := k.w1e0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
        (mid376At (fsp + 976#64) v976 v984 v992 bs352_976 ∗
          wordsAt (fsp + 1352#64) c_1352.toList ∗ wordsAt (fsp + 3232#64) c_ca0.toList ∗
          memRegion (fsp + 3272#64) 376 ∗
          ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗ mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
          statesRecvRoAt b ∗
          ((selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗
            memRegion (selfA + 392#64) 8 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
            memRegion (selfA + 528#64) 400 ∗ words50At (fsp + 1856#64) c_enc ∗
            wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
            relocatedHeap (fun a => polyEncoderAt A a outEnc) c_enc.toBytes ∗
            relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
              (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
            memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
            (memRegion (fsp + 1392#64) 464 ∗ memRegion (fsp + 2312#64) 440 ∗
              memRegion (fsp + 3152#64) 80 ∗ memRegion (fsp + 3648#64) 48 ∗
              memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3824#64) 8 ∗
              memRegion (fsp + 3832#64) 24 ∗ memRegion (fsp + 3856#64) 128 ∗
              memRegion (fsp + 3984#64) 8 ∗ memRegion (fsp + 3992#64) 104 ∗
              memRegion (fsp + 4096#64) 48) ∗
            memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗ Rest)) := by
    refine Entails.trans hP3 ?_
    rw [polyEncoderAt_eq_tag_body A selfA st.sending_ct1]
    refine Entails.trans (Entails.of_eq (show _ =
      polyEncoderBodyAt A (selfA + 8#64) st.sending_ct1 ∗
      polyDecoderAt A (fsp + 2752#64) dec' ∗
      (memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 3152#64) 544) ∗
      (((fsp + 232#64) ↦₆₄ selfA) ∗
        copyScratchStackAt fsp
          { (copyFullScratchCt2 sc1 d0) with
            c0 := { (copyFullScratchCt2 sc1 d0).c0 with w12 := sc1.c0.w12 }, w88 := sc1.w88 } ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d0 selfA k.w200 k.w208) with
            we0 := k.we0, w118 := k.w118, w1e0 := k.w1e0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ statesRecvRoAt b ∗
        (selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
        words50At (fsp + 1856#64) c_enc ∗
        wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
        relocatedHeap (fun a => polyEncoderAt A a outEnc) c_enc.toBytes ∗
        relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
          (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 2312#64) 440 ∗ memRegion (fsp + 3696#64) 128 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
        memRegion (fsp + 3856#64) 128 ∗ memRegion (fsp + 3984#64) 8 ∗
        memRegion (fsp + 3992#64) 104 ∗ memRegion (fsp + 4096#64) 48 ∗
        memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗ Rest) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono (polyEncoderBodyAt_entails_vecs_tail A selfA st.sending_ct1)
      (sepConj_mono (polyDecoderAt_entails_vecs_tail A (fsp + 2752#64) dec')
        (sepConj_mono_left (memRegion_some_ok_ack_split_976 fsp)))) ?_
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v576; apply Entails.sepExists_elim; intro v584
    apply Entails.sepExists_elim; intro v592; apply Entails.sepExists_elim; intro bs352_576
    apply Entails.sepExists_elim; intro v976; apply Entails.sepExists_elim; intro v984
    apply Entails.sepExists_elim; intro v992; apply Entails.sepExists_elim; intro bs352_976
    apply Entails.sepExists_elim; intro c_1352; apply Entails.sepExists_elim; intro c_ca0
    apply Entails.sepExists_elim; intro vecs_dec; apply Entails.sepExists_elim; intro vecs_enc
    refine Entails.sepExists_right vecs_enc (Entails.sepExists_right vecs_dec
      (Entails.sepExists_right v576 (Entails.sepExists_right v584
        (Entails.sepExists_right v592 (Entails.sepExists_right bs352_576
          (Entails.sepExists_right v976 (Entails.sepExists_right v984
            (Entails.sepExists_right v992 (Entails.sepExists_right bs352_976
              (Entails.sepExists_right c_1352 (Entails.sepExists_right c_ca0 ?_)))))))))))
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hP3' ?_
  apply ProofLib.SepWP.exists_left; intro vecs_enc; apply ProofLib.SepWP.exists_left; intro vecs_dec
  apply ProofLib.SepWP.exists_left; intro v576; apply ProofLib.SepWP.exists_left; intro v584
  apply ProofLib.SepWP.exists_left; intro v592; apply ProofLib.SepWP.exists_left; intro bs352_576
  apply ProofLib.SepWP.exists_left; intro v976; apply ProofLib.SepWP.exists_left; intro v984
  apply ProofLib.SepWP.exists_left; intro v992; apply ProofLib.SepWP.exists_left; intro bs352_976
  apply ProofLib.SepWP.exists_left; intro c_1352; apply ProofLib.SepWP.exists_left; intro c_ca0
  wp_focus_pure; intro hvecs_enc; wp_focus_pure; intro hvecs_dec
  wp_focus_pure; intro hbs576; wp_focus_pure; intro hbs976
  refine SepWP.seq_inImage hinv3
    (SepWP.mono
      (ct1Sampled_drop_and_finish_stage_12108 hdealloc s3 fsp selfA vecs_enc hvecs_enc
        vecs_dec hvecs_dec c_enc g_uc outUc.epoch sc1 k _
        hfsp_align hpc3 hrun3 hsp3
        (hx20_3.trans (hx20_2.trans hx20_1))
        (hx21_3.trans (hx21_2.trans hx21_1))
        (hx22_3.trans (hx22_2.trans hx22_1))
        (hx23_3.trans (hx23_2.trans hx23_1))) ?_)
  intro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, hx19_4, hx23_4, _, hx28_4, _, htr4⟩ hinv4
  have hP4' : P4 ⊢
      mid376At (fsp + 976#64) v976 v984 v992 bs352_976 ∗
      wordsAt (fsp + 1352#64) c_1352.toList ∗ wordsAt (fsp + 3232#64) c_ca0.toList ∗
      memRegion (fsp + 3272#64) 376 ∗ stackAt fsp statesRecvCalleeStackX ∗
      (copyScratchStackAt fsp (copyFullScratchCt2 sc1 d0) ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d0 selfA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
        statesRecvRoAt b ∗
        (memRegion (selfA + 8#64) 384 ∗ memRegion (fsp + 2752#64) 400 ∗ A.pool ∗
          (selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗
          memRegion (selfA + 392#64) 8 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          memRegion (selfA + 528#64) 400 ∗ words50At (fsp + 1856#64) c_enc ∗
          wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
          relocatedHeap (fun a => polyEncoderAt A a outEnc) c_enc.toBytes ∗
          relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
            (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
          (memRegion (fsp + 1392#64) 464 ∗ memRegion (fsp + 2312#64) 440 ∗
            memRegion (fsp + 3152#64) 80 ∗ memRegion (fsp + 3648#64) 48 ∗
            memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3824#64) 8 ∗
            memRegion (fsp + 3832#64) 24 ∗ memRegion (fsp + 3856#64) 128 ∗
            memRegion (fsp + 3984#64) 8 ∗ memRegion (fsp + 3992#64) 104 ∗
            memRegion (fsp + 4096#64) 48) ∗
          memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗ Rest)) :=
    Entails.trans hP4 (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hP4' ?_
  refine SepWP.seq_inImage hinv4
    (SepWP.mono
      (ct1s9_copy_some_ack_part2a_ext hA s4 fsp v976 v984 v992
        bs352_976 c_1352 c_ca0 _ hbs976 hfsp_align hpc4 hrun4 hsp4 hx23_4
        (hx28_4.trans (hx28_3.trans (hx28_2.trans (hx28_1.trans hx28)))) hinv4) ?_)
  intro s5 P5 hpc5 hrun5 ⟨hP5, hsp5, hx8_5, hx19_5, _, _, htr5⟩ hinv5
  let d := mkSplit928Ct2Sampled c_enc g_uc outUc.epoch (s5.readReg64 .x2) k.wf8 k.w3c0 k.w3c8 k.w100
    (mid376Bytes v576 v584 v592 bs352_576) k.tail
  have hP5' : P5 ⊢
      copyScratchStackAt fsp (copyFullScratchCt2 sc1 d) ∗
      epilogueStoreStackPart1At fsp
        { (epilogueStackOfSplit928 d selfA k.w200 k.w208) with
          we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
      ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
      wordsAt (fsp + 528#64) k.tail.toList ∗ mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
      statesRecvRoAt b ∗
      (mid376At (fsp + 976#64) v976 v984 v992 bs352_976 ∗
        wordsAt (fsp + 1352#64) c_1352.toList ∗ wordsAt (fsp + 3232#64) c_1352.toList ∗
        mid376At (fsp + 3272#64) v976 v984 v992 bs352_976 ∗
        memRegion (selfA + 8#64) 384 ∗ memRegion (fsp + 2752#64) 400 ∗
        A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
        (selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗
        memRegion (selfA + 392#64) 8 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        memRegion (selfA + 528#64) 400 ∗ words50At (fsp + 1856#64) c_enc ∗
        wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
        relocatedHeap (fun a => polyEncoderAt A a outEnc) c_enc.toBytes ∗
        relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
          (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        (memRegion (fsp + 1392#64) 464 ∗ memRegion (fsp + 2312#64) 440 ∗
          memRegion (fsp + 3152#64) 80 ∗ memRegion (fsp + 3648#64) 48 ∗
          memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3824#64) 8 ∗
          memRegion (fsp + 3832#64) 24 ∗ memRegion (fsp + 3856#64) 128 ∗
          memRegion (fsp + 3984#64) 8 ∗ memRegion (fsp + 3992#64) 104 ∗
          memRegion (fsp + 4096#64) 48) ∗
        memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗ Rest) :=
    Entails.trans hP5 (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hP5' ?_
  refine SepWP.seq_inImage hinv5
    (SepWP.mono
      (ct1Sampled_copy_some_ack_part2b hb s5 fsp selfA outA c_enc g_uc outUc.epoch
        v576 v584 v592 bs352_576 sc1 k _ hfsp_align hpc5 hrun5 hsp5 hx8_5
        (hx19_5.trans (hx19_4.trans (hx19_3.trans (hx19_2.trans (hx19_1.trans hx19)))))) ?_)
  intro s6 P6 hpc6 hrun6 ⟨hP6, hregs6, hsp6, hx19_6, _, htr6⟩ hinv6
  let k' := epilogueStackOfSplit928 d noneCap k.w200 k.w208
  have hmid' : k'.mid.length = 376 := by
    dsimp only [k', epilogueStackOfSplit928, d, mkSplit928Ct2Sampled]
    exact mid376Bytes_length v576 v584 v592 hbs576
  have hP6' : P6 ⊢
      epilogueStoreStackPart1At fsp k' ∗ epilogueStoreStackPart2At fsp k' ∗
      memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (copyScratchStackAt fsp (copyFullScratchCt2 sc1 d) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 3168 ∗ memRegion selfA chunkedStatesSize ∗
        relocatedHeap (fun a => polyEncoderAt A a outEnc) c_enc.toBytes ∗
        relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
          (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
        statesRecvRoAt b ∗ A.pool ∗ statesRecvSavedCells s0 ∗ Rest) := by
    refine Entails.trans ?_ (Entails.of_eq (show
      epilogueStoreStackPart1At fsp k' ∗ epilogueStoreStackPart2At fsp k' ∗
      memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
      (copyScratchStackAt fsp (copyFullScratchCt2 sc1 d) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 3168 ∗ memRegion selfA chunkedStatesSize ∗
        relocatedHeap (fun a => polyEncoderAt A a outEnc) c_enc.toBytes ∗
        relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
          (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
        statesRecvRoAt b ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗ Rest) = _ by ac_rfl))
    refine Entails.trans hP6 ?_
    simp only [memRegion_out_960_split_states_key]
    have hself :
        (selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ memRegion (selfA + 8#64) 384 ∗
          memRegion (selfA + 392#64) 8 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          memRegion (selfA + 528#64) 400 ⊢
        memRegion selfA chunkedStatesSize :=
      Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (words16_entails_memRegion_128 (selfA + 400#64) c_uc)))))
        (tag_384_8_128_400_entails_memRegion_928 selfA (polyEncoderTagVal st.sending_ct1))
    have hstk3168 := memRegion_some_ok_ack_join fsp v976 v984 v992 hbs976 c_1352 c_1352 c_enc g_uc outUc.epoch
    refine Entails.trans (Entails.of_eq (show _ =
      epilogueStoreStackPart1At fsp k' ∗ epilogueStoreStackPart2At fsp k' ∗
      memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
      (copyScratchStackAt fsp (copyFullScratchCt2 sc1 d) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        (mid376At (fsp + 976#64) v976 v984 v992 bs352_976 ∗
          wordsAt (fsp + 1352#64) c_1352.toList ∗ words50At (fsp + 1856#64) c_enc ∗
          wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
          memRegion (fsp + 2752#64) 400 ∗ wordsAt (fsp + 3232#64) c_1352.toList ∗
          mid376At (fsp + 3272#64) v976 v984 v992 bs352_976 ∗
          (memRegion (fsp + 1392#64) 464 ∗ memRegion (fsp + 2312#64) 440 ∗
            memRegion (fsp + 3152#64) 80 ∗ memRegion (fsp + 3648#64) 48 ∗
            memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3824#64) 8 ∗
            memRegion (fsp + 3832#64) 24 ∗ memRegion (fsp + 3856#64) 128 ∗
            memRegion (fsp + 3984#64) 8 ∗ memRegion (fsp + 3992#64) 104 ∗
            memRegion (fsp + 4096#64) 48)) ∗
        ((selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ memRegion (selfA + 8#64) 384 ∗
          memRegion (selfA + 392#64) 8 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          memRegion (selfA + 528#64) 400) ∗
        relocatedHeap (fun a => polyEncoderAt A a outEnc) c_enc.toBytes ∗
        relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
          (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
        statesRecvRoAt b ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hstk3168 (sepConj_mono_left hself))))))))
  refine SepWP.weaken_pre hP6' ?_
  refine SepWP.seq
    (ct1Sampled_epilogue_store_ext hA s6 fsp outA k' _ hmid' hfsp_align hpc6 hrun6 hsp6 hx19_6 hinv6) ?_
  intro s7 P7 hpc7 hrun7 ⟨hP7, hsp7, htr7⟩
  have heq_split : epilogueSplit928 s6 k' = d :=
    epilogueSplit928_of_eq s6 d noneCap k.w200 k.w208 hregs6
  have hP7' : P7 ⊢
      stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0 ∗
      (resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct2Sampled { uc := outUc, sending_ct2 := outEnc } }) ∗
        memRegion selfA chunkedStatesSize ∗ statesRecvRoAt b ∗ A.pool ∗ Rest) := by
    refine Entails.trans hP7 ?_
    simp only [heq_split]
    have hstk := copyScratch_and_epilogueStack_entails_memRegion_4144 fsp (copyFullScratchCt2 sc1 d) k' hmid'
    have hst_out := split928At_reconstruct_ct2Sampled A (F := F) outA outUc outEnc
      c_enc g_uc (s5.readReg64 .x2) k.wf8 k.w3c0 k.w3c8 k.w100
      k.tail (mid376Bytes_length v576 v584 v592 hbs576)
    have hkey := optEpochSecretAt_none_of_words4 A (outA + 928#64) (s6.readReg64 .x20) k.w200 k.w208
    dsimp only [resultV1RecvAt, v1RecvAt, k', epilogueStackOfSplit928] at hstk hkey ⊢
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hkey
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt fsp statesRecvCalleeStackX ∗
      (copyScratchStackAt fsp (copyFullScratchCt2 sc1 d) ∗
        epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
        epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168) ∗
      statesRecvSavedCells s0 ∗
      (((split928At outA d ∗
          relocatedHeap (fun a => polyEncoderAt A a outEnc) c_enc.toBytes ∗
          relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
            (wordsBytes (ct2SentWordsList g_uc outUc.epoch))) ∗
        (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ s6.readReg64 .x20) ∗
          ((outA + 944#64) ↦₆₄ k.w200) ∗ ((outA + 952#64) ↦₆₄ k.w208))) ∗
        memRegion selfA chunkedStatesSize ∗ statesRecvRoAt b ∗ A.pool ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono hstk
      (sepConj_mono_right (sepConj_mono_left (sepConj_mono hst_out hkey))))
  subst hfsp
  refine SepWP.weaken_pre hP7' ?_
  refine SepWP.mono
    (ct1Sampled_epilogue_19324 s0 s7 _ hsp0_align hpc7 hrun7 hsp7
      (htr7.trans (htr6.trans (htr5.trans (htr4.trans (htr3.trans (htr2.trans (htr1.trans htr)))))))) ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

/-- Tail of Path 5c from `+11696 -> s0.x30` (after `send_ct2_and_encode`) under `AllocContractsX`
    + `DeallocOkExt` at `statesRecvCalleeStackXExt` (`35936` B) / `statesRecvStackXExt` (`40176` B). -/
theorem ct1Sampled_some_ok_ack_from_11696_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64) (hA : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext) (s0 s_in : State) (fsp selfA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) (dec' : PolyDecoder) (c_uc : Words16)
    (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) (outEnc : PolyEncoder)
    (g_uc : AuthWords) (ct2Cap ct2Ptr macCap macPtr : BitVec 64)
    (sc1 : CopyScratchStack) (k : EpilogueStoreStack) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11696#64)
    (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA) (hx20 : s_in.readReg64 .x20 = macCap)
    (hx25 : s_in.readReg64 .x25 = ct2Cap) (hx26 : s_in.readReg64 .x26 = ct2Ptr)
    (hx27 : s_in.readReg64 .x27 = macPtr) (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (htr : TraceCalleeSaved s_in s0) (hinv : ImgCallInv img s_in) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s_in
      ((polyEncoderAt A (fsp + 1856#64) outEnc ∗
        wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
        relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
          (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
        vecCapPtrDealloc A ct2Cap ct2Ptr ∗ vecCapPtrDealloc A macCap macPtr ∗
        memRegion (fsp + 3856#64) 128 ∗ memRegion (fsp + 3992#64) 104 ∗
        unchunkedSendCt2RoAt img.base ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackXExt) ∗
        (polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
          wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
          copyScratchStackAt fsp sc1 ∗ epilogueStoreStackPart1At fsp k ∗
          ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2312#64) 440 ∗
          memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
          memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
          memRegion (fsp + 3984#64) 8 ∗ memRegion (fsp + 4096#64) 48 ∗
          memRegion outA v1RecvSize ∗
          (statesRecvJumpTableAt img.base ∗ tokenInitAt img.base ∗ reduceTableAt img.base) ∗
          statesRecvSavedCells s0 ∗ Rest))
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct2Sampled { uc := outUc, sending_ct2 := outEnc } }) ∗
          memRegion selfA chunkedStatesSize ∗ statesRecvRoAt img.base ∗ A.pool ∗
          stackAt s0.sp statesRecvStackXExt ∗ Rest) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine SepWP.weaken_pre ?_
    (SepWP.mono
      (ct1Sampled_some_ok_ack_from_11696_core hb hA hdealloc s0 s_in fsp selfA outA st dec' c_uc
        outUc outEnc g_uc ct2Cap ct2Ptr macCap macPtr sc1 k
        (memRegion (fsp - 35936#64) 16384 ∗ Rest)
        hfsp_align hsp0_align hfsp hpc hrun hsp
        hx19 hx20 hx25 hx26 hx27 hx28 hx29 htr hinv) ?_)
  · rw [ct1s9_stackAt_fsp_calleeExt_eq_X fsp]
    exact Entails.of_eq (by ac_rfl)
  · intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
    subst hfsp
    rw [ct1s9_fsp_sub_35936 s0.sp, stackAt_statesRecvStackXExt_eq_X s0.sp]
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.Recv
