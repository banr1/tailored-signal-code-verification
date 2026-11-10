/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart4
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Sampled` Arm (`AllocContractsX`, Part 5)

**Checked by Lean.** `AllocContractsX` / `.inImage img` counterparts of `<Ct1Sent>::recv_ek`
(`ct1Sampled_call_recv_ek_ext`, `+11508 -> +11528`) and Path 5b `memcpy` staging
(`ct1Sampled_copy_some_no_ack_part2a_ext`, `+16596 -> +16800`).
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

private def ct1s5GrowToCalleeExt {α : Type} (oldStack : Nat) (spec : Spec α) : Spec α where
  pre := fun x s =>
    spec.pre x s ∗
      memRegion (s.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
        (statesRecvCalleeStackXExt - oldStack)
  post := fun x s0 sf =>
    spec.post x s0 sf ∗
      memRegion (s0.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
        (statesRecvCalleeStackXExt - oldStack)
  onPanic := spec.onPanic

private theorem ct1s5_stackAt_statesRecvCalleeExt_eq_recvEk (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackXExt =
      stackAt fsp unchunkedRecvEkStack ∗
        memRegion (fsp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
          (statesRecvCalleeStackXExt - unchunkedRecvEkStack) := by
  have h1 : unchunkedRecvEkStack + (statesRecvCalleeStackXExt - unchunkedRecvEkStack) =
      statesRecvCalleeStackXExt := by decide
  have h2 : unchunkedRecvEkStack + (statesRecvCalleeStackXExt - unchunkedRecvEkStack) ≤ 2 ^ 64 := by
    rw [h1]; decide
  have h := ProofLib.stackAt_split_bottom fsp unchunkedRecvEkStack
    (statesRecvCalleeStackXExt - unchunkedRecvEkStack) h2
  rw [h1] at h
  rw [h, sepConj_comm]

private theorem ct1s5_unchunkedRecvEk_addr_ok {α : Type} {b : BitVec 64}
    {ext : String → Option (State → State)} {spec : Spec α}
    (h : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentRecvEkName) spec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 34412#64) spec := by
  refine CryptoVerification.SpqrV1.Drop.sub_ok_of_addr_eq ?_ h
  dsimp only [tripleRatchetProgAtExt, statesRecvName, unchunkedCt1SentRecvEkName]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv",
      ls_lemma% fnOff "<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek"]
  bv_omega

private theorem ct1s5_stackAt_statesRecvCallee_eq_extHook (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 3168 ∗ stackAt fsp extHookStack :=
  ProofLib.stackAt_split_bottom fsp extHookStack 3168 (by decide)

private theorem ct1s5_memcpy_region_ok_at_statesRecv_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      ((withStack sessionMemcpyRegionSpec extHookStack).inImage img) :=
  hA.session_memcpy_region_ok_at statesRecvName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))

section
set_option quotPrecheck false
local notation (priority := high) "ct1s5GrowToCalleeExt" =>
  fun {α : Type} (oldStack : Nat) (spec : Spec α) =>
    ({ pre := fun x s =>
         spec.pre x s ∗
           memRegion (s.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
             (statesRecvCalleeStackXExt - oldStack)
       post := fun x s0 sf =>
         spec.post x s0 sf ∗
           memRegion (s0.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
             (statesRecvCalleeStackXExt - oldStack)
       onPanic := spec.onPanic } : Spec α)

/-- Calls `<Unchunked.SendCt.Ct1Sent>::recv_ek` (`+11508 -> +11528`) under `.inImage img` at
    `statesRecvCalleeStackXExt` (`35936` B). -/
theorem ct1Sampled_call_recv_ek_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hrecv_ek : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentRecvEkName)
      ((ct1s5GrowToCalleeExt unchunkedRecvEkStack
        (unchunkedCt1SentRecvEkSpec A F K)).inImage img))
    (s_in : State) (fsp : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (decoded : Bytes)
    (res : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)))
    (Rest : SepProp)
    (hres : uc.recv_ek K uc.epoch decoded = StatesResult.ofError res)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11508#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx20 : s_in.readReg64 .x20 = uc.epoch)
    (hinv : ImgCallInv img s_in) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11528#64) s_in
      (memRegion (fsp + 1856#64) 128 ∗
        unchunkedCt1SentAt A (fsp + 3696#64) uc ∗
        vecU8 A (fsp + 3832#64) decoded ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackXExt ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          unchunkedCt1SentRecvEkResAt A (fsp + 1856#64) res ∗
          memRegion (fsp + 3696#64) 128 ∗
          memRegion (fsp + 3832#64) 24 ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackXExt ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = uc.epoch ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  change subroutine_ok _ _
    ((Recv.ct1s5GrowToCalleeExt unchunkedRecvEkStack
      (unchunkedCt1SentRecvEkSpec A F K)).inImage img) at hrecv_ek
  subst hsp
  have hcall := ct1s5_unchunkedRecvEk_addr_ok hrecv_ek
  have hsplit := ct1s5_stackAt_statesRecvCalleeExt_eq_recvEk s_in.sp
  states_recv_fetches_range img.base (Rust.withPanics ext) 11508 20
  dsimp only [tripleRatchetProgAtExt, statesRecvName, Recv.ct1s5GrowToCalleeExt,
    BitVec.ofNat_eq_ofNat] at hpc hcall hsplit ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  rw [hsplit, ← hx20]
  wp_steps
  wp_call_inImage hcall hinv
    ⟨s_in.sp + 1856#64, s_in.sp + 3696#64, s_in.sp + 3832#64, uc, decoded, res⟩
  wp_done

end

/-- Part 2a of Path 5b (`+16596 -> +16800`, `0x59528..0x59568`) under `AllocContractsX`. -/
theorem ct1Sampled_copy_some_no_ack_part2a_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (s_in : State) (fsp : BitVec 64)
    (w0 w8 w16 : BitVec 64) (bs352_976 : List (BitVec 8))
    (c_1352 c_ca0 : Words5)
    (Rest : SepProp)
    (h976_len : bs352_976.length = 352)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 16596#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx23 : s_in.readReg64 .x23 = 3#64)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
    (hinv : ImgCallInv img s_in) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 16800#64) s_in
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
        sf.readReg64 .x8 = 2#64 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x28 = fsp + 3272#64 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hmemcpy_raw := ct1s5_memcpy_region_ok_at_statesRecv_ext hA
  have hsplit := ct1s5_stackAt_statesRecvCallee_eq_extHook s_in.sp
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

end CryptoVerification.SpqrV1.States.Recv
