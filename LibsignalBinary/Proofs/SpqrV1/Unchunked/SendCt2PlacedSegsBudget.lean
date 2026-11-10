/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsReserveBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<Ct1SentEkReceived>::send_ct2`: Relocatable Segments 2–5a

Composes `[LibsignalPlacement]` `RustCliAllocBudget`-threaded Segments 2–5a (`+136 → +836`)
and proves `UnchunkedSendCt2PreEnv` / `UnchunkedSendCt2PostEnv` composition lemmas.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegsBudget

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalHooks LibsignalPlacement blkPC_347 blkPl_347 lsLogFilterAddr lsmpl lsρ
)
open CryptoVerification.RustHeap (vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalSpqrV1 (
  Authenticator Bytes MlKem flipEndiannessOfEncapsulationStateBytes
  issue1275NeedsFlip mlkemEncaps2Spec spqrAuthApi
)
open CryptoVerification.SpqrV1.Alloc (
  spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym
)
open CryptoVerification.SpqrV1.States.Leaves (UnchunkedSendCt2Ghost)
open CryptoVerification.SpqrV1.Unchunked (
  sendCt2EsWorkAt spqrLibcruxHmacSym spqrMlkemEncaps2Sym spqrRustDeallocSym
  unchunkedSendCt2PlacedRoAt
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget (sliceConcat3Spec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (framelessMemcpyAcpSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (doReserveSpec)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux (
  SendCt2Reserve128Env UnchunkedSendCt2Env UnchunkedSendCt2PostEnv UnchunkedSendCt2PreEnv
  libcruxHmacSafeBudgetSpec sendCt2ConcatHmacEvents sendCt2FlipAllocEvents
  sendCt2PlacedPostQ sendCt2PlacedPostQp sendCt2Reserve128Events sendCt2Seg23Events
  sepWPp_rw_pre_eq subroutine_ok_libcruxHmacSafe_of_budget
)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsReserveBudget (
  send_ct2_reserve_ct1_placed_preEnv_wpp send_ct2_reserve_ct1_placed_wpp
)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudget (
  send_ct2_5d8_to_604_placed_wpp send_ct2_scan_to_628_placed_preEnv_wpp
  send_ct2_scan_to_628_placed_wpp
)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux (
  freeOnlyEvs_sendCt2MdDeallocEvents sendCt2MdDeallocEvents sendCt2Seg5aEvents
  send_ct2_628_to_690_placed_preEnv_wpp send_ct2_628_to_690_placed_wpp
)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidPlacedBudget (
  send_ct2_append_hmac_placed_preEnv_wpp send_ct2_append_hmac_placed_wpp
)

export CryptoVerification.SpqrV1.Unchunked (
  spqrRustDeallocSym
  spqrMlkemEncaps2Sym
  spqrLibcruxHmacSym
)

export LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudget (
  Ct1SentEkReceived
  sendCt2FlipAllocEvents
  sendCt2FlipDeallocEvents
  sendCt2Seg23Events
  sendCt2Reserve128Events
  SendCt2Reserve128Env
  sendCt2ConcatHmacEvents
  UnchunkedSendCt2PreEnv
  UnchunkedSendCt2PostEnv
  UnchunkedSendCt2Env
  unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv
  unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfEnv
  unchunkedCt1SentEkReceivedSendCt2PlacedSpec
  UnchunkedCt1SentEkReceivedSendCt2PlacedOk
  sendCt2PlacedPostQOfPostEnv
  sendCt2PlacedPostQOfEnv
  sendCt2PlacedPostQ
  sendCt2PlacedPostQp
  libcruxHmacSafeBudgetSpec
  subroutine_ok_libcruxHmacSafe_of_budget
  libcrux_hmac_safe_placed_ok
  mlkem_encaps2_vm_placed_ok
  swap_loop_placed_ok
  swap_loop_placed_pool_ok
  scan_loop_false_placed_ok
  scan_loop_false_placed_pool_ok
  scan_loop_true_placed_ok
  scan_loop_true_placed_pool_ok
  send_ct2_prologue_to_scan_placed
  send_ct2_prologue_to_scan_placed_pool
  send_ct2_5d8_to_604_placed_wpp
  send_ct2_scan_to_628_placed_wpp
  send_ct2_scan_to_628_placed_preEnv_wpp
  send_ct2_reserve_ct1_placed_wpp
  send_ct2_reserve_ct1_placed_preEnv_wpp
)

export LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux (
  sendCt2MdDeallocEvents
  sendCt2Seg5aEvents
  freeOnlyEvs_rustDeallocEvents
  freeOnlyEvs_sendCt2MdDeallocEvents
  freeOnlyEvs_sendCt2FlipDeallocEvents
  send_ct2_628_to_690_placed_wpp
  send_ct2_628_to_690_placed_preEnv_wpp
)

export LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidPlacedBudget (
  send_ct2_append_hmac_placed_wpp
  send_ct2_append_hmac_placed_preEnv_wpp
)

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrAuthApi

/-! ## `libcrux_hmac` Bridge and Envelope Composition Lemmas -/

/-- Budget-threaded counterpart of `SendCt2PlacedSegs.libcrux_hmac_safe_of_subroutine_ok`:
    lifts `libcruxHmacBudgetSpec` to panic-free `libcruxHmacSafeBudgetSpec` when
    `key.length < 2 ^ 32`, `data.length < 2 ^ 32`, and `FitsEvents` holds. -/
theorem libcrux_hmac_safe_of_subroutine_ok {prog : Program} {entry : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hraw : subroutine_ok prog entry (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok prog entry (libcruxHmacSafeBudgetSpec F M A lim) :=
  subroutine_ok_libcruxHmacSafe_of_budget hraw

/-- Any `SendCt2Reserve128Env` trace `evsRes` witnesses `UnchunkedSendCt2PreEnv x` on
    `sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2ConcatHmacEvents x.st.ct1.length`. -/
theorem unchunkedSendCt2PreEnv_of_reserve {F : ShaCompress}
    {x : UnchunkedSendCt2Ghost F} {evsRes : List AllocEvent}
    (hRes : SendCt2Reserve128Env x.st.ct1.length evsRes) :
    UnchunkedSendCt2PreEnv x
      (sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2ConcatHmacEvents x.st.ct1.length) :=
  ⟨evsRes, hRes, rfl⟩

/-- Reassociates the cumulative Segments 2–5a event list into its `UnchunkedSendCt2PreEnv`
    prefix followed by `sendCt2MdDeallocEvents`. -/
theorem sendCt2Seg23_res_seg5a_eq (es : Bytes) (evsRes : List AllocEvent) (ct1Len : Nat) :
    sendCt2Seg23Events es ++ evsRes ++ sendCt2Seg5aEvents ct1Len =
      (sendCt2Seg23Events es ++ evsRes ++ sendCt2ConcatHmacEvents ct1Len) ++
        sendCt2MdDeallocEvents ct1Len := by
  unfold sendCt2Seg5aEvents
  simp only [List.append_assoc]

/-- At exit of Segment 5a (`+836`), the accumulated allocator event list already lies in
    `UnchunkedSendCt2PostEnv x`. -/
theorem unchunkedSendCt2PostEnv_of_seg5a {F : ShaCompress}
    {x : UnchunkedSendCt2Ghost F} {evsRes : List AllocEvent}
    (hRes : SendCt2Reserve128Env x.st.ct1.length evsRes) :
    UnchunkedSendCt2PostEnv x
      (sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2Seg5aEvents x.st.ct1.length) :=
  ⟨sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2ConcatHmacEvents x.st.ct1.length,
    sendCt2MdDeallocEvents x.st.ct1.length,
    unchunkedSendCt2PreEnv_of_reserve hRes,
    freeOnlyEvs_sendCt2MdDeallocEvents x.st.ct1.length,
    sendCt2Seg23_res_seg5a_eq x.st.es evsRes x.st.ct1.length⟩

/-- Appending any trailing `FreeOnlyEvs` epilogue deallocations `evsFree` (Segment 5b drops of
    `ct1`, `es`, and `ek`) to the Segment 5a event list preserves `UnchunkedSendCt2PostEnv x`. -/
theorem unchunkedSendCt2PostEnv_of_seg5a_append_free {F : ShaCompress}
    {x : UnchunkedSendCt2Ghost F} {evsRes evsFree : List AllocEvent}
    (hRes : SendCt2Reserve128Env x.st.ct1.length evsRes)
    (hFree : FreeOnlyEvs evsFree) :
    UnchunkedSendCt2PostEnv x
      ((sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2Seg5aEvents x.st.ct1.length) ++
        evsFree) := by
  refine ⟨sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2ConcatHmacEvents x.st.ct1.length,
    sendCt2MdDeallocEvents x.st.ct1.length ++ evsFree,
    unchunkedSendCt2PreEnv_of_reserve hRes,
    FreeOnlyEvs.append (freeOnlyEvs_sendCt2MdDeallocEvents x.st.ct1.length) hFree, ?_⟩
  rw [sendCt2Seg23_res_seg5a_eq, List.append_assoc]

/-! ## Postcondition Segment Specializations -/

theorem send_ct2_reserve_ct1_placed_postQ_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (doReserveSpec M A lim))
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ)
    (cap_ct1 ptr_ct1 : BitVec 64)
    (s0 st : State) (F_frame R : SepProp)
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hct1_lt32 : x.st.ct1.length < 2 ^ 32)
    (hpc : st.pc = (blkPl_347).base + 656#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hcont : ∀ (st' : State) (cap_ct1' ptr_ct1' : BitVec 64) (evsRes : List AllocEvent),
      SendCt2Reserve128Env x.st.ct1.length evsRes →
      cap_ct1' ≠ 0#64 →
      x.st.ct1.length + 128 ≤ cap_ct1'.toNat →
      cap_ct1'.toNat < 2 ^ 63 →
      ptr_ct1' ≠ 0#64 →
      st'.pc = (blkPl_347).base + 676#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x1 = BitVec.ofNat 64 x.st.ct1.length →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        (((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          (ptr_ct1' ↦ₛ x.st.ct1) ∗
          memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length)
            (cap_ct1'.toNat - x.st.ct1.length) ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗
          A.pool lim (M.stepEvents (sendCt2Seg23Events x.st.es ++ evsRes) st0) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        (sendCt2PlacedPostQ M A lim F K x st0 s0 R)
        sendCt2PlacedPostQp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      (vecU8At A.repAlloc (s0.sp - 304#64) cap_ct1 ptr_ct1 x.st.ct1 ∗
        A.pool lim (M.stepEvents (sendCt2Seg23Events x.st.es) st0) st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      (sendCt2PlacedPostQ M A lim F K x st0 s0 R)
      sendCt2PlacedPostQp :=
  send_ct2_reserve_ct1_placed_preEnv_wpp h_res x st0 cap_ct1 ptr_ct1 s0 st F_frame
    hPre hct1_lt32 hpc hrun hsp hsp_s0 htr hvregs hcont

theorem send_ct2_scan_to_628_placed_postQ_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMemcpySym) framelessMemcpyAcpSpec)
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ) (esPtr : BitVec 64)
    (s0 st : State) (F_frame R : SepProp)
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hes_len : x.st.es.length = 2080)
    (hpc : st.pc = (blkPl_347).base + 136#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx8 : st.readReg64 .x8 = esPtr + 1536#64)
    (hx9 : st.readReg64 .x9 = 512#64)
    (hx10 : st.readReg64 .x10 = 2#64)
    (hx11 : st.readReg64 .x11 = 65534#64)
    (hx13 : st.readReg64 .x13 = 65535#64)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx28 : st.readReg64 .x28 = bv% (2 ^ 64 - 1))
    (hcont : ∀ (st' : State) (esWorkPtr : BitVec 64),
      st'.pc = (blkPl_347).base + 552#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x19 = esPtr →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x21 =
        (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 1#64 else 0#64) →
      st'.readReg64 .x22 = esWorkPtr →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x28 =
        (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512)
         then 2080#64 else bv% (2 ^ 64 - 1)) →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        (sendCt2EsWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          A.pool lim (M.stepEvents (sendCt2FlipAllocEvents x.st.es) st0) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        (sendCt2PlacedPostQ M A lim F K x st0 s0 R)
        sendCt2PlacedPostQp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      ((esPtr ↦ₛ x.st.es) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        A.pool lim st0 st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      (sendCt2PlacedPostQ M A lim F K x st0 s0 R)
      sendCt2PlacedPostQp :=
  send_ct2_scan_to_628_placed_preEnv_wpp hshim halloc hmemcpy x st0 esPtr s0 st F_frame
    hPre hes_len hpc hrun hsp hsp_s0 htr hvregs hx8 hx9 hx10 hx11 hx13 hx19 hx28 hcont

theorem send_ct2_628_to_690_placed_postQ_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (henc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMlkemEncaps2Sym) (withVmPreserved (mlkemEncaps2Spec K)))
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ)
    (esPtr ekPtr esWorkPtr : BitVec 64)
    (esVec : List.Vector (BitVec 8) 2080) (ekVec : List.Vector (BitVec 8) 1152)
    (s0 st : State) (F_frame R : SepProp)
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hesVec : esVec.toList = if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then
      flipEndiannessOfEncapsulationStateBytes x.st.es else x.st.es)
    (hekVec : ekVec.toList = x.st.ek)
    (hct2_eq : x.ct2 = (K.encaps2 esVec ekVec).toList)
    (hekPtr_ne : ekPtr ≠ 0#64)
    (hpc : st.pc = (blkPl_347).base + 552#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx20 : st.readReg64 .x20 = ekPtr)
    (hx21 : st.readReg64 .x21 =
      (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 1#64 else 0#64))
    (hx22 : st.readReg64 .x22 = esWorkPtr)
    (hx27 : st.readReg64 .x27 = 1152#64)
    (hx28 : st.readReg64 .x28 =
      (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 2080#64 else bv% (2 ^ 64 - 1)))
    (hcont : ∀ (st' : State) (ptr_ct2 : BitVec 64),
      ptr_ct2 ≠ 0#64 →
      st'.pc = (blkPl_347).base + 656#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x19 = esPtr →
      st'.readReg64 .x20 = ekPtr →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = ptr_ct2 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        ((esPtr ↦ₛ x.st.es) ∗
          (ekPtr ↦ₛ x.st.ek) ∗
          (ptr_ct2 ↦ₛ x.ct2) ∗
          A.live ptr_ct2 128 1 ∗
          memRegion (s0.sp - 272#64) 128 ∗
          A.pool lim (M.stepEvents (sendCt2Seg23Events x.st.es) st0) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        (sendCt2PlacedPostQ M A lim F K x st0 s0 R)
        sendCt2PlacedPostQp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      (sendCt2EsWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗
        (ekPtr ↦ₛ x.st.ek) ∗
        memRegion (s0.sp - 272#64) 128 ∗
        A.pool lim (M.stepEvents (sendCt2FlipAllocEvents x.st.es) st0) st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      (sendCt2PlacedPostQ M A lim F K x st0 s0 R)
      sendCt2PlacedPostQp :=
  send_ct2_628_to_690_placed_preEnv_wpp henc hshim halloc hdealloc x st0
    esPtr ekPtr esWorkPtr esVec ekVec s0 st F_frame
    hPre hesVec hekVec hct2_eq hekPtr_ne hpc hrun hsp hsp_s0 htr hvregs
    hx19 hx20 hx21 hx22 hx27 hx28 hcont

theorem send_ct2_append_hmac_placed_postQ_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (sliceConcat3Spec M A lim))
    (h_hmac : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrLibcruxHmacSym) (libcruxHmacSafeBudgetSpec F M A lim))
    (h_dealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ) (evsRes : List AllocEvent)
    (mkPtr cap_ct1' ptr_ct1' ptr_ct2 e0 : BitVec 64)
    (s0 st : State) (F_frame R : SepProp)
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hRes : SendCt2Reserve128Env x.st.ct1.length evsRes)
    (hct2_len : x.ct2.length = 128)
    (hmk_lt32 : x.st.auth.macKey.length < 2 ^ 32)
    (hdata_lt32 :
      (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length < 2 ^ 32)
    (hmac_eq : x.mac = x.st.auth.macCtUnchecked F x.st.epoch (x.st.ct1 ++ x.ct2))
    (hge128 : x.st.ct1.length + 128 ≤ cap_ct1'.toNat)
    (hmax_ct1' : cap_ct1'.toNat < 2 ^ 63)
    (hpc : st.pc = (blkPl_347).base + 676#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx1 : st.readReg64 .x1 = BitVec.ofNat 64 x.st.ct1.length)
    (hx25 : st.readReg64 .x25 = mkPtr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length)
    (hx27 : st.readReg64 .x27 = ptr_ct2)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State),
      st'.pc = (blkPl_347).base + 836#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x22 = ptr_ct1' →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = mkPtr →
      st'.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length →
      st'.readReg64 .x27 = ptr_ct2 →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        (((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
          ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          memRegion ptr_ct1' cap_ct1'.toNat ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗
          (ptr_ct2 ↦ₛ x.ct2) ∗
          (mkPtr ↦ₛ x.st.auth.macKey) ∗
          vecU8 A.repAlloc (s0.sp - 272#64) x.mac ∗
          memRegion (s0.sp - 248#64) 24 ∗
          memRegion (s0.sp - 224#64) 80 ∗
          memRegion (s0.sp - 144#64) 24 ∗
          ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
          ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗
          A.pool lim
            (M.stepEvents (sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2Seg5aEvents x.st.ct1.length) st0)
            st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        (sendCt2PlacedPostQ M A lim F K x st0 s0 R)
        sendCt2PlacedPostQp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      (((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
        ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        (ptr_ct1' ↦ₛ x.st.ct1) ∗
        memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length)
          (cap_ct1'.toNat - x.st.ct1.length) ∗
        A.live ptr_ct1' cap_ct1'.toNat 1 ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗
        (mkPtr ↦ₛ x.st.auth.macKey) ∗
        memRegion (s0.sp - 272#64) 128 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗
        A.pool lim (M.stepEvents (sendCt2Seg23Events x.st.es ++ evsRes) st0) st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      (sendCt2PlacedPostQ M A lim F K x st0 s0 R)
      sendCt2PlacedPostQp :=
  send_ct2_append_hmac_placed_preEnv_wpp h_concat3 h_hmac h_dealloc x st0 evsRes
    mkPtr cap_ct1' ptr_ct1' ptr_ct2 e0 s0 st F_frame
    hPre hRes hct2_len hmk_lt32 hdata_lt32 hmac_eq hge128 hmax_ct1'
    hpc hrun hsp hsp_s0 htr hvregs hx1 hx25 hx26 hx27 hx29 hcont

/-! ## Composed Relocatable Segments 2–5a (`+136 → +836`) -/

/-- Composed relocatable `[LibsignalPlacement]` budget-threaded pipeline for Segments 2→3→4→5a
    (`+136 → +836`) of `<Ct1SentEkReceived>::send_ct2` (Block `347`), polymorphic over
    `{Q Qp : State → SepProp → Prop}` under `FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x)`. -/
theorem send_ct2_segs_2_to_5a_placed_preEnv_wpp [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (doReserveSpec M A lim))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (sliceConcat3Spec M A lim))
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMemcpySym) framelessMemcpyAcpSpec)
    (henc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMlkemEncaps2Sym) (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac_safe : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrLibcruxHmacSym) (libcruxHmacSafeBudgetSpec F M A lim))
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ)
    (mkPtr esPtr ekPtr ct1Cap ct1Ptr e0 : BitVec 64)
    (esVec : List.Vector (BitVec 8) 2080) (ekVec : List.Vector (BitVec 8) 1152)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hes_len : x.st.es.length = 2080)
    (hesVec : esVec.toList = if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then
      flipEndiannessOfEncapsulationStateBytes x.st.es else x.st.es)
    (hekVec : ekVec.toList = x.st.ek)
    (hct2_eq : x.ct2 = (K.encaps2 esVec ekVec).toList)
    (hct2_len : x.ct2.length = 128)
    (hekPtr_ne : ekPtr ≠ 0#64)
    (hct1_lt32 : x.st.ct1.length < 2 ^ 32)
    (hmk_lt32 : x.st.auth.macKey.length < 2 ^ 32)
    (hdata_lt32 :
      (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length < 2 ^ 32)
    (hmac_eq : x.mac = x.st.auth.macCtUnchecked F x.st.epoch (x.st.ct1 ++ x.ct2))
    (hpc : st.pc = (blkPl_347).base + 136#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx8 : st.readReg64 .x8 = esPtr + 1536#64)
    (hx9 : st.readReg64 .x9 = 512#64)
    (hx10 : st.readReg64 .x10 = 2#64)
    (hx11 : st.readReg64 .x11 = 65534#64)
    (hx13 : st.readReg64 .x13 = 65535#64)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx20 : st.readReg64 .x20 = ekPtr)
    (hx25 : st.readReg64 .x25 = mkPtr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length)
    (hx27 : st.readReg64 .x27 = 1152#64)
    (hx28 : st.readReg64 .x28 = bv% (2 ^ 64 - 1))
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st5 : State) (cap_ct1' ptr_ct1' ptr_ct2 : BitVec 64)
        (evsRes : List AllocEvent),
      SendCt2Reserve128Env x.st.ct1.length evsRes →
      cap_ct1' ≠ 0#64 →
      x.st.ct1.length + 128 ≤ cap_ct1'.toNat →
      cap_ct1'.toNat < 2 ^ 63 →
      ptr_ct1' ≠ 0#64 →
      ptr_ct2 ≠ 0#64 →
      st5.pc = (blkPl_347).base + 836#64 →
      st5.status = .Running →
      st5.sp = s0.sp - 336#64 →
      st5.trace = s0.trace →
      calleeSavedVRegs st5 = calleeSavedVRegs s0 →
      st5.readReg64 .x19 = esPtr →
      st5.readReg64 .x20 = ekPtr →
      st5.readReg64 .x22 = ptr_ct1' →
      st5.readReg64 .x23 = st.readReg64 .x23 →
      st5.readReg64 .x24 = st.readReg64 .x24 →
      st5.readReg64 .x25 = mkPtr →
      st5.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length →
      st5.readReg64 .x27 = ptr_ct2 →
      st5.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st5
        (((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
          ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          memRegion ptr_ct1' cap_ct1'.toNat ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗
          (esPtr ↦ₛ x.st.es) ∗
          (ekPtr ↦ₛ x.st.ek) ∗
          (ptr_ct2 ↦ₛ x.ct2) ∗
          A.live ptr_ct2 128 1 ∗
          (mkPtr ↦ₛ x.st.auth.macKey) ∗
          vecU8 A.repAlloc (s0.sp - 272#64) x.mac ∗
          memRegion (s0.sp - 248#64) 24 ∗
          memRegion (s0.sp - 224#64) 80 ∗
          memRegion (s0.sp - 144#64) 24 ∗
          ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
          unchunkedSendCt2PlacedRoAt ∗
          A.pool lim
            (M.stepEvents (sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2Seg5aEvents x.st.ct1.length) st0)
            st5 ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      ((esPtr ↦ₛ x.st.es) ∗
        (ekPtr ↦ₛ x.st.ek) ∗
        (mkPtr ↦ₛ x.st.auth.macKey) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        vecU8At A.repAlloc (s0.sp - 304#64) ct1Cap ct1Ptr x.st.ct1 ∗
        memRegion (s0.sp - 272#64) 128 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        unchunkedSendCt2PlacedRoAt ∗
        A.pool lim st0 st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      Q Qp := by
  refine sepWPp_rw_pre_eq (by unfold unchunkedSendCt2PlacedRoAt; sep_ac_rfl)
    (send_ct2_scan_to_628_placed_preEnv_wpp hshim halloc hmemcpy x st0 esPtr s0 st
      (F_frame ∗ (mkPtr ↦ₛ x.st.auth.macKey) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        vecU8At A.repAlloc (s0.sp - 304#64) ct1Cap ct1Ptr x.st.ct1 ∗
        memRegion (s0.sp - 272#64) 128 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel))
      hPre hes_len hpc hrun hsp hsp_s0 htr hvregs
      hx8 hx9 hx10 hx11 hx13 hx19 hx28
      (fun st2 esWorkPtr hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx21_2 hx22_2
        hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 => ?_))
  refine sepWPp_rw_pre_eq (by sep_ac_rfl)
    (send_ct2_628_to_690_placed_preEnv_wpp henc hshim halloc hdealloc x st0
      esPtr ekPtr esWorkPtr esVec ekVec s0 st2
      (F_frame ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ (mkPtr ↦ₛ x.st.auth.macKey) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        vecU8At A.repAlloc (s0.sp - 304#64) ct1Cap ct1Ptr x.st.ct1 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel))
      hPre hesVec hekVec hct2_eq hekPtr_ne hpc2 hrun2 hsp2 hsp_s0 htr2 hvregs2
      hx19_2 (hx20_2.trans hx20) hx21_2 hx22_2 (hx27_2.trans hx27) hx28_2
      (fun st3 ptr_ct2 hptr_ct2_ne hpc3 hrun3 hsp3 htr3 hvregs3
        hx19_3 hx20_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx29_3 => ?_))
  refine sepWPp_rw_pre_eq (by sep_ac_rfl)
    (send_ct2_reserve_ct1_placed_preEnv_wpp h_res x st0 ct1Cap ct1Ptr s0 st3
      (F_frame ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ (esPtr ↦ₛ x.st.es) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗ A.live ptr_ct2 128 1 ∗
        memRegion (s0.sp - 272#64) 128 ∗ (mkPtr ↦ₛ x.st.auth.macKey) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel))
      hPre hct1_lt32 hpc3 hrun3 hsp3 hsp_s0 htr3 hvregs3
      (fun st4 cap_ct1' ptr_ct1' evsRes hRes hcap_ct1'_ne hge128 hmax_ct1' hptr_ct1'_ne
        hpc4 hrun4 hsp4 htr4 hvregs4 hx1_4 hx19_4 hx20_4 hx23_4 hx24_4 hx25_4
        hx26_4 hx27_4 hx29_4 => ?_))
  refine sepWPp_rw_pre_eq (by sep_ac_rfl)
    (send_ct2_append_hmac_placed_preEnv_wpp h_concat3 hhmac_safe hdealloc x st0 evsRes
      mkPtr cap_ct1' ptr_ct1' ptr_ct2 e0 s0 st4
      (F_frame ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ (esPtr ↦ₛ x.st.es) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        A.live ptr_ct2 128 1)
      hPre hRes hct2_len hmk_lt32 hdata_lt32 hmac_eq hge128 hmax_ct1'
      hpc4 hrun4 hsp4 hsp_s0 htr4 hvregs4 hx1_4
      (((hx25_4.trans hx25_3).trans hx25_2).trans hx25)
      (((hx26_4.trans hx26_3).trans hx26_2).trans hx26)
      (hx27_4.trans hx27_3)
      (((hx29_4.trans hx29_3).trans hx29_2).trans hx29)
      (fun st5 hpc5 hrun5 hsp5 htr5 hvregs5 hx19_5 hx20_5 hx22_5 hx23_5 hx24_5
        hx25_5 hx26_5 hx27_5 hx29_5 => ?_))
  exact sepWPp_rw_pre_eq (by unfold unchunkedSendCt2PlacedRoAt; sep_ac_rfl)
    (hcont st5 cap_ct1' ptr_ct1' ptr_ct2 evsRes hRes
      hcap_ct1'_ne hge128 hmax_ct1' hptr_ct1'_ne hptr_ct2_ne
      hpc5 hrun5 hsp5 htr5 hvregs5
      ((hx19_5.trans hx19_4).trans hx19_3)
      ((hx20_5.trans hx20_4).trans hx20_3)
      hx22_5
      (((hx23_5.trans hx23_4).trans hx23_3).trans hx23_2)
      (((hx24_5.trans hx24_4).trans hx24_3).trans hx24_2)
      hx25_5 hx26_5 hx27_5 hx29_5)

theorem send_ct2_segs_2_to_5a_placed_postQ_wpp [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (doReserveSpec M A lim))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (sliceConcat3Spec M A lim))
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMemcpySym) framelessMemcpyAcpSpec)
    (henc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMlkemEncaps2Sym) (withVmPreserved (mlkemEncaps2Spec K)))
    (hhmac_safe : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrLibcruxHmacSym) (libcruxHmacSafeBudgetSpec F M A lim))
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ)
    (mkPtr esPtr ekPtr ct1Cap ct1Ptr e0 : BitVec 64)
    (esVec : List.Vector (BitVec 8) 2080) (ekVec : List.Vector (BitVec 8) 1152)
    (s0 st : State) (F_frame R : SepProp)
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hes_len : x.st.es.length = 2080)
    (hesVec : esVec.toList = if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then
      flipEndiannessOfEncapsulationStateBytes x.st.es else x.st.es)
    (hekVec : ekVec.toList = x.st.ek)
    (hct2_eq : x.ct2 = (K.encaps2 esVec ekVec).toList)
    (hct2_len : x.ct2.length = 128)
    (hekPtr_ne : ekPtr ≠ 0#64)
    (hct1_lt32 : x.st.ct1.length < 2 ^ 32)
    (hmk_lt32 : x.st.auth.macKey.length < 2 ^ 32)
    (hdata_lt32 :
      (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length < 2 ^ 32)
    (hmac_eq : x.mac = x.st.auth.macCtUnchecked F x.st.epoch (x.st.ct1 ++ x.ct2))
    (hpc : st.pc = (blkPl_347).base + 136#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx8 : st.readReg64 .x8 = esPtr + 1536#64)
    (hx9 : st.readReg64 .x9 = 512#64)
    (hx10 : st.readReg64 .x10 = 2#64)
    (hx11 : st.readReg64 .x11 = 65534#64)
    (hx13 : st.readReg64 .x13 = 65535#64)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx20 : st.readReg64 .x20 = ekPtr)
    (hx25 : st.readReg64 .x25 = mkPtr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length)
    (hx27 : st.readReg64 .x27 = 1152#64)
    (hx28 : st.readReg64 .x28 = bv% (2 ^ 64 - 1))
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st5 : State) (cap_ct1' ptr_ct1' ptr_ct2 : BitVec 64)
        (evsRes : List AllocEvent),
      SendCt2Reserve128Env x.st.ct1.length evsRes →
      cap_ct1' ≠ 0#64 →
      x.st.ct1.length + 128 ≤ cap_ct1'.toNat →
      cap_ct1'.toNat < 2 ^ 63 →
      ptr_ct1' ≠ 0#64 →
      ptr_ct2 ≠ 0#64 →
      st5.pc = (blkPl_347).base + 836#64 →
      st5.status = .Running →
      st5.sp = s0.sp - 336#64 →
      st5.trace = s0.trace →
      calleeSavedVRegs st5 = calleeSavedVRegs s0 →
      st5.readReg64 .x19 = esPtr →
      st5.readReg64 .x20 = ekPtr →
      st5.readReg64 .x22 = ptr_ct1' →
      st5.readReg64 .x23 = st.readReg64 .x23 →
      st5.readReg64 .x24 = st.readReg64 .x24 →
      st5.readReg64 .x25 = mkPtr →
      st5.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length →
      st5.readReg64 .x27 = ptr_ct2 →
      st5.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st5
        (((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
          ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          memRegion ptr_ct1' cap_ct1'.toNat ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗
          (esPtr ↦ₛ x.st.es) ∗
          (ekPtr ↦ₛ x.st.ek) ∗
          (ptr_ct2 ↦ₛ x.ct2) ∗
          A.live ptr_ct2 128 1 ∗
          (mkPtr ↦ₛ x.st.auth.macKey) ∗
          vecU8 A.repAlloc (s0.sp - 272#64) x.mac ∗
          memRegion (s0.sp - 248#64) 24 ∗
          memRegion (s0.sp - 224#64) 80 ∗
          memRegion (s0.sp - 144#64) 24 ∗
          ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
          unchunkedSendCt2PlacedRoAt ∗
          A.pool lim
            (M.stepEvents (sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2Seg5aEvents x.st.ct1.length) st0)
            st5 ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        (sendCt2PlacedPostQ M A lim F K x st0 s0 R)
        sendCt2PlacedPostQp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      ((esPtr ↦ₛ x.st.es) ∗
        (ekPtr ↦ₛ x.st.ek) ∗
        (mkPtr ↦ₛ x.st.auth.macKey) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        vecU8At A.repAlloc (s0.sp - 304#64) ct1Cap ct1Ptr x.st.ct1 ∗
        memRegion (s0.sp - 272#64) 128 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        unchunkedSendCt2PlacedRoAt ∗
        A.pool lim st0 st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      (sendCt2PlacedPostQ M A lim F K x st0 s0 R)
      sendCt2PlacedPostQp :=
  send_ct2_segs_2_to_5a_placed_preEnv_wpp h_res h_concat3 hshim halloc hdealloc
    hmemcpy henc hhmac_safe x st0 mkPtr esPtr ekPtr ct1Cap ct1Ptr e0 esVec ekVec
    s0 st F_frame hPre hes_len hesVec hekVec hct2_eq hct2_len hekPtr_ne
    hct1_lt32 hmk_lt32 hdata_lt32 hmac_eq hpc hrun hsp hsp_s0 htr hvregs
    hx8 hx9 hx10 hx11 hx13 hx19 hx20 hx25 hx26 hx27 hx28 hx29 hcont

end LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegsBudget
