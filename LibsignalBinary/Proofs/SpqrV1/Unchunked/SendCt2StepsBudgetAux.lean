/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Steps
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import ProofLib.SepLogic.WPp
public meta import ProofLib.SepLogic.WP -- shake: keep
public meta import Lean -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Base
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Decodes
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Issue1275
meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Issue1275 -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WP.Structural

/-!
# Budget-Threaded `<Ct1SentEkReceived>::send_ct2`: Auxiliary Envelopes and Prologue

Proves `FitsEnv` sub-segment projections from `UnchunkedSendCt2PreEnv`, defines fixed-base
`unchunkedCt1SentEkReceivedSendCt2SpecOfPrePostEnv` and `libcruxHmacSafeBudgetSpec`, and
lifts the fixed-base prologue (`+0 → +136`) with `VmPreserved`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalHooks LibsignalPlacement blkPC_347 blkPl_347 libsignalSessionCode lsρ
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  DoReserveCall allocName deallocName doReserveStack extHookStack memcpyName
  reserveCap sessionMemcpyRegionSpec sessionShimSpec shimName
  sub_ok_at_of_fnAddr tripleRatchetProgAtExt withStack
)
open CryptoVerification.LibsignalSpqrV1 (
  Bytes LibcruxHmacCall MlKem issue1275NeedsFlip libcruxHmacName
  mlkemEncaps2Name mlkemEncaps2Spec spqrAuthApi
)
open CryptoVerification.SpqrV1.Alloc (
  doReserve7Name spqrMemcpySym spqrRustAllocSym
  spqrRustNoAllocShimSym spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.Auth.MacHdrFacts (libcruxHmac_fnOff)
open CryptoVerification.SpqrV1.ChainProofs (
  SliceConcat3Ghost bytesAt_false bytesAt_true sliceConcatName
)
open CryptoVerification.SpqrV1.Drop (unchunkedCt1SentEkReceivedAt unchunkedCt2SentAt)
open CryptoVerification.SpqrV1.States.Leaves (
  UnchunkedSendCt2Ghost unchunkedCt1SentEkReceivedSendCt2Name
  unchunkedCt1SentEkReceivedSendCt2_fnOff unchunkedSendCt2RoAt unchunkedSendCt2Stack
)
open CryptoVerification.SpqrV1.Unchunked (
  ctLabel_length doReserve7_fnOff fold_sp_272_128 fold_stA_48_80
  fold_vecU8At_sp_304 mlkemEncaps2_fnOff sendCt2CalleeSavedAt
  sliceConcat_fnOff' spqrLibcruxHmacSym spqrMlkemEncaps2Sym spqrRustDeallocSym
  vecU8HeapAt
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  FreeOnlyEvs RustCliAllocBudget RustLayoutOk VmPreserved fitsEvents_append
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocBudgetSpecBase
  rustCliAllocNoOomSpec rustCliAllocNoOomSpecBase
  rustCliDeallocBudgetSpec rustCliDeallocBudgetSpecBase rustReallocEvents
  subroutine_ok_allocNoOom_of_budget subroutine_ok_allocNoOom_of_budgetBase
)
open LibsignalBinary.Heap.SpecBudget (
  LibcruxHmacEnv libcruxHmacBudgetSpec libcruxHmacSha256Events withVmPreserved
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget (
  SliceConcat3Env fitsEnv_sliceConcat3_iff sliceConcat3Events sliceConcat3Spec
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (doReserveSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudget (do_reserve_7_ok_ext_4k)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget (AllocContracts4K)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveEnv doReserveEvents fitsEnv_doReserve_iff
)

export LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget (
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
  swap_loop_placed_ok
  swap_loop_placed_pool_ok
  scan_loop_false_placed_ok
  scan_loop_false_placed_pool_ok
  scan_loop_true_placed_ok
  scan_loop_true_placed_pool_ok
  send_ct2_prologue_to_scan_placed
  send_ct2_prologue_to_scan_placed_pool
)

theorem fetch_withSvc (P : Program) (svc : State → State) (a : BitVec 64) :
    P.fetch a = (P.withSvc svc).fetch a := rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.sp_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.sp_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg64_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg64_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg32_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg32_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg_setMem_setPC_pre
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false ctLabel_length

/-! ## `FitsEnv` Sub-Segment Projections -/

/-- Any `evsRes` satisfying `SendCt2Reserve128Env` yields `FitsEvents` for the full allocation
    trace `sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2ConcatHmacEvents x.st.ct1.length`. -/
theorem fitsEvents_of_preEnv {F : ShaCompress} {M : AllocCostModel} {lim : BudgetLimits}
    {st0 : M.σ} {x : UnchunkedSendCt2Ghost F} {evsRes : List AllocEvent}
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hRes : SendCt2Reserve128Env x.st.ct1.length evsRes) :
    FitsEvents M lim st0
      (sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2ConcatHmacEvents x.st.ct1.length) :=
  hPre _ ⟨evsRes, hRes, rfl⟩

/-- `FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x)` implies `FitsEvents` for Segments 2–3
    (`sendCt2Seg23Events x.st.es`). -/
theorem fitsEvents_seg23_of_preEnv {F : ShaCompress} {M : AllocCostModel} {lim : BudgetLimits}
    {st0 : M.σ} {x : UnchunkedSendCt2Ghost F}
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x)) :
    FitsEvents M lim st0 (sendCt2Seg23Events x.st.es) := by
  have h := fitsEvents_of_preEnv hPre (SendCt2PlacedBudget.SendCt2Reserve128Env.nil x.st.ct1.length)
  rw [List.append_nil, fitsEvents_append] at h
  exact h.1

theorem fitsEvents_flipAlloc_of_seg23 {M : AllocCostModel} {lim : BudgetLimits}
    {st0 : M.σ} {es : Bytes}
    (h : FitsEvents M lim st0 (sendCt2Seg23Events es)) :
    FitsEvents M lim st0 (sendCt2FlipAllocEvents es) := by
  unfold sendCt2Seg23Events at h
  rw [List.append_assoc, fitsEvents_append] at h
  exact h.1

theorem fitsEvents_flipAlloc_of_preEnv {F : ShaCompress} {M : AllocCostModel} {lim : BudgetLimits}
    {st0 : M.σ} {x : UnchunkedSendCt2Ghost F}
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x)) :
    FitsEvents M lim st0 (sendCt2FlipAllocEvents x.st.es) :=
  fitsEvents_flipAlloc_of_seg23 (fitsEvents_seg23_of_preEnv hPre)

theorem fitsEvents_alloc128_of_seg23 {M : AllocCostModel} {lim : BudgetLimits}
    {st0 : M.σ} {es : Bytes}
    (h : FitsEvents M lim st0 (sendCt2Seg23Events es)) :
    FitsEvents M lim (M.stepEvents (sendCt2FlipAllocEvents es) st0) (rustAllocEvents 128 1) := by
  unfold sendCt2Seg23Events at h
  rw [List.append_assoc, fitsEvents_append] at h
  rw [fitsEvents_append] at h
  exact h.2.1

theorem fitsEvents_flipDealloc_of_seg23 {M : AllocCostModel} {lim : BudgetLimits}
    {st0 : M.σ} {es : Bytes}
    (h : FitsEvents M lim st0 (sendCt2Seg23Events es)) :
    FitsEvents M lim
      (M.stepEvents (sendCt2FlipAllocEvents es ++ rustAllocEvents 128 1) st0)
      (sendCt2FlipDeallocEvents es) := by
  unfold sendCt2Seg23Events at h
  rw [fitsEvents_append] at h
  exact h.2

/-- Slow-path `ct1.reserve(128)` budget admissibility after Segments 2–3. -/
theorem fitsEvents_reserve128_of_preEnv {F : ShaCompress} {M : AllocCostModel}
    {lim : BudgetLimits} {st0 : M.σ} {x : UnchunkedSendCt2Ghost F} {cap : BitVec 64}
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hle : x.st.ct1.length ≤ cap.toNat) (hhi : cap.toNat ≤ x.st.ct1.length + 127) :
    FitsEvents M lim (M.stepEvents (sendCt2Seg23Events x.st.es) st0)
      (sendCt2Reserve128Events cap x.st.ct1.length) := by
  have h := fitsEvents_of_preEnv hPre (SendCt2PlacedBudget.SendCt2Reserve128Env.slow hle hhi)
  rw [List.append_assoc, fitsEvents_append] at h
  have h2 := h.2
  rw [fitsEvents_append] at h2
  exact h2.1

theorem doReserveEvents_128_eq (v cap ptr : BitVec 64) (bs : Bytes) :
    doReserveEvents ⟨v, cap, ptr, bs, 128⟩ = sendCt2Reserve128Events cap bs.length :=
  rfl

theorem fitsEnv_doReserve128_of_fitsEvents {M : AllocCostModel} {lim : BudgetLimits}
    {stCost : M.σ} {v cap ptr : BitVec 64} {bs : Bytes}
    (hFit : FitsEvents M lim stCost (sendCt2Reserve128Events cap bs.length)) :
    FitsEnv M lim stCost (DoReserveEnv ⟨v, cap, ptr, bs, 128⟩) := by
  rw [fitsEnv_doReserve_iff, doReserveEvents_128_eq]
  exact hFit

/-- Segment 5a (`slice_concat_3` + `libcrux_hmac::hmac`) budget admissibility after any `evsRes`
    in `SendCt2Reserve128Env x.st.ct1.length`. -/
theorem fitsEvents_concatHmac_of_preEnv {F : ShaCompress} {M : AllocCostModel}
    {lim : BudgetLimits} {st0 : M.σ} {x : UnchunkedSendCt2Ghost F} {evsRes : List AllocEvent}
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hRes : SendCt2Reserve128Env x.st.ct1.length evsRes) :
    FitsEvents M lim (M.stepEvents (sendCt2Seg23Events x.st.es ++ evsRes) st0)
      (sendCt2ConcatHmacEvents x.st.ct1.length) := by
  have h := fitsEvents_of_preEnv hPre hRes
  rw [fitsEvents_append] at h
  exact h.2

theorem fitsEnv_sliceConcat3_of_concatHmac {M : AllocCostModel} {lim : BudgetLimits}
    {stCost : M.σ} {g : SliceConcat3Ghost} {ct1Len : Nat}
    (hlen : g.bs0.length + g.bs1.length + g.bs2.length = 35 + 8 + (ct1Len + 128))
    (hpos : 0 < g.bs0.length + g.bs1.length + g.bs2.length)
    (hFit : FitsEvents M lim stCost (sendCt2ConcatHmacEvents ct1Len)) :
    FitsEnv M lim stCost (SliceConcat3Env g) := by
  unfold sendCt2ConcatHmacEvents at hFit
  rw [fitsEvents_append] at hFit
  rw [fitsEnv_sliceConcat3_iff]
  unfold sliceConcat3Events
  have hne : g.bs0.length + g.bs1.length + g.bs2.length ≠ 0 := Nat.ne_of_gt hpos
  simp only [hne, ↓reduceIte, hlen]
  exact hFit.1

theorem fitsEnv_libcruxHmac_of_fitsEvents {M : AllocCostModel} {lim : BudgetLimits}
    {stCost : M.σ} {call : LibcruxHmacCall}
    (hk : call.key.length < 2 ^ 32) (hd : call.data.length < 2 ^ 32)
    (hFit : FitsEvents M lim stCost libcruxHmacSha256Events) :
    FitsEnv M lim stCost (LibcruxHmacEnv call) := by
  intro evs hevs
  unfold LibcruxHmacEnv at hevs
  simp only [hk, hd, and_self, ↓reduceIte] at hevs
  subst hevs
  exact hFit

/-! ## Fixed-Base Budget-Threaded Specifications -/

/-- Two-envelope (`PreEnv` / `PostEnv`) budget-threaded fixed-base specification of
    `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2`. -/
def unchunkedCt1SentEkReceivedSendCt2SpecOfPrePostEnv
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) (b : BitVec 64)
    (PreEnv PostEnv : UnchunkedSendCt2Ghost F → List AllocEvent → Prop) :
    Spec (UnchunkedSendCt2Ghost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜b &&& 4095#64 = 0#64 ∧
      s.readReg64 .x0 = x.outA ∧ s.readReg64 .x1 = x.stA ∧
      x.st.send_ct2 K = .ok (x.outUc, x.ct2, x.mac) ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      memRegion x.outA 104 ∗
      unchunkedCt1SentEkReceivedAt A.repAlloc x.stA x.st ∗
      unchunkedSendCt2RoAt b ∗
      A.pool lim st s ∗ stackAt s.sp unchunkedSendCt2Stack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
      unchunkedCt2SentAt A.repAlloc x.outA x.outUc ∗
      vecU8 A.repAlloc (x.outA + 56#64) x.ct2 ∗
      vecU8 A.repAlloc (x.outA + 80#64) x.mac ∗
      memRegion x.stA 128 ∗
      unchunkedSendCt2RoAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp unchunkedSendCt2Stack

abbrev unchunkedCt1SentEkReceivedSendCt2SpecOfEnv
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) (b : BitVec 64)
    (Env : UnchunkedSendCt2Ghost F → List AllocEvent → Prop) :
    Spec (UnchunkedSendCt2Ghost F × M.σ) :=
  unchunkedCt1SentEkReceivedSendCt2SpecOfPrePostEnv M A lim F K b Env Env

abbrev unchunkedCt1SentEkReceivedSendCt2Spec
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) (b : BitVec 64) :
    Spec (UnchunkedSendCt2Ghost F × M.σ) :=
  unchunkedCt1SentEkReceivedSendCt2SpecOfPrePostEnv M A lim F K b
    UnchunkedSendCt2PreEnv UnchunkedSendCt2PostEnv

abbrev sendCt2PostQOfPostEnv
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) (b : BitVec 64)
    (PostEnv : UnchunkedSendCt2Ghost F → List AllocEvent → Prop)
    (x : UnchunkedSendCt2Ghost F) (st : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (unchunkedCt1SentEkReceivedSendCt2SpecOfPrePostEnv M A lim F K b
          UnchunkedSendCt2PreEnv PostEnv).post (x, st) s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev sendCt2PostQOfEnv
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) (b : BitVec 64)
    (Env : UnchunkedSendCt2Ghost F → List AllocEvent → Prop)
    (x : UnchunkedSendCt2Ghost F) (st : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  sendCt2PostQOfPostEnv M A lim F K b Env x st s0 R

abbrev sendCt2PostQ
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) (b : BitVec 64)
    (x : UnchunkedSendCt2Ghost F) (st : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  sendCt2PostQOfPostEnv M A lim F K b UnchunkedSendCt2PostEnv x st s0 R

abbrev sendCt2PostQp : State → SepProp → Prop :=
  fun _ _ => False

/-! ## Budget-Threaded Callee Wrappers -/

/-- Non-panicking budget-threaded `libcrux_hmac::hmac` contract when `key.length < 2 ^ 32` and
    `data.length < 2 ^ 32` are already established at the call site. -/
def libcruxHmacSafeBudgetSpec (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (LibcruxHmacCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.ret ∧ (s.readReg64 .x0).setWidth 32 = 0#32 ∧
      s.readReg64 .x1 = x.keyA ∧ (s.readReg64 .x2).toNat = x.key.length ∧
      s.readReg64 .x3 = x.dataA ∧ (s.readReg64 .x4).toNat = x.data.length ∧
      (s.readReg64 .x5).setWidth 32 = 1#32 ∧ s.readReg64 .x6 = 32#64 ∧
      x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32 ∧
      FitsEvents M lim st libcruxHmacSha256Events⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      memRegion x.ret 24 ∗ A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      vecU8 A.repAlloc x.ret (hmacWith F x.key x.data) ∗
      A.pool lim (M.stepEvents libcruxHmacSha256Events st) sf ∗ stackAt s0.sp extHookStack

theorem subroutine_ok_libcruxHmacSafe_of_budget {prog : Program} {fnAddr : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hraw : subroutine_ok prog fnAddr (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok prog fnAddr (libcruxHmacSafeBudgetSpec F M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [libcruxHmacSafeBudgetSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hk_lt, hd_lt, hFit⟩, hmem⟩
  have hpre' : s0.mem ⊨ (libcruxHmacBudgetSpec F M A lim).pre (x, st) s0 ∗ R := by
    dsimp only [libcruxHmacBudgetSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6,
      fitsEnv_libcruxHmac_of_fitsEvents hk_lt hd_lt hFit⟩, hmem⟩
  refine hraw.mono_outcome (x, st) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [libcruxHmacBudgetSpec, libcruxHmacSafeBudgetSpec] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hevs⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hevs ⊢
    rcases hevs with ⟨⟨_, _, htr, hEnv⟩, hsp_mem⟩
    unfold LibcruxHmacEnv at hEnv
    simp only [hk_lt, hd_lt, and_self, ↓reduceIte] at hEnv
    subst hEnv
    exact ⟨htr, hsp_mem⟩
  · dsimp only [libcruxHmacBudgetSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    rcases hpan.1.1 with hk_ge | hd_ge <;> omega
  · exact Or.inr (Or.inr hex)

theorem libcrux_hmac_safe_placed_ok [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hhmac : HookSat H spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrLibcruxHmacSym) (libcruxHmacSafeBudgetSpec F M A lim) :=
  subroutine_ok_libcruxHmacSafe_of_budget (spqr_hook_ok_of_mem hhmac)

theorem mlkem_encaps2_vm_placed_ok [LibsignalPlacement] {K : MlKem} {H : LibsignalHooks}
    (hencaps2 : HookSat H spqrMlkemEncaps2Sym (withVmPreserved (mlkemEncaps2Spec K))) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMlkemEncaps2Sym) (withVmPreserved (mlkemEncaps2Spec K)) :=
  spqr_hook_ok_of_mem hencaps2

theorem mlkem_encaps2_vm_ok_at_ext (b : BitVec 64) (K : MlKem)
    (ext : String → Option (State → State))
    (hencaps2 : HookSat ext mlkemEncaps2Name (withVmPreserved (mlkemEncaps2Spec K)))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff mlkemEncaps2Name := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withVmPreserved (mlkemEncaps2Spec K)) :=
  hook_ok_at (hname := mlkemEncaps2Name) rfl (hk.trans mlkemEncaps2_fnOff) (by decide)
    (fun _ => by simp only [arm64_norm, mlkemEncaps2Name])
    (by simp [Rust.isPanicSymbol, mlkemEncaps2Name]) hencaps2

theorem libcrux_hmac_safe_budget_ok_at_ext (b : BitVec 64)
    (F : ShaState → List (BitVec 8) → ShaState)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacBudgetSpec F M A lim))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff libcruxHmacName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (libcruxHmacSafeBudgetSpec F M A lim) :=
  subroutine_ok_libcruxHmacSafe_of_budget <|
    hook_ok_at (hname := libcruxHmacName) rfl (hk.trans libcruxHmac_fnOff) (by decide)
      (fun _ => by simp only [arm64_norm, libcruxHmacName])
      (by simp [Rust.isPanicSymbol, libcruxHmacName]) hhmac

theorem shim_ok_at_sendCt2 {b : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
      (withVmPreserved sessionShimSpec) :=
  hA.shim_ok_at unchunkedCt1SentEkReceivedSendCt2Name
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
    (by fnoff_eq)

theorem alloc_ok_at_sendCt2 {b : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        bv% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
      (rustCliAllocBudgetSpecBase M A lim false) :=
  hA.alloc_ok_at unchunkedCt1SentEkReceivedSendCt2Name
    (num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
    (by fnoff_eq)

theorem allocNoOom_ok_at_sendCt2 {b : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        bv% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
      (rustCliAllocNoOomSpecBase M A lim false) :=
  subroutine_ok_allocNoOom_of_budgetBase (alloc_ok_at_sendCt2 hA)

theorem dealloc_ok_at_sendCt2 {b : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        bv% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
      (rustCliDeallocBudgetSpecBase M A lim) :=
  hA.dealloc_ok_at unchunkedCt1SentEkReceivedSendCt2Name
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
    (by fnoff_eq)

theorem memcpy_ok_at_sendCt2 {b : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        bv% (ls_off% "memcpy" -
          ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
      (withStack (withVmPreserved sessionMemcpyRegionSpec) extHookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memcpy_region extHookStack (by decide) (by decide))
    unchunkedCt1SentEkReceivedSendCt2Name
    (num% (ls_off% "memcpy" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
    (by fnoff_eq)

theorem doReserve7_ok_at_sendCt2 {b : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        (bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]") -
          bv% (ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2")))
      (doReserveSpec M A lim) := by
  have hrel :
      (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        (bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]") -
          bv% (ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2")) =
      (tripleRatchetProgAtExt b ext).fnAddr doReserve7Name := by
    dsimp only [tripleRatchetProgAtExt]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      unchunkedCt1SentEkReceivedSendCt2_fnOff, doReserve7_fnOff]
    bv_omega
  rw [hrel]
  exact do_reserve_7_ok_ext_4k hA

theorem sliceConcat3_ok_at_sendCt2 {b : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hconcat3 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr sliceConcatName)
      (sliceConcat3Spec M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        bv% (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" -
          ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
      (sliceConcat3Spec M A lim) := by
  have hrel :
      (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        bv% (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" -
          ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      (tripleRatchetProgAtExt b ext).fnAddr sliceConcatName := by
    dsimp only [tripleRatchetProgAtExt]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      unchunkedCt1SentEkReceivedSendCt2_fnOff, sliceConcat_fnOff']
    bv_omega
  rw [hrel]
  exact hconcat3

/-! ## `SepWP` / `SepWPp` Combinators -/

theorem sepWP_fold_eq {prog : Program} {pc : BitVec 64} {s : State} {P T T' : SepProp}
    (F : SepProp) {post : State → SepProp → Prop} {oom : State → SepProp}
    (hent : T ⊢ T') (hf : P = T ∗ F)
    (h : SepWP prog pc s (T' ∗ F) post oom) :
    SepWP prog pc s P post oom :=
  SepWP.weaken_pre (hf ▸ sepConj_mono_left hent) h

theorem sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hent : P ⊢ P') (h : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => h R (Satisfies.mono (sepConj_mono_left hent) hm) hL

theorem sepWPp_rw_pre_eq {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (heq : P = P') (h : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  heq ▸ h

theorem sepWPp_fold_eq {prog : Program} {ret : BitVec 64} {s : State} {P T T' : SepProp}
    (F : SepProp) {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hent : T ⊢ T') (hf : P = T ∗ F)
    (h : SepWPp prog ret s (T' ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  sepWPp_weaken_pre (hf ▸ sepConj_mono_left hent) h

theorem sepWPp_pure_left_eq {prog : Program} {ret : BitVec 64} {s : State} {φ : Prop}
    {P : SepProp} (F : SepProp) {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P = ⌜φ⌝ ∗ F) (h : φ → SepWPp prog ret s F Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rw [hf, sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

theorem sepWPp_exists_left_eq {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {Φ : α → SepProp} {P : SepProp} (F : SepProp)
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P = (∃∗ a : α, Φ a) ∗ F)
    (h : ∀ a : α, SepWPp prog ret s (Φ a ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rw [hf, sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨a, hma⟩
  exact h a R (by simpa only [sepConj_assoc] using hma) hL

theorem sepWPp_intro_state {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ s' : State, s' = s → SepWPp prog ret s' P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  h s rfl

/-- Framed `SepWPp` subroutine call for any total-correctness (`onExit = ⌜False⌝`,
    `onPanic = ⌜False⌝`, `onOom = ⌜False⌝`) contract `spec`, polymorphic in `Q` and `Qp`. -/
theorem sepWPp_call_noPanic {α : Type} {prog : Program}
    {fnAddr ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog fnAddr spec)
    (x : α) (F : SepProp) {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hexit : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) Q Qp oom) :
    SepWPp prog target_pc s P Q Qp oom := by
  refine SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp_align hlr hpre
    (fun sf code _ _ hpost => False.elim (not_satisfies_false_sepConj (hexit code sf ▸ hpost)))
    (fun sf _ ⟨_, hpost⟩ => False.elim (not_satisfies_false_sepConj (hpan sf ▸ hpost)))
    hnext
    (fun sf _ _ hpost => False.elim (not_satisfies_false_sepConj (hoom sf ▸ hpost)))

/-- Framed `SepWPp` call rule for `rustCliAllocNoOomSpec M A lim false` (`__rust_alloc`),
    discharging the OOM branch directly from `FitsEvents M lim stCost (rustAllocEvents size align)`. -/
theorem call_rustAllocNoOom_wppBase {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {fnAddr ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog fnAddr (rustCliAllocNoOomSpecBase M A lim false))
    (size align : Nat) (stCost : M.σ)
    (hlay : RustLayoutOk size align)
    (hFit : FitsEvents M lim stCost (rustAllocEvents size align))
    {s : State} {sp_call : BitVec 64} {P : SepProp} (Frame : SepProp)
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : (s.readReg64 Reg.x0).toNat = size) (hx1 : (s.readReg64 Reg.x1).toNat = align)
    (hsplit : P = (A.pool lim stCost s ∗ stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → AllocCallPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → (sf.readReg64 .x0).toNat % align = 0 →
      SepWPp prog target_pc sf
        ((A.live (sf.readReg64 .x0) size align ∗
          memRegion (sf.readReg64 .x0) size ∗
          A.pool lim (M.stepEvents (rustAllocEvents size align) stCost) sf ∗
          stackAt sp_call allocHookStack) ∗ Frame) Q Qp oom) :
    SepWPp prog target_pc s P Q Qp oom := by
  refine sepWPp_call_noPanic hcall (size, align, stCost) Frame
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf hpc_sf hrun_sf hsp_sf _ => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [rustCliAllocNoOomSpecBase]
    rw [hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay, hFit⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [rustCliAllocNoOomSpecBase]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp]
    refine sepWPp_pure_left_eq
      ((A.pool lim (M.stepEvents (rustAllocEvents size align) stCost) sf ∗
        stackAt sp_call allocHookStack ∗
        A.live (sf.readReg64 .x0) size align ∗
        memRegion (sf.readReg64 .x0) size) ∗ Frame)
      (by sep_ac_rfl) ?_
    rintro ⟨hacp, hmod, hne⟩
    exact sepWPp_rw_pre_eq (by sep_ac_rfl)
      (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hacp hne hmod)

theorem call_rustAllocNoOom_wpp [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {fnAddr ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog fnAddr (rustCliAllocNoOomSpec M A lim false))
    (size align : Nat) (stCost : M.σ)
    (hlay : RustLayoutOk size align)
    (hFit : FitsEvents M lim stCost (rustAllocEvents size align))
    {s : State} {sp_call : BitVec 64} {P : SepProp} (Frame : SepProp)
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : (s.readReg64 Reg.x0).toNat = size) (hx1 : (s.readReg64 Reg.x1).toNat = align)
    (hsplit : P = (A.pool lim stCost s ∗ stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → AllocCallPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → (sf.readReg64 .x0).toNat % align = 0 →
      SepWPp prog target_pc sf
        ((A.live (sf.readReg64 .x0) size align ∗
          memRegion (sf.readReg64 .x0) size ∗
          A.pool lim (M.stepEvents (rustAllocEvents size align) stCost) sf ∗
          stackAt sp_call allocHookStack) ∗ Frame) Q Qp oom)
    (hlr_ls : LsRetAddr624 ret_pc := by simp (config := { decide := true }) only [wp_norm, arm64_norm]) :
    SepWPp prog target_pc s P Q Qp oom := by
  refine sepWPp_call_noPanic hcall (size, align, stCost) Frame
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf hpc_sf hrun_sf hsp_sf _ => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [rustCliAllocNoOomSpec]
    rw [hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay, hFit, hlr.symm ▸ hlr_ls⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [rustCliAllocNoOomSpec]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp]
    refine sepWPp_pure_left_eq
      ((A.pool lim (M.stepEvents (rustAllocEvents size align) stCost) sf ∗
        stackAt sp_call allocHookStack ∗
        A.live (sf.readReg64 .x0) size align ∗
        memRegion (sf.readReg64 .x0) size) ∗ Frame)
      (by sep_ac_rfl) ?_
    rintro ⟨hacp, hmod, hne⟩
    exact sepWPp_rw_pre_eq (by sep_ac_rfl)
      (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hacp hne hmod)

/-! ## Fixed-Base Segment 1: Prologue (`+0 → +136`) -/

theorem send_ct2_prologue_to_scan_vm {b : BitVec 64} {ext : String → Option (State → State)}
    {F : ShaCompress} {M : AllocCostModel} (A : RustCliAllocBudget M)
    (outA stA : BitVec 64)
    (st : Ct1SentEkReceived (spqrAuthApi F))
    (rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr ct1Cap ct1Ptr : BitVec 64)
    (l0 l1 l2 l3 l4 l5 s64 e0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : BitVec 64)
    (s0 : State) (Frame : SepProp)
    (hes_len : st.es.length = 2080)
    (hek_len : st.ek.length = 1152)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
    (hrun : s0.status = .Running)
    (hsp : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 .x0 = outA)
    (hx1 : s0.readReg64 .x1 = stA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 136#64)
      s0
      ((stA ↦₆₄ rkCap) ∗ ((stA + 8#64) ↦₆₄ rkPtr) ∗
        ((stA + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
        ((stA + 24#64) ↦₆₄ mkCap) ∗ ((stA + 32#64) ↦₆₄ mkPtr) ∗
        ((stA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
        ((stA + 48#64) ↦₆₄ esCap) ∗ ((stA + 56#64) ↦₆₄ esPtr) ∗
        ((stA + 64#64) ↦₆₄ BitVec.ofNat 64 st.es.length) ∗
        ((stA + 72#64) ↦₆₄ ekCap) ∗ ((stA + 80#64) ↦₆₄ ekPtr) ∗
        ((stA + 88#64) ↦₆₄ BitVec.ofNat 64 st.ek.length) ∗
        ((stA + 96#64) ↦₆₄ ct1Cap) ∗ ((stA + 104#64) ↦₆₄ ct1Ptr) ∗
        ((stA + 112#64) ↦₆₄ BitVec.ofNat 64 st.ct1.length) ∗
        ((stA + 120#64) ↦₆₄ st.epoch) ∗
        vecU8HeapAt A.repAlloc ct1Cap ct1Ptr st.ct1 ∗
        ((s0.sp - 328#64) ↦₆₄ l0) ∗ ((s0.sp - 320#64) ↦₆₄ l1) ∗
        ((s0.sp - 312#64) ↦₆₄ l2) ∗ ((s0.sp - 304#64) ↦₆₄ l3) ∗
        ((s0.sp - 296#64) ↦₆₄ l4) ∗ ((s0.sp - 288#64) ↦₆₄ l5) ∗
        ((s0.sp - 272#64) ↦₆₄ s64) ∗ memRegion (s0.sp - 264#64) 120 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
        ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
        ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
        ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
        ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
        ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗
        Frame)
      (fun sf Pf =>
        VmPreserved s0 sf ∧
        Pf = ((stA ↦₆₄ rkCap) ∗ ((stA + 8#64) ↦₆₄ rkPtr) ∗
          ((stA + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
          ((stA + 24#64) ↦₆₄ mkCap) ∗ ((stA + 32#64) ↦₆₄ mkPtr) ∗
          ((stA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
          memRegion (stA + 48#64) 80 ∗
          ((s0.sp - 328#64) ↦₆₄ esCap) ∗ ((s0.sp - 320#64) ↦₆₄ ekCap) ∗
          ((s0.sp - 312#64) ↦₆₄ st.epoch) ∗
          vecU8At A.repAlloc (s0.sp - 304#64) ct1Cap ct1Ptr st.ct1 ∗
          memRegion (s0.sp - 272#64) 128 ∗
          ((s0.sp - 120#64) ↦₆₄ e0) ∗
          sendCt2CalleeSavedAt s0 ∗
          Frame) ∧
        sf.sp = s0.sp - 336#64 ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        sf.readReg64 .x8 = esPtr + 1536#64 ∧
        sf.readReg64 .x9 = 512#64 ∧
        sf.readReg64 .x10 = 2#64 ∧
        sf.readReg64 .x11 = 65534#64 ∧
        sf.readReg64 .x13 = 65535#64 ∧
        sf.readReg64 .x19 = esPtr ∧
        sf.readReg64 .x20 = ekPtr ∧
        sf.readReg64 .x23 = outA ∧
        sf.readReg64 .x24 = stA ∧
        sf.readReg64 .x25 = mkPtr ∧
        sf.readReg64 .x26 = BitVec.ofNat 64 st.auth.macKey.length ∧
        sf.readReg64 .x27 = 1152#64 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        sf.readReg64 .x29 = s0.sp - 96#64) := by
  simp only [wp_norm, arm64_norm] at hx0 hx1
  send_ct2_fetches b trapHooks 136
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  simp +singlePass only [Program.fnAddr_rebase, fetch_withSvc _ noSyscalls] at *
  revert hpc
  generalize_entry
    (libsignalSessionCode.fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      fnOffVal reverting [Program.fetch, SepWP]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  intro hpc
  apply sepWP_rebase_vmPreserved
  generalize_entry libsignalSessionCode = codeProg reverting [Program.fetch, SepWP]
  examples_hide_fetches
  rw [hes_len, hek_len]
  wp_steps
  refine sepWP_fold_eq
    ((stA ↦₆₄ rkCap) ∗ ((stA + 8#64) ↦₆₄ rkPtr) ∗
      ((stA + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
      ((stA + 24#64) ↦₆₄ mkCap) ∗ ((stA + 32#64) ↦₆₄ mkPtr) ∗
      ((stA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
      ((s0.sp - 328#64) ↦₆₄ esCap) ∗ ((s0.sp - 320#64) ↦₆₄ ekCap) ∗
      ((s0.sp - 312#64) ↦₆₄ st.epoch) ∗
      (((s0.sp - 304#64) ↦₆₄ ct1Cap) ∗ ((s0.sp - 296#64) ↦₆₄ ct1Ptr) ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 st.ct1.length) ∗
        vecU8HeapAt A.repAlloc ct1Cap ct1Ptr st.ct1) ∗
      (((s0.sp - 272#64) ↦₆₄ 2080#64) ∗ memRegion (s0.sp - 264#64) 120) ∗
      ((s0.sp - 120#64) ↦₆₄ e0) ∗
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
      ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
      ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
      ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
      ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      Frame)
    (fold_stA_48_80 stA esCap esPtr 2080#64 ekCap ekPtr 1152#64
      ct1Cap ct1Ptr (BitVec.ofNat 64 st.ct1.length) st.epoch)
    (by simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
         Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30, arm64_norm]; sep_ac_rfl) ?_
  refine sepWP_fold_eq
    (memRegion (stA + 48#64) 80 ∗
      (stA ↦₆₄ rkCap) ∗ ((stA + 8#64) ↦₆₄ rkPtr) ∗
      ((stA + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
      ((stA + 24#64) ↦₆₄ mkCap) ∗ ((stA + 32#64) ↦₆₄ mkPtr) ∗
      ((stA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
      ((s0.sp - 328#64) ↦₆₄ esCap) ∗ ((s0.sp - 320#64) ↦₆₄ ekCap) ∗
      ((s0.sp - 312#64) ↦₆₄ st.epoch) ∗
      (((s0.sp - 272#64) ↦₆₄ 2080#64) ∗ memRegion (s0.sp - 264#64) 120) ∗
      ((s0.sp - 120#64) ↦₆₄ e0) ∗
      sendCt2CalleeSavedAt s0 ∗
      Frame)
    (fold_vecU8At_sp_304 A.repAlloc s0.sp ct1Cap ct1Ptr st.ct1)
    (by unfold sendCt2CalleeSavedAt; sep_ac_rfl) ?_
  refine sepWP_fold_eq
    ((stA ↦₆₄ rkCap) ∗ ((stA + 8#64) ↦₆₄ rkPtr) ∗
      ((stA + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
      ((stA + 24#64) ↦₆₄ mkCap) ∗ ((stA + 32#64) ↦₆₄ mkPtr) ∗
      ((stA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
      memRegion (stA + 48#64) 80 ∗
      ((s0.sp - 328#64) ↦₆₄ esCap) ∗ ((s0.sp - 320#64) ↦₆₄ ekCap) ∗
      ((s0.sp - 312#64) ↦₆₄ st.epoch) ∗
      vecU8At A.repAlloc (s0.sp - 304#64) ct1Cap ct1Ptr st.ct1 ∗
      ((s0.sp - 120#64) ↦₆₄ e0) ∗
      sendCt2CalleeSavedAt s0 ∗
      Frame)
    (fold_sp_272_128 s0.sp 2080#64)
    (by sep_ac_rfl) ?_
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨by simp only [wp_norm, arm64_norm], by sep_ac_rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [State.sp, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x13, Reg.x19, Reg.x20,
      Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29,
      arm64_norm, hx0, hx1]

theorem send_ct2_prologue_to_scan_pool {b : BitVec 64} {ext : String → Option (State → State)}
    {F : ShaCompress} {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stCost : M.σ)
    (outA stA : BitVec 64)
    (st : Ct1SentEkReceived (spqrAuthApi F))
    (rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr ct1Cap ct1Ptr : BitVec 64)
    (l0 l1 l2 l3 l4 l5 s64 e0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : BitVec 64)
    (s0 : State) (Frame : SepProp)
    (hes_len : st.es.length = 2080)
    (hek_len : st.ek.length = 1152)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
    (hrun : s0.status = .Running)
    (hsp : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 .x0 = outA)
    (hx1 : s0.readReg64 .x1 = stA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 136#64)
      s0
      ((stA ↦₆₄ rkCap) ∗ ((stA + 8#64) ↦₆₄ rkPtr) ∗
        ((stA + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
        ((stA + 24#64) ↦₆₄ mkCap) ∗ ((stA + 32#64) ↦₆₄ mkPtr) ∗
        ((stA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
        ((stA + 48#64) ↦₆₄ esCap) ∗ ((stA + 56#64) ↦₆₄ esPtr) ∗
        ((stA + 64#64) ↦₆₄ BitVec.ofNat 64 st.es.length) ∗
        ((stA + 72#64) ↦₆₄ ekCap) ∗ ((stA + 80#64) ↦₆₄ ekPtr) ∗
        ((stA + 88#64) ↦₆₄ BitVec.ofNat 64 st.ek.length) ∗
        ((stA + 96#64) ↦₆₄ ct1Cap) ∗ ((stA + 104#64) ↦₆₄ ct1Ptr) ∗
        ((stA + 112#64) ↦₆₄ BitVec.ofNat 64 st.ct1.length) ∗
        ((stA + 120#64) ↦₆₄ st.epoch) ∗
        vecU8HeapAt A.repAlloc ct1Cap ct1Ptr st.ct1 ∗
        ((s0.sp - 328#64) ↦₆₄ l0) ∗ ((s0.sp - 320#64) ↦₆₄ l1) ∗
        ((s0.sp - 312#64) ↦₆₄ l2) ∗ ((s0.sp - 304#64) ↦₆₄ l3) ∗
        ((s0.sp - 296#64) ↦₆₄ l4) ∗ ((s0.sp - 288#64) ↦₆₄ l5) ∗
        ((s0.sp - 272#64) ↦₆₄ s64) ∗ memRegion (s0.sp - 264#64) 120 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
        ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
        ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
        ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
        ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
        ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗
        A.pool lim stCost s0 ∗ Frame)
      (fun sf Pf =>
        VmPreserved s0 sf ∧
        Pf = ((stA ↦₆₄ rkCap) ∗ ((stA + 8#64) ↦₆₄ rkPtr) ∗
          ((stA + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
          ((stA + 24#64) ↦₆₄ mkCap) ∗ ((stA + 32#64) ↦₆₄ mkPtr) ∗
          ((stA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
          memRegion (stA + 48#64) 80 ∗
          ((s0.sp - 328#64) ↦₆₄ esCap) ∗ ((s0.sp - 320#64) ↦₆₄ ekCap) ∗
          ((s0.sp - 312#64) ↦₆₄ st.epoch) ∗
          vecU8At A.repAlloc (s0.sp - 304#64) ct1Cap ct1Ptr st.ct1 ∗
          memRegion (s0.sp - 272#64) 128 ∗
          ((s0.sp - 120#64) ↦₆₄ e0) ∗
          sendCt2CalleeSavedAt s0 ∗
          A.pool lim stCost sf ∗ Frame) ∧
        sf.sp = s0.sp - 336#64 ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        sf.readReg64 .x8 = esPtr + 1536#64 ∧
        sf.readReg64 .x9 = 512#64 ∧
        sf.readReg64 .x10 = 2#64 ∧
        sf.readReg64 .x11 = 65534#64 ∧
        sf.readReg64 .x13 = 65535#64 ∧
        sf.readReg64 .x19 = esPtr ∧
        sf.readReg64 .x20 = ekPtr ∧
        sf.readReg64 .x23 = outA ∧
        sf.readReg64 .x24 = stA ∧
        sf.readReg64 .x25 = mkPtr ∧
        sf.readReg64 .x26 = BitVec.ofNat 64 st.auth.macKey.length ∧
        sf.readReg64 .x27 = 1152#64 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        sf.readReg64 .x29 = s0.sp - 96#64) := by
  refine SepWP.seq
    (send_ct2_prologue_to_scan_vm A outA stA st rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr
      ct1Cap ct1Ptr l0 l1 l2 l3 l4 l5 s64 e0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11
      s0 (A.pool lim stCost s0 ∗ Frame) hes_len hek_len hpc hrun hsp hx0 hx1)
    fun sf Pf hpcm hrunm
      ⟨hvm, hPf, hsp', htr', hvregs', hx8, hx9, hx10, hx11, hx13, hx19, hx20, hx23, hx24,
        hx25, hx26, hx27, hx28, hx29⟩ => ?_
  rw [hPf, ← A.pool_of_vmPreserved hvm]
  exact SepWP.done hpcm hrunm
    ⟨hvm, rfl, hsp', htr', hvregs', hx8, hx9, hx10, hx11, hx13, hx19, hx20, hx23, hx24,
      hx25, hx26, hx27, hx28, hx29⟩

end LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux
