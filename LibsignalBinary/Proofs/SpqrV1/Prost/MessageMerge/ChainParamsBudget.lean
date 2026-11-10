/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParams
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.DefsClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergeCodeSym
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.Defs
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.Prost
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Budget-Threaded SPQR V1 `ChainParams::merge` Verification (Block `294`)

Defines concrete allocator event envelopes (`ChainParamsErrEnv`, `ChainParamsMergeEnv`,
`ChainParamsMergePostEnv`) and budget-threaded contracts (`chainParamsMergeSpecOfEnv`,
`chainParamsMergeSpec`), and proves code-loaded `[LibsignalPlacement]` Block `294` contracts
(`chainParamsMerge_cl_placed_ok_of_contracts`, `chainParamsMerge_cro_placed_ok_of_contracts`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement extract_withLsCodeLoaded lsmpl
   withLsCodeLoaded)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack extract_withLsCodeRoLoaded
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (HighCalleeSaved IsDropSuffix SkipFieldGhost bv32_zeroExtend_ofNat decodeVarint_suffix
   itag_beq_tag_false key_shr32_of_ge key_shr32_of_lt key_wt_none key_wt_some
   memRegion_48_split2 pointsTo64_memRegion32_entails_40 pointsTo64_pair_entails_memRegion16
   pointsToBytes_prefix_join sf_truncate32_ofNat64 skip_suffix sliceCursorAfter
   sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt suffix_trans tag_cbz_false
   ule_len_of_ge ule_len_of_lt w1_tag_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.LibsignalSpqrV1 (ChainParamsPB)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_decodeVarint_toOption)
open CryptoVerification.SpqrV1.ProtoRepr (chainParamsPBAt)
open CryptoVerification.SpqrV1.Varint
  (skipBelow3 skipBelow3_err skipBelow3_err_entails skipBelow3_leaf skipBelow3_leaf_entails
   skipField3Stack stackAt_skipField3)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChainParamsMergeGhost SepWPp.call_frame_lscl_mm SepWPp.elim_lsclProp
   SepWPp.of_sepWP_lscl_mm WppPost blkPC_294 blkPl_294 bv_len_sub_limit
   chainParamsMergeStack chainParamsPBAt_entails_exists chainParamsPB_mergeField_other
   chainParamsPB_mergeField_tag1 chainParamsPB_mergeField_tag2 cmp_len_limit_of_eq
   cmp_len_limit_of_gt cmp_len_limit_of_lt codecWireTypeToProto decodeErrorWith_one_entails_le1
   decodeErrorWith_zero_entails_le1 iwt_cbnz_true_of_ne_varint
   memRegion8_memRegion40_entails_48 memRegion_48_split_96
   memRegion_48_wtErr96 mergeLoopBin mergeLoopBin_eq_limit mergeLoopBin_lt_limit
   mergeLoopBin_of_decodeVarint_none mergeLoopBin_of_key_ge mergeLoopBin_of_key_ok
   mergeLoopBin_of_tag_zero mergeLoopBin_of_wt_none mergeMessageBin
   mergeMessageBin_eq_proto_mergeMessage pointsTo64_memRegion40_entails_48
   protoPrefixStep_chainParamsPB_mergeField sepConj_memRegion_48_split_96 setWidth8_ofNat64_wt
   skipBelow3_99_eq_stackAt_98 subroutine_ok_withLsCodeLoaded_of_withLsclProp
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm withLsclProp
   wtErr96_entails_memRegion40 wt_beq_two_of_lengthDelimited wt_beq_two_of_ne_lengthDelimited)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget fitsEvents_append
   rustAllocEvents)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv DecodeErrorPushEnv decodeErrorFromBudgetSpec decodeErrorPushBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (SkipField3Env skipField3Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv SkipFieldEnv decodeVarintSliceEvents skipFieldEventsCore)

private theorem sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

@[local simp, local arm64_norm]
private theorem bv64_sub_zero (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
private theorem bv64_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre calleeSavedVRegs_setMem_pre

/-! ## 1. Allocator Event Envelopes & Budget Specifications (Block `294`) -/

/-- Exact error-path allocator event envelope of `ChainParams::merge` (Block `294`):
either a single `DecodeError::from` (`72`-byte `Inner`), or `DecodeError::from` followed by
`DecodeError::push` at stack length `0`. -/
inductive ChainParamsErrEnv : List AllocEvent → Prop where
  | fromOnly : ChainParamsErrEnv (rustAllocEvents 72 8)
  | fromPush {evs_p : List AllocEvent} :
      DecodeErrorPushEnv 0 evs_p → ChainParamsErrEnv (rustAllocEvents 72 8 ++ evs_p)

/-- Precondition allocator event envelope of `ChainParams::merge` (Block `294`). -/
inductive ChainParamsMergeEnv (_x : ChainParamsMergeGhost) : List AllocEvent → Prop where
  | ok : ChainParamsMergeEnv _x []
  | err {evs : List AllocEvent} : ChainParamsErrEnv evs → ChainParamsMergeEnv _x evs

/-- Postcondition allocator event envelope of `ChainParams::merge` (Block `294`):
`evs = []` on `Ok`, and `ChainParamsErrEnv evs` on `Err`. -/
def ChainParamsMergePostEnv (x : ChainParamsMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
  | some _ => evs = []
  | none => ChainParamsErrEnv evs

theorem chainParamsMergePostEnv_imp_pre {x : ChainParamsMergeGhost} {evs : List AllocEvent}
    (h : ChainParamsMergePostEnv x evs) :
    ChainParamsMergeEnv x evs := by
  dsimp only [ChainParamsMergePostEnv] at h
  split at h
  · subst h; exact .ok
  · exact .err h

private theorem decodeVarint2Env_of_some {bs : List (BitVec 8)} {p : BitVec 64 × List (BitVec 8)}
    {evs : List AllocEvent} (hdv : decodeVarint bs = some p) (h : DecodeVarint2Env bs evs) :
    evs = [] := by
  change DecodeVarintSliceEnv bs evs at h
  simpa [DecodeVarintSliceEnv, decodeVarintSliceEvents, hdv] using h

private theorem decodeVarint2Env_of_none {bs : List (BitVec 8)} {evs : List AllocEvent}
    (hdv : decodeVarint bs = none) (h : DecodeVarint2Env bs evs) :
    evs = rustAllocEvents 72 8 := by
  change DecodeVarintSliceEnv bs evs at h
  simpa [DecodeVarintSliceEnv, decodeVarintSliceEvents, hdv] using h

private theorem skipField3Env_of_some {g : SkipFieldGhost} {rest' : List (BitVec 8)}
    {evs : List AllocEvent}
    (hsf : skipField (2 * g.bs.length + 2) g.depth g.tag g.wt g.bs = some rest')
    (h : SkipField3Env g evs) :
    evs = [] := by
  change SkipFieldEnv g evs at h
  simpa [SkipFieldEnv, skipFieldEventsCore, hsf] using h

private theorem skipField3Env_of_none {g : SkipFieldGhost} {evs : List AllocEvent}
    (hsf : skipField (2 * g.bs.length + 2) g.depth g.tag g.wt g.bs = none)
    (h : SkipField3Env g evs) :
    evs = rustAllocEvents 72 8 := by
  change SkipFieldEnv g evs at h
  simpa [SkipFieldEnv, skipFieldEventsCore, hsf] using h

theorem FitsEnv.chainParams_decodeErrorFrom {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x : ChainParamsMergeGhost} (hFit : FitsEnv M lim st (ChainParamsMergeEnv x)) :
    FitsEnv M lim st DecodeErrorFromEnv := by
  intro evs he
  rw [he]
  exact hFit _ (.err .fromOnly)

theorem FitsEnv.chainParams_decodeVarint2 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x : ChainParamsMergeGhost} (bs : List (BitVec 8))
    (hFit : FitsEnv M lim st (ChainParamsMergeEnv x)) :
    FitsEnv M lim st (DecodeVarint2Env bs) := by
  intro evs he
  cases hdv : decodeVarint bs with
  | none =>
    rw [decodeVarint2Env_of_none hdv he]
    exact hFit _ (.err .fromOnly)
  | some p =>
    rw [decodeVarint2Env_of_some hdv he]
    exact hFit _ .ok

theorem FitsEnv.chainParams_skipField3 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x : ChainParamsMergeGhost} (g : SkipFieldGhost)
    (hFit : FitsEnv M lim st (ChainParamsMergeEnv x)) :
    FitsEnv M lim st (SkipField3Env g) := by
  intro evs he
  cases hsf : skipField (2 * g.bs.length + 2) g.depth g.tag g.wt g.bs with
  | none =>
    rw [skipField3Env_of_none hsf he]
    exact hFit _ (.err .fromOnly)
  | some rest' =>
    rw [skipField3Env_of_some hsf he]
    exact hFit _ .ok

theorem FitsEnv.chainParams_decodeErrorPush0 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x : ChainParamsMergeGhost} (hFit : FitsEnv M lim st (ChainParamsMergeEnv x)) :
    FitsEnv M lim (M.stepEvents (rustAllocEvents 72 8) st) (DecodeErrorPushEnv 0) :=
  fun evs_p hp =>
    ((fitsEvents_append M lim (rustAllocEvents 72 8) evs_p st).mp
      (hFit (rustAllocEvents 72 8 ++ evs_p) (.err (.fromPush hp)))).2

/-- Envelope-parameterized budget-threaded contract of
`prost::encoding::message::merge::<spqr::proto::pq_ratchet::ChainParams, &mut &[u8]>` (Block `294`). -/
def chainParamsMergeSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : ChainParamsMergeGhost → List AllocEvent → Prop) :
    Spec (ChainParamsMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      chainParamsPBAt x.msgPtr x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp chainParamsMergeStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp chainParamsMergeStack ∗
      match (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chainParamsPBAt x.msgPtr m' ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 1⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : ChainParamsPB, chainParamsPBAt x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of
`prost::encoding::message::merge::<spqr::proto::pq_ratchet::ChainParams, &mut &[u8]>`
(Block `294`, `onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def chainParamsMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainParamsMergeGhost × M.σ) :=
  chainParamsMergeSpecOfEnv A lim ChainParamsMergeEnv ChainParamsMergePostEnv

theorem subroutine_ok_chainParamsMergeOfEnv {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    {Pre₁ Post₁ Pre₂ Post₂ : ChainParamsMergeGhost → List AllocEvent → Prop}
    (hpre : ∀ x evs, Pre₁ x evs → Pre₂ x evs)
    (hpost : ∀ x evs, Post₁ x evs → Post₂ x evs)
    (h : subroutine_ok prog entry (chainParamsMergeSpecOfEnv A lim Pre₁ Post₁)) :
    subroutine_ok prog entry (chainParamsMergeSpecOfEnv A lim Pre₂ Post₂) := by
  refine subroutine_ok_mono h
    (fun ⟨x, st⟩ R s0 hp => ?_)
    (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · dsimp only [chainParamsMergeSpecOfEnv] at hp ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1, hp.1.2.2.2.2.mono (hpre x)⟩, hp.2⟩
  · dsimp only [chainParamsMergeSpecOfEnv] at hq ⊢
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (Entails.sepExists_mono fun evs =>
        Entails.pure_left fun h1 => Entails.pure_right (hpost x evs h1) (Entails.of_eq rfl)))))) hq

theorem subroutine_ok_withLsCodeLoaded_chainParamsMergeOfEnv {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {pl : Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64}
    {Pre₁ Post₁ Pre₂ Post₂ : ChainParamsMergeGhost → List AllocEvent → Prop}
    (hpre : ∀ x evs, Pre₁ x evs → Pre₂ x evs)
    (hpost : ∀ x evs, Post₁ x evs → Post₂ x evs)
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (chainParamsMergeSpecOfEnv A lim Pre₁ Post₁))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (chainParamsMergeSpecOfEnv A lim Pre₂ Post₂)) := by
  refine subroutine_ok_mono h
    (fun ⟨x, st⟩ R s0 hp => ?_)
    (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · obtain ⟨hcl, hp⟩ := extract_withLsCodeLoaded hp
    dsimp only [withLsCodeLoaded, chainParamsMergeSpecOfEnv] at hp ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1, hp.1.2.2.2.2.mono (hpre x)⟩, hp.2⟩
  · dsimp only [withLsCodeLoaded, chainParamsMergeSpecOfEnv] at hq ⊢
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (Entails.sepExists_mono fun evs =>
        Entails.pure_left fun h1 => Entails.pure_right (hpost x evs h1) (Entails.of_eq rfl)))))) hq

theorem subroutine_ok_withLsCodeRoLoaded_chainParamsMergeOfEnv {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {pl : Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64}
    {Pre₁ Post₁ Pre₂ Post₂ : ChainParamsMergeGhost → List AllocEvent → Prop}
    (hpre : ∀ x evs, Pre₁ x evs → Pre₂ x evs)
    (hpost : ∀ x evs, Post₁ x evs → Post₂ x evs)
    (h : subroutine_ok prog entry (withLsCodeRoLoaded pl (chainParamsMergeSpecOfEnv A lim Pre₁ Post₁))) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl (chainParamsMergeSpecOfEnv A lim Pre₂ Post₂)) := by
  refine subroutine_ok_mono h
    (fun ⟨x, st⟩ R s0 hp => ?_)
    (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · obtain ⟨hcro, hp⟩ := extract_withLsCodeRoLoaded hp
    dsimp only [withLsCodeRoLoaded, chainParamsMergeSpecOfEnv] at hp ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1, hp.1.2.2.2.2.mono (hpre x)⟩, hp.2⟩
  · dsimp only [withLsCodeRoLoaded, chainParamsMergeSpecOfEnv] at hq ⊢
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (Entails.sepExists_mono fun evs =>
        Entails.pure_left fun h1 => Entails.pure_right (hpost x evs h1) (Entails.of_eq rfl)))))) hq

/-! ## 2. Loop & Error-Exit Separation-Logic Bundles and Shared Exit/Tag-1 Steps -/

/-- Budget-threaded loop-header separation-logic bundle at `+0x0a0` (`(blkPl_294).base + 160#64`). -/
abbrev chainParamsBudgetLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64) (m : ChainParamsPB) (bs cur : List (BitVec 8)) : SepProp :=
  chainParamsPBAt msgPtr m ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗
    A.pool lim st s ∗ memRegion (s0.sp - 96#64) 48 ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗ skipBelow3 s0.sp 99

/-- Budget-threaded error-exit separation-logic bundle at `+0x068`, `+0x074`, `+0x220` of Block `294`. -/
abbrev chainParamsBudgetErrFrame {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64) (m : ChainParamsPB) (bs : List (BitVec 8)) : SepProp :=
  chainParamsPBAt msgPtr m ∗ (bufRef ↦₆₄ slot) ∗ memRegion slot 16 ∗ (ptr ↦ₛ bs) ∗
    A.pool lim st s ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

/-- `SepWPp` panic postcondition matched to `wpp_init` on budget-threaded `onPanic = ⌜False⌝` specs. -/
abbrev WppBudgetPanic {α : Type} (spec : Spec α) (x : α) (R : SepProp) (s0 : State)
    (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R)

theorem wppBudgetPanic_false {α : Type} {spec : Spec α} {x : α} {R : SepProp} {s0 sf : State}
    {F : SepProp} :
    WppBudgetPanic spec x R s0 sf (⌜False⌝ ∗ F) := by
  intro hm
  rw [sepConj_assoc] at hm
  exact False.elim (not_satisfies_false_sepConj hm)

/-- Placed shared exit from `+0x074` (`(blkPl_294).base + 116#64`) when `x1 = err ≠ 0#64` owns
`decodeErrorAtStackLen A.repAlloc err 0`. -/
theorem chainParams_err0_ret_exit_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : ChainParamsMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : ChainParamsPB} {err : BitVec 64}
    (hnone : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hevs : ∃ evs, ChainParamsErrEnv evs ∧ st_cur = M.stepEvents evs st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_294).base + 116#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (herr : err ≠ 0#64) (hcs : HighCalleeSaved s0 s) :
    SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err 0 ∗ memRegion (s0.sp - 96#64) 48 ∗
        skipBelow3 s0.sp 99 ∗
        chainParamsBudgetErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chainParamsMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (chainParamsMergeSpec A lim) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  rcases hevs with ⟨evs, hevs_err, rfl⟩
  have hevs_post : ChainParamsMergePostEnv x evs := by
    simp only [ChainParamsMergePostEnv, hnone]
    exact hevs_err
  apply SepWPp.of_sepWP_ret
  unfold WppPost chainParamsMergeSpec chainParamsMergeSpecOfEnv
  simp only [hnone, stackAt_skipField3 _ 99 (by decide), chainParamsBudgetErrFrame,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx1]
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A.repAlloc err) (by sep_focus)
  apply SepWP.fold (chainParamsPBAt_entails_exists x.msgPtr m) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  wp_done

/-- Code-loaded placed shared exit from `+0x068` (`(blkPl_294).base + 104#64`): calls
`DecodeError::from` on `(s0.sp - 96#64, w, st0)` and returns at `+0x070..+0x088`. -/
theorem chainParams_from_err_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : ChainParamsMergeGhost} {st0 : M.σ} {R : SepProp}
    {s0 s : State} {m : ChainParamsPB} {w : BitVec 64}
    (hFit : FitsEnv M lim st0 (ChainParamsMergeEnv x))
    (hnone : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_294).base + 104#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hcs : HighCalleeSaved s0 s)
    (hinv : LibsignalCodeLoaded lsmpl s.mem) :
    SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 96#64) ↦₆₄ w) ∗ memRegion (s0.sp - 88#64) 40 ∗
        skipBelow3 s0.sp 99 ∗
        chainParamsBudgetErrFrame A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chainParamsMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (chainParamsMergeSpec A lim) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscl_mm (mid := lsmpl.base 261) hinv
  conv => arg 4; rw [skipBelow3_err s0.sp 99 (by decide), chainParamsBudgetErrFrame]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 261)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscl_mm (spec := decodeErrorFromBudgetSpec M A lim)
    (x := (s0.sp - 96#64, w, st0))
    (ret_pc := (blkPl_294).base + 112#64) hFromCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp], hw, FitsEnv.chainParams_decodeErrorFrom hFit⟩ (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm _hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hspm hx19 hx20 hx21 hx22 hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp hvregs_m
  apply SepWPp.of_sepWP_ret
  unfold WppPost chainParamsMergeSpec chainParamsMergeSpecOfEnv
  simp only [decodeErrorFromBudgetSpec, hnone, stackAt_skipField3 _ 99 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, htr, hsp, hspm]
  apply SepWP.exists_elim; intro evs_f
  wp_focus_pure; rintro ⟨_herr, htrm⟩
  wp_focus_pure; intro hevs_f
  have hevs_post : ChainParamsMergePostEnv x evs_f := by
    simp only [ChainParamsMergePostEnv, hnone]
    rw [hevs_f]
    exact .fromOnly
  conv => arg 4; simp only [arm64_norm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 99 (by decide)) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48 s0.sp) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A.repAlloc _) (by sep_focus)
  apply SepWP.fold (chainParamsPBAt_entails_exists x.msgPtr m) (by sep_focus)
  wp_done

/-- Code-loaded placed shared exit from `+0x220` (`(blkPl_294).base + 544#64`): calls
`DecodeError::push` on `(s0.sp - 96#64, err, 0, M.stepEvents (rustAllocEvents 72 8) st0)` and
returns at `+0x224..+0x23c`. -/
theorem chainParams_push_err_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hPushCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    {x : ChainParamsMergeGhost} {st0 : M.σ} {R : SepProp}
    {s0 s : State} {m : ChainParamsPB} {err : BitVec 64}
    (hFit : FitsEnv M lim st0 (ChainParamsMergeEnv x))
    (hnone : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_294).base + 544#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 96#64)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeLoaded lsmpl s.mem) :
    SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 96#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗
        memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 99 ∗
        chainParamsBudgetErrFrame A lim (M.stepEvents (rustAllocEvents 72 8) st0) s0 s
          x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chainParamsMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (chainParamsMergeSpec A lim) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscl_mm (mid := lsmpl.base 257) hinv
  conv => arg 4; rw [skipBelow3_err s0.sp 99 (by decide), chainParamsBudgetErrFrame]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 257)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscl_mm (spec := decodeErrorPushBudgetSpec M A lim)
    (x := (s0.sp - 96#64, err, 0, M.stepEvents (rustAllocEvents 72 8) st0))
    (ret_pc := (blkPl_294).base + 548#64) hPushCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp, hx0], by decide, FitsEnv.chainParams_decodeErrorPush0 hFit⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm _hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hspm hx19 hx20 hx21 hx22 hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp hvregs_m
  apply SepWPp.of_sepWP_ret
  unfold WppPost chainParamsMergeSpec chainParamsMergeSpecOfEnv
  simp only [decodeErrorPushBudgetSpec, hnone, stackAt_skipField3 _ 99 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, htr, hsp, hspm]
  apply SepWP.exists_elim; intro evs_p
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_p
  have hevs_post : ChainParamsMergePostEnv x (rustAllocEvents 72 8 ++ evs_p) := by
    simp only [ChainParamsMergePostEnv, hnone]
    exact .fromPush hevs_p
  have hst_eq :
      M.stepEvents evs_p (M.stepEvents (rustAllocEvents 72 8) st0) =
        M.stepEvents (rustAllocEvents 72 8 ++ evs_p) st0 :=
    (M.stepEvents_append (rustAllocEvents 72 8) evs_p st0).symm
  conv => arg 4; simp only [hst_eq, arm64_norm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 99 (by decide)) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  apply SepWP.fold (decodeErrorWith_one_entails_le1 A.repAlloc err) (by sep_focus)
  apply SepWP.fold (chainParamsPBAt_entails_exists x.msgPtr m) (by sep_focus)
  apply SepWP.fold (pointsTo64_memRegion40_entails_48 s0.sp err) (by sep_focus)
  wp_done

/-- Code-loaded placed step lemma for unknown field tags (`tag ≠ 1 ∧ tag ≠ 2`) at `+0x08c`
(`(blkPl_294).base + 140#64`). -/
theorem chainParams_skip_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hSkipCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    {x : ChainParamsMergeGhost} {st0 : M.σ} {R : SepProp}
    {s0 s : State} {m : ChainParamsPB} {rest : List (BitVec 8)} {tag : Nat} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st0 (ChainParamsMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 98 tag iwt rest = none →
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 98 tag iwt rest = some rest' →
      s'.pc = (blkPl_294).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeLoaded lsmpl s'.mem →
      SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s'
        (chainParamsBudgetLoopPre A lim st0 s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (chainParamsMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (chainParamsMergeSpec A lim) (x, st0) R s0))
    (hpc : s.pc = (blkPl_294).base + 140#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeLoaded lsmpl s.mem) :
    SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s
      (chainParamsBudgetLoopPre A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chainParamsMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (chainParamsMergeSpec A lim) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let g : SkipFieldGhost := ⟨iwt, tag, 98, x.bufRef, x.slot, restPtr, rest⟩
  apply SepWPp.of_sepWP_lscl_mm (mid := lsmpl.base 263) hinv
  conv => arg 4; rw [chainParamsBudgetLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_99_eq_stackAt_98 s0.sp]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 263)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscl_mm (spec := skipField3Spec A lim)
    (x := (g, st0))
    (ret_pc := (blkPl_294).base + 152#64) hSkipCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl
    ⟨by simp only [arm64_norm, g, hsp, hx0, setWidth8_ofNat64_wt],
     by simp only [arm64_norm, g, hsp, hx1], htag_lt,
     by simp only [arm64_norm, g, hsp, hx19],
     by simp only [arm64_norm, g, hsp], (by decide : 98 < 2 ^ 32), hrest_lt,
     FitsEnv.chainParams_skipField3 g hFit⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 98 tag iwt rest with
  | none =>
    have hnone := hnone_of_sf hsf
    apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 116#64) hinvm
    (conv => arg 4; simp only [skipField3Spec, g, hsf, ← skipBelow3_99_eq_stackAt_98,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_sf
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_sf
    wp_focus_pure; intro hsm0
    have hevs_eq : evs_sf = rustAllocEvents 72 8 := skipField3Env_of_none hsf hevs_sf
    conv => arg 4; simp only [arm64_norm, hsp]
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    wp_steps_sync_pool ((blkPl_294).base + 116#64)
    simp only [State.setMem_setMem]
    wp_reach; intro _hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [chainParamsBudgetErrFrame]; sep_ac_rfl))
      (chainParams_err0_ret_exit_placed hnone
        ⟨evs_sf, hevs_eq ▸ .fromOnly, rfl⟩ hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) hsm0
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩)
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 160#64) hinvm
    (conv => arg 4; simp only [skipField3Spec, g, hsf, ← skipBelow3_99_eq_stackAt_98,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_sf
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_sf
    wp_focus_pure; intro hsm0
    have hevs_nil : evs_sf = [] := skipField3Env_of_some hsf hevs_sf
    subst hevs_nil
    conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps_sync_pool ((blkPl_294).base + 160#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [chainParamsBudgetLoopPre]; sep_ac_rfl))
      (hcont rest' _ hsf
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm')

/-- Code-loaded placed shared exit for tag 1 (`max_jump`) from `+0x1bc` (`(blkPl_294).base + 444#64`). -/
theorem chainParams_tag1_push_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hPushCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    {x : ChainParamsMergeGhost} {st0 : M.σ} {R : SepProp}
    {s0 s : State} {m : ChainParamsPB} {err : BitVec 64}
    (hFit : FitsEnv M lim st0 (ChainParamsMergeEnv x))
    (hnone : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_294).base + 444#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx8 : s.readReg64 (Reg.gpr 8#5) = err)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeLoaded lsmpl s.mem) :
    SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err 0 ∗ memRegion (s0.sp - 96#64) 48 ∗
        skipBelow3 s0.sp 99 ∗
        chainParamsBudgetErrFrame A lim (M.stepEvents (rustAllocEvents 72 8) st0) s0 s
          x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chainParamsMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (chainParamsMergeSpec A lim) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let s2 : State :=
    ((((s.writeReg64 (Reg.gpr 1#5)
        (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_294.ρ "spqr:.rodata..Lanon.21")).setPC
        ((blkPl_294).base + 452#64)).writeReg64 (Reg.gpr 3#5)
        (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_294.ρ "spqr:.rodata.cst8+0x0")).setPC
        ((blkPl_294).base + 460#64))
  have hpool_s2 :
      A.pool lim (M.stepEvents (rustAllocEvents 72 8) st0) s =
        A.pool lim (M.stepEvents (rustAllocEvents 72 8) st0) s2 := by
    simp only [s2, RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64]
  apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 544#64) hinv
  conv => arg 4; rw [sepConj_memRegion_48_split_96, chainParamsBudgetErrFrame]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_stk0
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_294_pairStep_0x1bc _ _ rfl hpc hrun
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_294_pairStep_0x1c4 _ _ rfl rfl (by simp only [arm64_norm, hrun])
  change SepWP _ _ s2 _ _ _
  conv => arg 4; rw [hpool_s2]
  dsimp only [s2]
  wp_steps_sync_pool ((blkPl_294).base + 544#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.weaken_pre (by dsimp only [chainParamsBudgetErrFrame]; sep_entail)
    (chainParams_push_err_exit_cl_placed hPushCall hFit hnone herr hsp_align
      (by simp only [s2, arm64_norm]) (by simp only [s2, arm64_norm, hrun]) (by simp only [s2, arm64_norm, hsp])
      (by simp only [s2, arm64_norm, htr]) (by simp only [s2, arm64_norm, hsp])
      ⟨by simp only [s2, arm64_norm, hx23], by simp only [s2, arm64_norm, hx24],
       by simp only [s2, arm64_norm, hx25], by simp only [s2, arm64_norm, hx26],
       by simp only [s2, arm64_norm, hx27], by simp only [s2, arm64_norm, hx28],
       by simp only [s2, arm64_norm, hvregs]⟩ hinv)

/-- Code-loaded placed step lemma for tag 1 (`max_jump`) at `+0x104` (`(blkPl_294).base + 260#64`)
when `iwt ≠ .varint`. -/
theorem chainParams_tag1_wt_err_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    {x : ChainParamsMergeGhost} {st0 : M.σ} {R : SepProp}
    {s0 s : State} {m : ChainParamsPB} {rest : List (BitVec 8)} {iwt : WireType}
    (hFit : FitsEnv M lim st0 (ChainParamsMergeEnv x))
    (hiwt : iwt ≠ .varint) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hpc : s.pc = (blkPl_294).base + 260#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeLoaded lsmpl s.mem) :
    SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s
      (chainParamsBudgetLoopPre A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chainParamsMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (chainParamsMergeSpec A lim) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hcbnz := iwt_cbnz_true_of_ne_varint hiwt
  apply SepWPp.of_sepWP_lscl_mm (mid := lsmpl.base 261) hinv
  conv => arg 4; rw [chainParamsBudgetLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    sliceCursorAt, memRegion_48_wtErr96 s0.sp, skipBelow3_err s0.sp 99 (by decide)]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
  wp_steps_sync_pool (lsmpl.base 261)
  simp only [State.setMem_setMem]
  apply SepWP.fold (wtErr96_entails_memRegion40 s0.sp _ _) (by sep_focus)
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscl_mm (spec := decodeErrorFromBudgetSpec M A lim)
    (x := (s0.sp - 96#64, 0x8000000000000006#64, st0))
    (ret_pc := (blkPl_294).base + 440#64) hFromCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp], (by decide : KindNoHeap 0x8000000000000006#64),
      FitsEnv.chainParams_decodeErrorFrom hFit⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 444#64) hinvm
  (conv => arg 4; simp only [decodeErrorFromBudgetSpec, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro evs_f
  wp_focus_pure; rintro ⟨hve_ne, htrm⟩
  wp_focus_pure; intro hevs_f
  rw [hevs_f]
  conv => arg 4; simp only [arm64_norm, hsp]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 99 (by decide)) (by sep_focus)
  wp_steps_sync_pool ((blkPl_294).base + 444#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinvm
  refine SepWPp.weaken_pre (by dsimp only [chainParamsBudgetErrFrame]; sep_entail)
    (chainParams_tag1_push_exit_cl_placed hPushCall hFit hnone hve_ne hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm)

/-- Code-loaded placed step lemma for tag 1 (`max_jump`) at `+0x104` (`(blkPl_294).base + 260#64`)
when `iwt = .varint`. -/
theorem chainParams_tag1_varint_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hPushCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChainParamsMergeGhost} {st0 : M.σ} {R : SepProp}
    {s0 s : State} {m : ChainParamsPB} {rest : List (BitVec 8)} {limit : Nat}
    (hFit : FitsEnv M lim st0 (ChainParamsMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_dv : decodeVarint rest = none →
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_294).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeLoaded lsmpl s'.mem →
      SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s'
        (chainParamsBudgetLoopPre A lim st0 s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with maxJump := v.truncate 32 } x.bs rest')
        (WppPost (chainParamsMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (chainParamsMergeSpec A lim) (x, st0) R s0))
    (hpc : s.pc = (blkPl_294).base + 260#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeLoaded lsmpl s.mem) :
    SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s
      (chainParamsBudgetLoopPre A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chainParamsMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (chainParamsMergeSpec A lim) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply SepWPp.of_sepWP_lscl_mm (mid := lsmpl.base 291) hinv
  conv => arg 4; rw [chainParamsBudgetLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_leaf s0.sp 99 (by decide)]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscl_mm (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, st0))
    (ret_pc := (blkPl_294).base + 272#64) hVarintCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp, hx19], hrest_lt, FitsEnv.chainParams_decodeVarint2 rest hFit⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hdv : decodeVarint rest with
  | none =>
    have hnone := hnone_of_dv hdv
    apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 444#64) hinvm
    (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_dv
    wp_focus_pure; intro hsm0
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_dv
    wp_focus_pure; intro hsm1
    rw [decodeVarint2Env_of_none hdv hevs_dv]
    conv => arg 4; simp only [arm64_norm, hsp]
    have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp 99 (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    wp_steps_sync_pool ((blkPl_294).base + 444#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm
    refine SepWPp.weaken_pre (by dsimp only [chainParamsBudgetErrFrame]; sep_entail)
      (chainParams_tag1_push_exit_cl_placed hPushCall hFit hnone hsm1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm)
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
    apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 160#64) hinvm
    (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv, chainParamsPBAt, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_dv
    wp_focus_pure; rintro ⟨hsm0, hsm1⟩
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_dv
    have hevs_nil : evs_dv = [] := decodeVarint2Env_of_some hdv hevs_dv
    subst hevs_nil
    conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp 99 (by decide)) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps_sync_pool ((blkPl_294).base + 160#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm
    refine SepWPp.weaken_pre (by dsimp only [chainParamsBudgetLoopPre, chainParamsPBAt]; sep_entail)
      (hcont v rest' _ hdv
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm)

/-! ## 3. Tag 2, Loop Exit, Key Decode, Loop Induction, and Top-Level Block `294` Verification -/

/-- Code-loaded placed shared exit for tag 2 (`max_ooo_keys`) from `+0x200` (`(blkPl_294).base + 512#64`). -/
theorem chainParams_tag2_push_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hPushCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    {x : ChainParamsMergeGhost} {st0 : M.σ} {R : SepProp}
    {s0 s : State} {m : ChainParamsPB} {err : BitVec 64}
    (hFit : FitsEnv M lim st0 (ChainParamsMergeEnv x))
    (hnone : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_294).base + 512#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx8 : s.readReg64 (Reg.gpr 8#5) = err)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeLoaded lsmpl s.mem) :
    SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err 0 ∗ memRegion (s0.sp - 96#64) 48 ∗
        skipBelow3 s0.sp 99 ∗
        chainParamsBudgetErrFrame A lim (M.stepEvents (rustAllocEvents 72 8) st0) s0 s
          x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chainParamsMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (chainParamsMergeSpec A lim) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 544#64) hinv
  conv => arg 4; rw [sepConj_memRegion_48_split_96, chainParamsBudgetErrFrame]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_stk0
  wp_steps_sync_pool ((blkPl_294).base + 544#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.weaken_pre (by dsimp only [chainParamsBudgetErrFrame]; sep_entail)
    (chainParams_push_err_exit_cl_placed hPushCall hFit hnone herr hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
      ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24],
       by simp only [arm64_norm, hx25], by simp only [arm64_norm, hx26],
       by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28],
       by simp only [arm64_norm, hvregs]⟩ hinv)

/-- Code-loaded placed step lemma for tag 2 (`max_ooo_keys`) at `+0x0e4` (`(blkPl_294).base + 228#64`)
when `iwt ≠ .varint`. -/
theorem chainParams_tag2_wt_err_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    {x : ChainParamsMergeGhost} {st0 : M.σ} {R : SepProp}
    {s0 s : State} {m : ChainParamsPB} {rest : List (BitVec 8)} {iwt : WireType}
    (hFit : FitsEnv M lim st0 (ChainParamsMergeEnv x))
    (hiwt : iwt ≠ .varint) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hpc : s.pc = (blkPl_294).base + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeLoaded lsmpl s.mem) :
    SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s
      (chainParamsBudgetLoopPre A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chainParamsMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (chainParamsMergeSpec A lim) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hcbnz := iwt_cbnz_true_of_ne_varint hiwt
  apply SepWPp.of_sepWP_lscl_mm (mid := lsmpl.base 261) hinv
  conv => arg 4; rw [chainParamsBudgetLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    sliceCursorAt, memRegion_48_wtErr96 s0.sp, skipBelow3_err s0.sp 99 (by decide)]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
  wp_steps_sync_pool (lsmpl.base 261)
  simp only [State.setMem_setMem]
  apply SepWP.fold (wtErr96_entails_memRegion40 s0.sp _ _) (by sep_focus)
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscl_mm (spec := decodeErrorFromBudgetSpec M A lim)
    (x := (s0.sp - 96#64, 0x8000000000000006#64, st0))
    (ret_pc := (blkPl_294).base + 508#64) hFromCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp], (by decide : KindNoHeap 0x8000000000000006#64),
      FitsEnv.chainParams_decodeErrorFrom hFit⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 512#64) hinvm
  (conv => arg 4; simp only [decodeErrorFromBudgetSpec, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro evs_f
  wp_focus_pure; rintro ⟨hve_ne, htrm⟩
  wp_focus_pure; intro hevs_f
  rw [hevs_f]
  conv => arg 4; simp only [arm64_norm, hsp]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 99 (by decide)) (by sep_focus)
  wp_steps_sync_pool ((blkPl_294).base + 512#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinvm
  refine SepWPp.weaken_pre (by dsimp only [chainParamsBudgetErrFrame]; sep_entail)
    (chainParams_tag2_push_exit_cl_placed hPushCall hFit hnone hve_ne hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm)

/-- Code-loaded placed step lemma for tag 2 (`max_ooo_keys`) at `+0x0e4` (`(blkPl_294).base + 228#64`)
when `iwt = .varint`. -/
theorem chainParams_tag2_varint_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hPushCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChainParamsMergeGhost} {st0 : M.σ} {R : SepProp}
    {s0 s : State} {m : ChainParamsPB} {rest : List (BitVec 8)} {limit : Nat}
    (hFit : FitsEnv M lim st0 (ChainParamsMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_dv : decodeVarint rest = none →
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_294).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeLoaded lsmpl s'.mem →
      SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s'
        (chainParamsBudgetLoopPre A lim st0 s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with maxOooKeys := v.truncate 32 } x.bs rest')
        (WppPost (chainParamsMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (chainParamsMergeSpec A lim) (x, st0) R s0))
    (hpc : s.pc = (blkPl_294).base + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeLoaded lsmpl s.mem) :
    SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s
      (chainParamsBudgetLoopPre A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chainParamsMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (chainParamsMergeSpec A lim) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply SepWPp.of_sepWP_lscl_mm (mid := lsmpl.base 291) hinv
  conv => arg 4; rw [chainParamsBudgetLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_leaf s0.sp 99 (by decide)]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscl_mm (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, st0))
    (ret_pc := (blkPl_294).base + 240#64) hVarintCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp, hx19], hrest_lt, FitsEnv.chainParams_decodeVarint2 rest hFit⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hdv : decodeVarint rest with
  | none =>
    have hnone := hnone_of_dv hdv
    apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 512#64) hinvm
    (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_dv
    wp_focus_pure; intro hsm0
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_dv
    wp_focus_pure; intro hsm1
    rw [decodeVarint2Env_of_none hdv hevs_dv]
    conv => arg 4; simp only [arm64_norm, hsp]
    have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp 99 (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    wp_steps_sync_pool ((blkPl_294).base + 512#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm
    refine SepWPp.weaken_pre (by dsimp only [chainParamsBudgetErrFrame]; sep_entail)
      (chainParams_tag2_push_exit_cl_placed hPushCall hFit hnone hsm1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm)
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
    apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 160#64) hinvm
    (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv, chainParamsPBAt, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_dv
    wp_focus_pure; rintro ⟨hsm0, hsm1⟩
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_dv
    have hevs_nil : evs_dv = [] := decodeVarint2Env_of_some hdv hevs_dv
    subst hevs_nil
    conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp 99 (by decide)) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps_sync_pool ((blkPl_294).base + 160#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm
    refine SepWPp.weaken_pre (by dsimp only [chainParamsBudgetLoopPre, chainParamsPBAt]; sep_entail)
      (hcont v rest' _ hdv
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm)

/-- Code-loaded placed loop-exit step at `+0x0a0` (`(blkPl_294).base + 160#64`) when `cur.length ≤ limit`. -/
theorem chainParams_loop_le_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : ChainParamsMergeGhost} {st0 : M.σ} {R : SepProp}
    {s0 s : State} {m : ChainParamsPB} {cur : List (BitVec 8)} {limit : Nat}
    (hFit : FitsEnv M lim st0 (ChainParamsMergeEnv x))
    (hle_lim : cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hlim_lt : limit < 2 ^ 63)
    (hres_cur : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
      (mergeLoopBin ChainParamsPB.mergeField (cur.length - limit) m cur limit 98).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hpc : s.pc = (blkPl_294).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeLoaded lsmpl s.mem) :
    SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s
      (chainParamsBudgetLoopPre A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (chainParamsMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (chainParamsMergeSpec A lim) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by
      rw [← heq_lim]; exact hcur_suf.symm
    have hsome : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
        some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    have hevs_post : ChainParamsMergePostEnv x [] := by
      simp only [ChainParamsMergePostEnv, hsome]
    apply SepWPp.of_sepWP_ret
    unfold WppPost chainParamsMergeSpec chainParamsMergeSpecOfEnv
    simp only [hsome, stackAt_skipField3 _ 99 (by decide), chainParamsBudgetLoopPre,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp]
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    conv => arg 4; rw [show st0 = M.stepEvents [] st0 from rfl]
    wp_done
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim, Option.map_none]
    apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 104#64) hinv
    conv => arg 4; rw [chainParamsBudgetLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_split_96 s0.sp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0
    wp_steps_sync_pool ((blkPl_294).base + 104#64)
    simp only [State.setMem_setMem]
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    wp_reach; intro hinv
    refine SepWPp.weaken_pre (by dsimp only [chainParamsBudgetErrFrame]; sep_entail)
      (chainParams_from_err_exit_cl_placed hFromCall hFit hnone
        (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
        (by simp only [arm64_norm, htr])
        ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24],
         by simp only [arm64_norm, hx25], by simp only [arm64_norm, hx26],
         by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28],
         by simp only [arm64_norm, hvregs]⟩ hinv)

/-- Code-loaded placed key-decode step at `+0x0a0` (`(blkPl_294).base + 160#64`) when `¬ cur.length ≤ limit`. -/
theorem chainParams_decode_key_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChainParamsMergeGhost} {st0 : M.σ} {R : SepProp}
    {s0 s : State} {m : ChainParamsPB} {cur : List (BitVec 8)} {limit : Nat}
    (hFit : FitsEnv M lim st0 (ChainParamsMergeEnv x))
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hres_cur : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
      (mergeLoopBin ChainParamsPB.mergeField (cur.length - limit) m cur limit 98).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_294).base + 212#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeLoaded lsmpl s'.mem →
      SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s'
        (chainParamsBudgetLoopPre A lim st0 s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (chainParamsMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (chainParamsMergeSpec A lim) (x, st0) R s0))
    (hpc : s.pc = (blkPl_294).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeLoaded lsmpl s.mem) :
    SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s
      (chainParamsBudgetLoopPre A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (chainParamsMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (chainParamsMergeSpec A lim) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  apply SepWPp.of_sepWP_lscl_mm (mid := lsmpl.base 291) hinv
  conv => arg 4; rw [chainParamsBudgetLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, skipBelow3_leaf s0.sp 99 (by decide)]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscl_mm (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, st0))
    (ret_pc := (blkPl_294).base + 180#64) hVarintCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp, hx19], hcur_lt, FitsEnv.chainParams_decodeVarint2 cur hFit⟩
    (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [hres_cur, mergeLoopBin_of_decodeVarint_none protoPrefixStep_chainParamsPB_mergeField hgt_lim hd, Option.map_none]
    apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 116#64) hinvm
    (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_dv
    wp_focus_pure; intro hsm0
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_dv
    wp_focus_pure; intro hsm1
    have hevs_eq : evs_dv = rustAllocEvents 72 8 := decodeVarint2Env_of_none hd hevs_dv
    conv => arg 4; simp only [arm64_norm, hsp]
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp 99 (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    wp_steps_sync_pool ((blkPl_294).base + 116#64)
    simp only [State.setMem_setMem]
    wp_reach; intro _hinvm'
    refine SepWPp.weaken_pre (by dsimp only [chainParamsBudgetErrFrame]; sep_entail)
      (chainParams_err0_ret_exit_placed hnone
        ⟨evs_dv, hevs_eq ▸ .fromOnly, rfl⟩ hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) hsm1
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩)
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
    have hrest_suf : IsDropSuffix x.bs rest :=
      suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
        rw [hres_cur, mergeLoopBin_of_key_ge protoPrefixStep_chainParamsPB_mergeField hgt_lim hd hk_ge, Option.map_none]
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 104#64) hinvm
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro evs_dv
      wp_focus_pure; rintro ⟨hsm0, hsm1⟩
      wp_focus_pure; intro htrm
      wp_focus_pure; intro hevs_dv
      have hevs_nil : evs_dv = [] := decodeVarint2Env_of_some hd hevs_dv
      subst hevs_nil
      conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp 99 (by decide)) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2 s0.sp]
      conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1
      wp_steps_sync_pool ((blkPl_294).base + 104#64)
      simp only [State.setMem_setMem]
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 := pointsTo64_memRegion32_entails_40 s0.sp key
      rw [← bv_sub_add_lit s0.sp 96 8] at h40
      apply SepWP.fold h40 (by sep_focus)
      wp_reach; intro hinvm
      refine SepWPp.weaken_pre (by dsimp only [chainParamsBudgetErrFrame]; sep_entail)
        (chainParams_from_err_exit_cl_placed hFromCall hFit hnone
          (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
          (by simp only [arm64_norm, htrm, htr])
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
           by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
           by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
           by simp only [arm64_norm, hvregs_m]⟩ hinvm)
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          rw [hres_cur, mergeLoopBin_of_wt_none protoPrefixStep_chainParamsPB_mergeField hgt_lim hd hk_ge hwt, Option.map_none]
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 104#64) hinvm
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_dv
        wp_focus_pure; rintro ⟨hsm0, hsm1⟩
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_dv
        have hevs_nil : evs_dv = [] := decodeVarint2Env_of_some hd hevs_dv
        subst hevs_nil
        conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 99 (by decide)) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2 s0.sp]
        conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1
        wp_steps_sync_pool ((blkPl_294).base + 104#64)
        simp only [State.setMem_setMem]
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 := pointsTo64_memRegion32_entails_40 s0.sp (key &&& 7#64)
        rw [← bv_sub_add_lit s0.sp 96 8] at h40
        apply SepWP.fold h40 (by sep_focus)
        wp_reach; intro hinvm
        refine SepWPp.weaken_pre (by dsimp only [chainParamsBudgetErrFrame]; sep_entail)
          (chainParams_from_err_exit_cl_placed hFromCall hFit hnone
            (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
            (by simp only [arm64_norm, htrm, htr])
            ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
             by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
             by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
             by simp only [arm64_norm, hvregs_m]⟩ hinvm)
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
            rw [hres_cur, mergeLoopBin_of_tag_zero protoPrefixStep_chainParamsPB_mergeField hgt_lim hd hk_ge hwt hitag0, Option.map_none]
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 104#64) hinvm
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd, sepExists_sepConj_left,
            sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs_dv
          wp_focus_pure; rintro ⟨hsm0, hsm1⟩
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs_dv
          have hevs_nil : evs_dv = [] := decodeVarint2Env_of_some hd hevs_dv
          subst hevs_nil
          conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
          apply SepWP.fold (skipBelow3_leaf_entails s0.sp 99 (by decide)) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split_96 s0.sp]
          conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_elim; intro v_err0
          wp_steps_sync_pool ((blkPl_294).base + 104#64)
          simp only [State.setMem_setMem]
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          wp_reach; intro hinvm
          refine SepWPp.weaken_pre (by dsimp only [chainParamsBudgetErrFrame]; sep_entail)
            (chainParams_from_err_exit_cl_placed hFromCall hFit hnone
              (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
              (by simp only [arm64_norm, htrm, htr])
              ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
               by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
               by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
               by simp only [arm64_norm, hvregs_m]⟩ hinvm)
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h
            have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1
            omega
          apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 212#64) hinvm
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd, sepExists_sepConj_left,
            sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs_dv
          wp_focus_pure; rintro ⟨hsm0, hsm1⟩
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs_dv
          have hevs_nil : evs_dv = [] := decodeVarint2Env_of_some hd hevs_dv
          subst hevs_nil
          conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
          apply SepWP.fold (skipBelow3_leaf_entails s0.sp 99 (by decide)) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          wp_steps_sync_pool ((blkPl_294).base + 212#64)
          simp only [State.setMem_setMem]
          wp_reach; intro hinvm
          refine SepWPp.weaken_pre (by dsimp only [chainParamsBudgetLoopPre]; sep_entail)
            (hcont key iwt rest _ hd hk_ge hwt hitag0
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
              (by simp only [arm64_norm, htrm, htr])
              (by simp only [arm64_norm, hsm1, hand_wt])
              (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
              (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
              (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
              ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
               by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
               by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
               by simp only [arm64_norm, hvregs_m]⟩ hinvm)

/-- Code-loaded placed loop induction for `ChainParams::merge` at `+0x0a0` (`(blkPl_294).base + 160#64`). -/
theorem chainParams_loop_ok_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    {x : ChainParamsMergeGhost} {st0 : M.σ} {R : SepProp} {s0 : State} {limit : Nat}
    (hFit : FitsEnv M lim st0 (ChainParamsMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63)
    (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : ChainParamsPB) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
        (mergeLoopBin ChainParamsPB.mergeField (cur.length - limit) m cur limit 98).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (blkPl_294).base + 160#64 →
      s.status = .Running → s.sp = s0.sp - 96#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s → LibsignalCodeLoaded lsmpl s.mem →
      SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s
        (chainParamsBudgetLoopPre A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (chainParamsMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (chainParamsMergeSpec A lim) (x, st0) R s0) := by
  intro n
  induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
    have hle_lim : cur.length ≤ limit := by omega
    exact chainParams_loop_le_exit_cl_placed hFromCall hFit hle_lim hsp_align hcur_le hcur_suf hlim_lt
      hres_cur hpc hrun hsp htr hx21 hx22 hcs hinv
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
    by_cases hle_lim : cur.length ≤ limit
    · exact chainParams_loop_le_exit_cl_placed hFromCall hFit hle_lim hsp_align hcur_le hcur_suf hlim_lt
        hres_cur hpc hrun hsp htr hx21 hx22 hcs hinv
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine chainParams_decode_key_step_cl_placed hFromCall hVarintCall hFit hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hres_cur ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hcs' hinv'
      obtain ⟨hx23', hx24', hx25', hx26', hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest :=
        suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 98)
        protoPrefixStep_chainParamsPB_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hloop_ok
        rw [chainParamsPB_mergeField_tag1] at hloop_ok
        apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 260#64) hinv'
        conv => arg 4; rw [chainParamsBudgetLoopPre]; simp only [sepConj_assoc]
        wp_steps_sync_pool ((blkPl_294).base + 260#64)
        simp only [State.setMem_setMem]
        wp_reach; intro hinv'
        apply SepWPp.weaken_pre
          (P' := chainParamsBudgetLoopPre A lim st0 s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
          (Entails.of_eq (by dsimp only [chainParamsBudgetLoopPre]; sep_ac_rfl))
        by_cases hiwt : iwt = .varint
        · subst hiwt
          have hnone_dv : decodeVarint rest = none →
              (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
            intro hdv; simp only [hres_cur, hloop_ok, eq_self, ↓reduceIte, hdv, Option.map_none]
          refine chainParams_tag1_varint_step_cl_placed (limit := limit) hPushCall hVarintCall hFit hsp_align
            hrest_le hrest_lt hrest_suf hnone_dv
            (fun v rest' s'' hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp'])
            (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0'])
            (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
            ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
             by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
             by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
             by simp only [arm64_norm, hvregs']⟩ hinv'
          have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv
          have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
          have hres_next : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
              (mergeLoopBin ChainParamsPB.mergeField (rest'.length - limit) { m with maxJump := v.truncate 32 } rest' limit 98).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, eq_self, ↓reduceIte, hdv, Option.map_some]
          exact ih { m with maxJump := v.truncate 32 } rest' s''
            (by omega) (by omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest (decodeVarint_suffix hdv))
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''
        · have hnone_wt : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
            simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, Option.map_none]
          exact chainParams_tag1_wt_err_step_cl_placed hFromCall hPushCall hFit hiwt hsp_align
            hrest_le hrest_suf hnone_wt
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp'])
            (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0'])
            ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
             by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
             by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
             by simp only [arm64_norm, hvregs']⟩ hinv'
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hloop_ok
          rw [chainParamsPB_mergeField_tag2] at hloop_ok
          apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 228#64) hinv'
          conv => arg 4; rw [chainParamsBudgetLoopPre]; simp only [sepConj_assoc]
          wp_steps_sync_pool ((blkPl_294).base + 228#64)
          simp only [State.setMem_setMem]
          wp_reach; intro hinv'
          apply SepWPp.weaken_pre
            (P' := chainParamsBudgetLoopPre A lim st0 s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
            (Entails.of_eq (by dsimp only [chainParamsBudgetLoopPre]; sep_ac_rfl))
          by_cases hiwt : iwt = .varint
          · subst hiwt
            have hnone_dv : decodeVarint rest = none →
                (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
              intro hdv; simp only [hres_cur, hloop_ok, eq_self, ↓reduceIte, hdv, Option.map_none]
            refine chainParams_tag2_varint_step_cl_placed (limit := limit) hPushCall hVarintCall hFit hsp_align
              hrest_le hrest_lt hrest_suf hnone_dv
              (fun v rest' s'' hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp'])
              (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0'])
              (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
              (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
              ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
               by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
               by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
               by simp only [arm64_norm, hvregs']⟩ hinv'
            have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv
            have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
            have hres_next : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
                (mergeLoopBin ChainParamsPB.mergeField (rest'.length - limit) { m with maxOooKeys := v.truncate 32 } rest' limit 98).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              simp only [hres_cur, hloop_ok, eq_self, ↓reduceIte, hdv, Option.map_some]
            exact ih { m with maxOooKeys := v.truncate 32 } rest' s''
              (by omega) (by omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest (decodeVarint_suffix hdv))
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''
          · have hnone_wt : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
              simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, Option.map_none]
            exact chainParams_tag2_wt_err_step_cl_placed hFromCall hPushCall hFit hiwt hsp_align
              hrest_le hrest_suf hnone_wt
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp'])
              (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0'])
              ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
               by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
               by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
               by simp only [arm64_norm, hvregs']⟩ hinv'
        · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
          obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 hitag_lt (by decide : 1 < 2 ^ 32)
          obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 hitag_lt (by decide : 2 < 2 ^ 32)
          have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by
            rw [sf_truncate32_ofNat64]; exact hb1_1
          have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by
            rw [sf_truncate32_ofNat64]; exact hb2_1
          have hb2_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 2#32) = true := by
            simp only [bne, hb2_1, Bool.not_false]
          have hb2_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 2#32) = true := by
            simp only [bne, hb2_2, Bool.not_false]
          rw [chainParamsPB_mergeField_other m iwt rest 98 hitag_lt htag1 htag2] at hloop_ok
          apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 140#64) hinv'
          conv => arg 4; rw [chainParamsBudgetLoopPre]; simp only [sepConj_assoc]
          wp_steps_sync_pool ((blkPl_294).base + 140#64)
          simp only [State.setMem_setMem]
          wp_reach; intro hinv'
          apply SepWPp.weaken_pre
            (P' := chainParamsBudgetLoopPre A lim st0 s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
            (Entails.of_eq (by dsimp only [chainParamsBudgetLoopPre]; sep_ac_rfl))
          have hnone_sf : skipField (2 * rest.length + 2) 98 (key.toNat / 8) iwt rest = none →
              (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
            intro hsf; rw [hres_cur, hloop_ok, hsf]; rfl
          refine chainParams_skip_step_cl_placed (limit := limit) hSkipCall hFit hsp_align hrest_le hrest_lt hrest_suf hitag_lt hnone_sf
            (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp'])
            (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0'])
            (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64])
            (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
            ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
             by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
             by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
             by simp only [arm64_norm, hvregs']⟩ hinv'
          have hrest'_le_rest : rest'.length ≤ rest.length :=
            (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
          have hres_next : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
              (mergeLoopBin ChainParamsPB.mergeField (rest'.length - limit) m rest' limit 98).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            rw [hres_cur, hloop_ok, hsf]; rfl
          exact ih m rest' s''
            (by omega) (by omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest
              ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''

/-- Relocatable code-loaded contract-parameterized budget verification of
`prost::encoding::message::merge::<ChainParams, &mut &[u8]>` (Block `294`) under `[LibsignalPlacement]`. -/
theorem chainParamsMerge_cl_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim))) :
    subroutine_ok ((blkPC_294).rebase (blkPl_294).base H)
      (blkPl_294).base
      (withLsCodeLoaded lsmpl (chainParamsMergeSpec A lim)) := by
  apply subroutine_ok_withLsCodeLoaded_of_withLsclProp
  unfold withLsclProp chainParamsMergeSpec chainParamsMergeSpecOfEnv
  wpp_init p s0
  rcases p with ⟨x, st0⟩
  apply SepWPp.elim_lsclProp; intro hinv0
  replace hpc : s0.pc = (blkPl_294).base := hpc
  change SepWPp _ _ _ _
    (WppPost (chainParamsMergeSpec A lim) (x, st0) R s0)
    (WppBudgetPanic (chainParamsMergeSpec A lim) (x, st0) R s0)
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
      simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    apply SepWPp.of_sepWP_lscl_mm (mid := lsmpl.base 291) hinv0
    conv => arg 4; rw [chainParamsMergeStack, stackAt_skipField3 s0.sp 99 (by decide), skipBelow3_leaf s0.sp 99 (by decide)]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp
    wp_steps_sync_pool (lsmpl.base 291)
    simp only [State.setMem_setMem]
    wp_reach; intro hinv0
    refine SepWPp.call_frame_lscl_mm (spec := decodeVarint2Spec A lim)
      (x := (⟨x.bufRef, x.slot, x.ptr, x.bs⟩, st0))
      (ret_pc := (blkPl_294).base + 48#64) hVarintCall hinv0
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      rfl ⟨by simp only [arm64_norm, h_3], h_4, FitsEnv.chainParams_decodeVarint2 x.bs h⟩
      (by sep_focus)
      (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
      (fun _ _ => wppBudgetPanic_false) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, h_2, h_3]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chainParamsPB_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 116#64) hinvm
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro evs_dv
      wp_focus_pure; intro hsm0
      wp_focus_pure; intro htrm
      wp_focus_pure; intro hevs_dv
      wp_focus_pure; intro hsm1
      have hevs_eq : evs_dv = rustAllocEvents 72 8 := decodeVarint2Env_of_none hdv0 hevs_dv
      conv => arg 4; simp only [arm64_norm]
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp 99 (by decide)) (by sep_focus)
      wp_steps_sync_pool ((blkPl_294).base + 116#64)
      simp only [State.setMem_setMem]
      wp_reach; intro _hinvm'
      refine SepWPp.weaken_pre (by dsimp only [chainParamsBudgetErrFrame]; sep_entail)
        (chainParams_err0_ret_exit_placed hnone
          ⟨evs_dv, hevs_eq ▸ .fromOnly, rfl⟩ hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
          (by simp only [arm64_norm, htrm]) (by simp only [arm64_norm]) hsm1
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
           by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
           by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
           by simp only [arm64_norm, hvregs_m]⟩)
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
      have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt h_4)
      have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chainParamsPB_mergeField]
          simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0, hlt_len]
        apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 104#64) hinvm
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_dv
        wp_focus_pure; rintro ⟨hsm0, hsm1⟩
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_dv
        have hevs_nil : evs_dv = [] := decodeVarint2Env_of_some hdv0 hevs_dv
        subst hevs_nil
        conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm]
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 99 (by decide)) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt, memRegion_48_split_96 s0.sp]
        conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_stk0
        wp_steps_sync_pool ((blkPl_294).base + 104#64)
        simp only [State.setMem_setMem]
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach; intro hinvm
        refine SepWPp.weaken_pre (by dsimp only [chainParamsBudgetErrFrame]; sep_entail)
          (chainParams_from_err_exit_cl_placed hFromCall h hnone
            (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
            (by simp only [arm64_norm, htrm])
            ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
             by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
             by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
             by simp only [arm64_norm, hvregs_m]⟩ hinvm)
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
          have hsuf := hrest0_suf; unfold IsDropSuffix at hsuf
          conv => rhs; rw [hsuf, List.drop_drop]
          exact congrArg (List.drop · x.bs) (by omega)
        have hres0 : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
            (mergeLoopBin ChainParamsPB.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chainParamsPB_mergeField]
          simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
            proto_decodeVarint_toOption, hdv0, hlt_len, hdrop_eq]
          rcases mergeLoopBin ChainParamsPB.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98 with _ | m' <;> rfl
        apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 160#64) hinvm
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_dv
        wp_focus_pure; rintro ⟨hsm0, hsm1⟩
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_dv
        have hevs_nil : evs_dv = [] := decodeVarint2Env_of_some hdv0 hevs_dv
        subst hevs_nil
        conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm]
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 99 (by decide)) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; simp only [sepConj_assoc]
        wp_steps_sync_pool ((blkPl_294).base + 160#64)
        simp only [State.setMem_setMem]
        wp_reach; intro hinvm
        refine SepWPp.weaken_pre (by rw [chainParamsBudgetLoopPre, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; sep_entail)
          (chainParams_loop_ok_cl_placed hFromCall hPushCall hVarintCall hSkipCall h hsp_align h_4 hlim_lt
            rest0.length x.msg rest0 _ (Nat.le_refl _) hrest0_le hrest0_suf hres0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
            (by simp only [arm64_norm, htrm])
            (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub])
            ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
             by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
             by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
             by simp only [arm64_norm, hvregs_m]⟩ hinvm)
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by
      simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [truncate32_zeroExtend64_and_255_eq, h_1]
      cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [← hbne1]; congr 2; bv_bits
    have hnone : (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chainParamsPB_mergeField]
      cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | rfl
    apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 104#64) hinv0
    conv => arg 4; rw [chainParamsMergeStack, stackAt_skipField3 s0.sp 99 (by decide), sliceCursorAt, memRegion_48_wtErr96 s0.sp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0
    apply SepWP.exists_elim; intro v_wt0
    wp_steps_sync_pool ((blkPl_294).base + 104#64)
    simp only [State.setMem_setMem]
    apply SepWP.fold (wtErr96_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    wp_reach; intro hinv0
    refine SepWPp.weaken_pre (by dsimp only [chainParamsBudgetErrFrame]; sep_entail)
      (chainParams_from_err_exit_cl_placed hFromCall h hnone
        (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm]⟩ hinv0)

theorem chainParamsMerge_cro_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim))) :
    subroutine_ok ((blkPC_294).rebase (blkPl_294).base H)
      (blkPl_294).base
      (withLsCodeRoLoaded lsmpl (chainParamsMergeSpec A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm
    (chainParamsMerge_cl_placed_ok_of_contracts hFromCall hPushCall hVarintCall hSkipCall)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget
