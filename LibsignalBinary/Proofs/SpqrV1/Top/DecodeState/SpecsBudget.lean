/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.Specs
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
public import LibsignalBinary.Heap.IfaceBudgetBase

/-!
# Budget-Threaded `spqr::decode_state` Callee & Top-Level Specifications

Defines callee-closed allocator event envelopes (`DecodeStateEnv` and per-submessage envelopes)
along with budget-threaded merge, `drop_glue`, callee-bundle, and top-level `decodeStateSpecX`
contracts (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
   fitsEvents_append rustAllocEvents rustCliDeallocBudgetSpecBase)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorPushEnv decodeErrorFromBudgetSpec decodeErrorPushBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (SkipField3Env bytesMerge3RawBudgetSpec skipField3BudgetSpec skipField3EventsCore)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget
  (GrowOneStrideEnv growOneStrideFullSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget
  (AllocContracts4K)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (v1StateMergeSpec v1StateMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (decodeVarintSliceEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv bytesMergeEventsCore doReserveClearEvents)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint mergeBytes skipField)
open CryptoVerification.LibsignalTripleRatchet
  (deallocName decodeErrorAtStackLen decodeErrorFromName decodeErrorPushName
   memcpyName sessionMemcpySpec tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeGhost SkipFieldGhost sliceCursorAfter sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1
  (ChainParamsPB EpochDirectionPB spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Alloc (growOneChainEpochName)
open CryptoVerification.SpqrV1.Drop
  (dropOptProtoInnerStateName dropProtoPqRatchetStateName)
open CryptoVerification.SpqrV1.ProtoRepr (chainParamsPBAt epochDirectionPBAt)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Name skipField3Name)
open CryptoVerification.SpqrV1.Prost.BytesMerge (bytesMerge3Name)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (OptInnerStatePolyBound V1StateMergeGhost chainParamsMergeName codecWireTypeToProto
   epochDirectionMergeName optProtoInnerStateCapAt v1StateJumpTablesAt v1StateMergeName)
open CryptoVerification.SpqrV1.Top.DecodeState
  (ChainParamsMergeGhost DecodeStateGhost DropOptProtoInnerStateGhost DropProtoPqRatchetStateGhost
   EpochDirectionMergeGhost V1InnerHeapPred chainParamsMergeStack
   decodeStateName decodeStateResultAt decodeStateStackX
   dropOptProtoInnerStateStack
   epochDirectionMergeStack epochDirectionPBCapOkAt optProtoInnerStateAt
   optProtoInnerStateCapOkAt protoPqRatchetStateAt)

/-! ## 1. Callee-Closed Event Envelopes for `spqr::decode_state` -/

/-- Single-step allocator event envelope inside `spqr::decode_state` on an input slice of length
at most `maxLen` with `Polynomial{Decoder,Encoder}` capacities bounded by `polyCapBound`:
covers `[]`, pure deallocations (`FreeOnlyEvs`), `DecodeError::from` (`72`, `8`),
`DecodeError::push` (`n ≤ 4`), deterministic `bytes::merge` (`bytesMergeEventsCore` with
`bs.length ≤ maxLen` and `valCap.toNat ≤ maxLen`), `RawVec<Pt/Poly>::grow_one` (`stride = 24`,
`align = 8`, `cap.toNat < polyCapBound`), and `RawVec<ChainEpoch>::grow_one` (`stride = 112`,
`align = 8`, `cap.toNat ≤ 2 * maxLen + 4`). -/
inductive DecodeStateIterEnv (maxLen polyCapBound : Nat) : List AllocEvent → Prop where
  | nil :
      DecodeStateIterEnv maxLen polyCapBound []
  | deallocs {evs : List AllocEvent} :
      FreeOnlyEvs evs →
      DecodeStateIterEnv maxLen polyCapBound evs
  | fromErr :
      DecodeStateIterEnv maxLen polyCapBound (rustAllocEvents 72 8)
  | pushErr {n : Nat} {evs : List AllocEvent} :
      n ≤ 4 →
      DecodeErrorPushEnv n evs →
      DecodeStateIterEnv maxLen polyCapBound evs
  | bytesMerge (wt : WireType) (valCap : BitVec 64) (bs : List (BitVec 8)) :
      bs.length ≤ maxLen →
      valCap.toNat ≤ maxLen →
      DecodeStateIterEnv maxLen polyCapBound (bytesMergeEventsCore wt valCap bs)
  | growPolyElem (cap : BitVec 64) {evs : List AllocEvent} :
      cap.toNat < polyCapBound →
      GrowOneStrideEnv cap 24 8 evs →
      DecodeStateIterEnv maxLen polyCapBound evs
  | growChainEpoch (cap : BitVec 64) {evs : List AllocEvent} :
      cap.toNat ≤ 2 * maxLen + 4 →
      GrowOneStrideEnv cap 112 8 evs →
      DecodeStateIterEnv maxLen polyCapBound evs

theorem DecodeStateIterEnv.mono {m₁ m₂ p₁ p₂ : Nat} {evs : List AllocEvent}
    (hm : m₁ ≤ m₂) (hp : p₁ ≤ p₂)
    (h : DecodeStateIterEnv m₁ p₁ evs) :
    DecodeStateIterEnv m₂ p₂ evs := by
  cases h with
  | nil => exact .nil
  | deallocs hf => exact .deallocs hf
  | fromErr => exact .fromErr
  | pushErr hn hp' => exact .pushErr hn hp'
  | bytesMerge wt vc bs hlen hvc =>
    exact .bytesMerge wt vc bs (Nat.le_trans hlen hm) (Nat.le_trans hvc hm)
  | growPolyElem cap hcap hg =>
    exact .growPolyElem cap (Nat.lt_of_lt_of_le hcap hp) hg
  | growChainEpoch cap hcap hg =>
    exact .growChainEpoch cap (by omega) hg

theorem DecodeStateIterEnv.of_freeOnly {maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (h : FreeOnlyEvs evs) :
    DecodeStateIterEnv maxLen polyCapBound evs :=
  .deallocs h

theorem DecodeStateIterEnv.of_decodeErrorFrom {maxLen polyCapBound : Nat} :
    DecodeStateIterEnv maxLen polyCapBound (rustAllocEvents 72 8) :=
  .fromErr

theorem DecodeStateIterEnv.of_decodeErrorPush {maxLen polyCapBound n : Nat} {evs : List AllocEvent}
    (hn : n ≤ 4) (h : DecodeErrorPushEnv n evs) :
    DecodeStateIterEnv maxLen polyCapBound evs :=
  .pushErr hn h

theorem DecodeStateIterEnv.of_decodeVarint2 {maxLen polyCapBound : Nat}
    {bs : List (BitVec 8)} {evs : List AllocEvent}
    (h : DecodeVarint2Env bs evs) :
    DecodeStateIterEnv maxLen polyCapBound evs := by
  simp only [DecodeVarint2Env, TripleRatchet.Prost.DefsBudget.DecodeVarintSliceEnv,
    decodeVarintSliceEvents] at h
  subst h
  split
  · exact .nil
  · exact .of_decodeErrorFrom

theorem DecodeStateIterEnv.of_skipField3 {maxLen polyCapBound : Nat}
    {x : SkipFieldGhost} {evs : List AllocEvent}
    (h : SkipField3Env x evs) :
    DecodeStateIterEnv maxLen polyCapBound evs := by
  dsimp only [SkipField3Env, skipField3EventsCore] at h
  subst h
  cases skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs with
  | some _ => exact .nil
  | none => exact .of_decodeErrorFrom

theorem DecodeStateIterEnv.of_bytesMergeEnv {maxLen polyCapBound : Nat}
    {x : BytesMergeGhost} {evs : List AllocEvent}
    (hlen : x.bs.length ≤ maxLen) (hmax : maxLen < 2 ^ 64)
    (hv : ∀ v r, mergeBytes x.wt x.bs = some (v, r) → v.length ≤ maxLen)
    (h : BytesMergeEnv x evs) :
    DecodeStateIterEnv maxLen polyCapBound evs := by
  dsimp only [BytesMergeEnv] at h
  subst h
  by_cases hcap : x.valCap.toNat ≤ maxLen
  · exact .bytesMerge x.wt x.valCap x.bs hlen hcap
  · let cap' : BitVec 64 := BitVec.ofNat 64 maxLen
    have hcap'_eq : cap'.toNat = maxLen := by
      simp [cap']
      omega
    have heq : bytesMergeEventsCore x.wt x.valCap x.bs = bytesMergeEventsCore x.wt cap' x.bs := by
      dsimp only [bytesMergeEventsCore]
      cases hmb : mergeBytes x.wt x.bs with
      | none => rfl
      | some p =>
        rcases p with ⟨v, r⟩
        have hvl : v.length ≤ maxLen := hv v r hmb
        by_cases hv0 : v.length = 0
        · simp [hv0]
        · simp only [hv0, ↓reduceIte, doReserveClearEvents, hcap'_eq, hvl,
            show v.length ≤ x.valCap.toNat by omega]
    rw [heq]
    exact .bytesMerge x.wt cap' x.bs hlen (by omega)

/-- Counter-bounded sequential closure of `DecodeStateIterEnv maxLen polyCapBound`
from step index `step` up to `limit` (`step < limit` at every step). -/
inductive DecodeStateStepsEnv : Nat → Nat → Nat → Nat → List AllocEvent → Prop where
  | nil {step limit maxLen polyCapBound : Nat} :
      DecodeStateStepsEnv step limit maxLen polyCapBound []
  | step {step limit maxLen polyCapBound : Nat} {evs₁ evs₂ : List AllocEvent} :
      step < limit →
      DecodeStateIterEnv maxLen polyCapBound evs₁ →
      DecodeStateStepsEnv (step + 1) limit maxLen polyCapBound evs₂ →
      DecodeStateStepsEnv step limit maxLen polyCapBound (evs₁ ++ evs₂)

theorem DecodeStateStepsEnv.mono_range {s₁ l₁ m₁ p₁ s₂ l₂ m₂ p₂ : Nat} {evs : List AllocEvent}
    (hr : s₂ + l₁ ≤ s₁ + l₂) (hm : m₁ ≤ m₂) (hp : p₁ ≤ p₂)
    (h : DecodeStateStepsEnv s₁ l₁ m₁ p₁ evs) :
    DecodeStateStepsEnv s₂ l₂ m₂ p₂ evs := by
  induction h generalizing s₂ l₂ with
  | nil => exact .nil
  | @step step limit _ _ e₁ e₂ hs h1 _ ih =>
    exact .step (by omega) (h1.mono hm hp) (ih (by omega) hm hp)

theorem DecodeStateStepsEnv.append_steps {s₁ l₁ d maxLen polyCapBound : Nat}
    {evs₁ evs₂ : List AllocEvent}
    (hs₁ : s₁ ≤ l₁)
    (h₁ : DecodeStateStepsEnv s₁ l₁ maxLen polyCapBound evs₁)
    (h₂ : DecodeStateStepsEnv 0 d maxLen polyCapBound evs₂) :
    DecodeStateStepsEnv s₁ (l₁ + d) maxLen polyCapBound (evs₁ ++ evs₂) := by
  induction h₁ with
  | @nil step limit _ _ =>
    simpa using h₂.mono_range (s₂ := step) (l₂ := limit + d) (by omega)
      (Nat.le_refl _) (Nat.le_refl _)
  | @step step limit _ _ e₁ e₂ hs head _ ih =>
    rw [List.append_assoc]
    exact .step (by omega) head (ih (by omega) h₂)

/-- Bounded-step sequential closure of `DecodeStateIterEnv maxLen polyCapBound` (`0..fuel`). -/
def DecodeStateLoopEnv (fuel maxLen polyCapBound : Nat) (evs : List AllocEvent) : Prop :=
  DecodeStateStepsEnv 0 fuel maxLen polyCapBound evs

theorem DecodeStateLoopEnv.nil {fuel maxLen polyCapBound : Nat} :
    DecodeStateLoopEnv fuel maxLen polyCapBound [] :=
  DecodeStateStepsEnv.nil

theorem DecodeStateLoopEnv.step {fuel maxLen polyCapBound : Nat} {evs₁ evs₂ : List AllocEvent}
    (h₁ : DecodeStateIterEnv maxLen polyCapBound evs₁)
    (h₂ : DecodeStateLoopEnv fuel maxLen polyCapBound evs₂) :
    DecodeStateLoopEnv (fuel + 1) maxLen polyCapBound (evs₁ ++ evs₂) :=
  DecodeStateStepsEnv.step (Nat.zero_lt_succ fuel) h₁
    (h₂.mono_range (by omega) (Nat.le_refl _) (Nat.le_refl _))

theorem DecodeStateLoopEnv.single {fuel maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (h : DecodeStateIterEnv maxLen polyCapBound evs) :
    DecodeStateLoopEnv (fuel + 1) maxLen polyCapBound evs := by
  simpa using DecodeStateLoopEnv.step (fuel := fuel) h .nil

theorem DecodeStateLoopEnv.mono_fuel {f₁ f₂ maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (hf : f₁ ≤ f₂) (h : DecodeStateLoopEnv f₁ maxLen polyCapBound evs) :
    DecodeStateLoopEnv f₂ maxLen polyCapBound evs :=
  h.mono_range (by omega) (Nat.le_refl _) (Nat.le_refl _)

theorem DecodeStateLoopEnv.mono {f₁ f₂ m₁ m₂ p₁ p₂ : Nat} {evs : List AllocEvent}
    (hf : f₁ ≤ f₂) (hm : m₁ ≤ m₂) (hp : p₁ ≤ p₂)
    (h : DecodeStateLoopEnv f₁ m₁ p₁ evs) :
    DecodeStateLoopEnv f₂ m₂ p₂ evs :=
  h.mono_range (by omega) hm hp

theorem DecodeStateLoopEnv.append {f₁ f₂ maxLen polyCapBound : Nat} {evs₁ evs₂ : List AllocEvent}
    (h₁ : DecodeStateLoopEnv f₁ maxLen polyCapBound evs₁)
    (h₂ : DecodeStateLoopEnv f₂ maxLen polyCapBound evs₂) :
    DecodeStateLoopEnv (f₁ + f₂) maxLen polyCapBound (evs₁ ++ evs₂) :=
  h₁.append_steps (Nat.zero_le _) h₂

theorem FitsEnv.decodeStateLoop_head {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen polyCapBound : Nat} {E : List AllocEvent → Prop}
    (hsub : ∀ evs, E evs → DecodeStateIterEnv maxLen polyCapBound evs)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv (fuel + 1) maxLen polyCapBound)) :
    FitsEnv M lim st E :=
  fun evs he => hFit evs (DecodeStateLoopEnv.single (hsub evs he))

theorem FitsEnv.decodeStateLoop_tail {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen polyCapBound : Nat} {evs₁ : List AllocEvent}
    (h1 : DecodeStateIterEnv maxLen polyCapBound evs₁)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv (fuel + 1) maxLen polyCapBound)) :
    FitsEnv M lim (M.stepEvents evs₁ st) (DecodeStateLoopEnv fuel maxLen polyCapBound) :=
  fun evs₂ h2 =>
    ((fitsEvents_append M lim evs₁ evs₂ st).mp
      (hFit (evs₁ ++ evs₂) (DecodeStateLoopEnv.step h1 h2))).2

theorem FitsEnv.decodeStateLoop_split {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {f₁ f₂ maxLen polyCapBound : Nat} {evs₁ : List AllocEvent}
    (h₁ : DecodeStateLoopEnv f₁ maxLen polyCapBound evs₁)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv (f₁ + f₂) maxLen polyCapBound)) :
    FitsEnv M lim (M.stepEvents evs₁ st) (DecodeStateLoopEnv f₂ maxLen polyCapBound) :=
  fun evs₂ h₂ =>
    ((fitsEvents_append M lim evs₁ evs₂ st).mp (hFit (evs₁ ++ evs₂) (h₁.append h₂))).2

theorem FitsEnv.decodeStateLoop_mono {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {f₁ f₂ m₁ m₂ p₁ p₂ : Nat}
    (hf : f₁ ≤ f₂) (hm : m₁ ≤ m₂) (hp : p₁ ≤ p₂)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv f₂ m₂ p₂)) :
    FitsEnv M lim st (DecodeStateLoopEnv f₁ m₁ p₁) :=
  hFit.mono fun _ h => h.mono hf hm hp

def DecodeStateEnv (x : DecodeStateGhost) (evs : List AllocEvent) : Prop :=
  DecodeStateLoopEnv (16 * x.st.bytes.length + 32) x.st.bytes.length
    (2 * x.st.bytes.length + 16) evs

/-! ## 2. `ChainParams::merge` & `EpochDirection::merge` Envelopes and Contracts -/

/-- Precondition allocation envelope of `ChainParams::merge` (`polyCapBound = 0`). -/
def ChainParamsMergeEnv (x : ChainParamsMergeGhost) (evs : List AllocEvent) : Prop :=
  DecodeStateLoopEnv (4 * x.bs.length + 8) x.bs.length 0 evs

/-- Postcondition allocation envelope of `ChainParams::merge`: proportional to consumed bytes
`x.bs.length - rest.length` on `Ok`, and bounded by `4 * x.bs.length + 8` on `Err`. -/
def ChainParamsMergePostEnv (x : ChainParamsMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
  | some (_, rest) => DecodeStateLoopEnv (4 * (x.bs.length - rest.length)) x.bs.length 0 evs
  | none => DecodeStateLoopEnv (4 * x.bs.length + 8) x.bs.length 0 evs

theorem chainParamsMergePostEnv_imp_pre {x : ChainParamsMergeGhost} {evs : List AllocEvent}
    (h : ChainParamsMergePostEnv x evs) :
    ChainParamsMergeEnv x evs := by
  dsimp only [ChainParamsMergePostEnv, ChainParamsMergeEnv] at h ⊢
  split at h
  · exact h.mono_fuel (by omega)
  · exact h

/-- Envelope-parameterized budget-threaded contract of `ChainParams::merge`. -/
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
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chainParamsPBAt x.msgPtr m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 1⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : ChainParamsPB, chainParamsPBAt x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `ChainParams::merge` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def chainParamsMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainParamsMergeGhost × M.σ) :=
  chainParamsMergeSpecOfEnv A lim ChainParamsMergeEnv ChainParamsMergePostEnv

/-- Precondition allocation envelope of `EpochDirection::merge` (`polyCapBound = 0`). -/
def EpochDirectionMergeEnv (x : EpochDirectionMergeGhost) (evs : List AllocEvent) : Prop :=
  DecodeStateLoopEnv (4 * x.bs.length + 8) x.bs.length 0 evs

/-- Postcondition allocation envelope of `EpochDirection::merge`: proportional to consumed bytes
`x.bs.length - rest.length` on `Ok`, and bounded by `4 * x.bs.length + 8` on `Err`. -/
def EpochDirectionMergePostEnv (x : EpochDirectionMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
  | some (_, rest) => DecodeStateLoopEnv (4 * (x.bs.length - rest.length)) x.bs.length 0 evs
  | none => DecodeStateLoopEnv (4 * x.bs.length + 8) x.bs.length 0 evs

theorem epochDirectionMergePostEnv_imp_pre {x : EpochDirectionMergeGhost} {evs : List AllocEvent}
    (h : EpochDirectionMergePostEnv x evs) :
    EpochDirectionMergeEnv x evs := by
  dsimp only [EpochDirectionMergePostEnv, EpochDirectionMergeEnv] at h ⊢
  split at h
  · exact h.mono_fuel (by omega)
  · exact h

/-- Envelope-parameterized budget-threaded contract of `EpochDirection::merge`. -/
def epochDirectionMergeSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop) :
    Spec (EpochDirectionMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      epochDirectionPBCapOkAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp epochDirectionMergeStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp epochDirectionMergeStack ∗
      match (mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          epochDirectionPBCapOkAt A.repAlloc x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 1⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : EpochDirectionPB, epochDirectionPBAt A.repAlloc x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `EpochDirection::merge` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def epochDirectionMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (EpochDirectionMergeGhost × M.σ) :=
  epochDirectionMergeSpecOfEnv A lim EpochDirectionMergeEnv EpochDirectionMergePostEnv

/-! ## 3. Budget-Threaded `drop_glue` Contracts (`FreeOnlyEvs`) -/

/-- Budget-threaded contract for
`core::ptr::drop_glue::<Option<spqr::proto::pq_ratchet::v1_state::InnerState>>`
(`FreeOnlyEvs`, `onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def dropOptProtoInnerStateSpec (H_inner : V1InnerHeapPred) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (b : BitVec 64) :
    Spec (DropOptProtoInnerStateGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      optProtoInnerStateAt H_inner A.repAlloc x.a x.st ∗
      v1StateJumpTablesAt b ∗
      A.pool lim st s ∗ stackAt s.sp dropOptProtoInnerStateStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.a 224 ∗
      v1StateJumpTablesAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropOptProtoInnerStateStack

/-- Budget-threaded contract for
`core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>`
(`FreeOnlyEvs`, `onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def dropProtoPqRatchetStateSpec (H_inner : V1InnerHeapPred) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (b : BitVec 64) :
    Spec (DropProtoPqRatchetStateGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      protoPqRatchetStateAt H_inner A.repAlloc x.a x.st ∗
      v1StateJumpTablesAt b ∗
      A.pool lim st s ∗ stackAt s.sp dropOptProtoInnerStateStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.a 352 ∗
      v1StateJumpTablesAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp dropOptProtoInnerStateStack

/-! ## 4. Callee Contract Bundles & Top-Level `decodeStateSpecX` -/

/-- Minimal 4K-stack allocator/memcpy projection required by `spqr::decode_state` (`VmPreserved` on
`memcpy` so `A.pool` syncs across `memcpy` calls). -/
structure DecodeStateAllocContracts (b : BitVec 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop where
  dealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr deallocName) (rustCliDeallocBudgetSpecBase M A lim)
  memcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
      (withVmPreserved (libcMemcpySpec hookStack))
  session_memcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
      (withVmPreserved (sessionMemcpySpec hookStack))

/-- Bundle of budget-threaded callee contracts used by `spqr::decode_state` (backed by
`AllocContracts4K`). -/
structure DecodeStateCalleeContracts (H_inner : V1InnerHeapPred) (b : BitVec 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop where
  b_page_aligned : b &&& 0xfff#64 = 0#64
  of_drop_inner : ∀ a opt,
    CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A.repAlloc a opt ⊢
      optProtoInnerStateAt H_inner A.repAlloc a opt
  of_cap_inner : ∀ a remLen opt,
    OptInnerStatePolyBound remLen opt →
    optProtoInnerStateCapAt A.repAlloc a remLen opt ⊢
      optProtoInnerStateCapOkAt H_inner A.repAlloc a remLen opt
  alloc : AllocContracts4K b A lim ext
  decodeErrorFrom : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr decodeErrorFromName)
    (decodeErrorFromBudgetSpec M A lim)
  decodeErrorPush : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr decodeErrorPushName)
    (decodeErrorPushBudgetSpec M A lim)
  decodeVarint2 : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr decodeVarint2Name)
    (decodeVarint2Spec A lim)
  skipField3 : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr skipField3Name)
    (skipField3BudgetSpec M A lim)
  chainParamsMerge : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr chainParamsMergeName)
    (chainParamsMergeSpec A lim)
  growOneChainEpoch : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr growOneChainEpochName)
    (growOneStrideFullSpec M A lim 112 8)
  dropOptProtoInnerState : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr dropOptProtoInnerStateName)
    (dropOptProtoInnerStateSpec H_inner A lim b)
  dropProtoPqRatchetState : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr dropProtoPqRatchetStateName)
    (dropProtoPqRatchetStateSpec H_inner A lim b)

/-- Full budget-threaded callee contracts for `spqr::decode_state`, extending
`DecodeStateCalleeContracts` with `.inImage img` contracts for `bytesMerge3`,
`epochDirectionMerge`, and `v1StateMerge`. -/
structure DecodeStateCalleeContractsX (H_inner : V1InnerHeapPred) (img : Obj.Image)
    (b : BitVec 64) {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop extends
    DecodeStateCalleeContracts H_inner b A lim ext where
  bytesMerge3 : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr bytesMerge3Name)
    ((bytesMerge3RawBudgetSpec M A lim).inImage img)
  epochDirectionMerge : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr epochDirectionMergeName)
    ((epochDirectionMergeSpec A lim).inImage img)
  v1StateMerge : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr v1StateMergeName)
    ((v1StateMergeSpec A lim b).inImage img)

/-- 4K-stack bundle of budget-threaded callee contracts used by `spqr::decode_state`. -/
structure DecodeStateCalleeContracts4K (H_inner : V1InnerHeapPred) (b : BitVec 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop where
  b_page_aligned : b &&& 0xfff#64 = 0#64
  of_drop_inner : ∀ a opt,
    CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A.repAlloc a opt ⊢
      optProtoInnerStateAt H_inner A.repAlloc a opt
  of_cap_inner : ∀ a remLen opt,
    OptInnerStatePolyBound remLen opt →
    optProtoInnerStateCapAt A.repAlloc a remLen opt ⊢
      optProtoInnerStateCapOkAt H_inner A.repAlloc a remLen opt
  alloc : DecodeStateAllocContracts b A lim ext
  decodeErrorFrom : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr decodeErrorFromName)
    (decodeErrorFromBudgetSpec M A lim)
  decodeErrorPush : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr decodeErrorPushName)
    (decodeErrorPushBudgetSpec M A lim)
  decodeVarint2 : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr decodeVarint2Name)
    (decodeVarint2Spec A lim)
  skipField3 : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr skipField3Name)
    (skipField3BudgetSpec M A lim)
  chainParamsMerge : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr chainParamsMergeName)
    (chainParamsMergeSpec A lim)
  growOneChainEpoch : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr growOneChainEpochName)
    (growOneStrideFullSpec M A lim 112 8)
  dropOptProtoInnerState : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr dropOptProtoInnerStateName)
    (dropOptProtoInnerStateSpec H_inner A lim b)
  dropProtoPqRatchetState : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr dropProtoPqRatchetStateName)
    (dropProtoPqRatchetStateSpec H_inner A lim b)

/-- Full 4K-stack budget-threaded callee contracts for `spqr::decode_state`, extending
`DecodeStateCalleeContracts4K` with `.inImage img` contracts for `bytesMerge3`,
`epochDirectionMerge`, and `v1StateMerge`. -/
structure DecodeStateCalleeContractsX4K (H_inner : V1InnerHeapPred) (img : Obj.Image)
    (b : BitVec 64) {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop extends
    DecodeStateCalleeContracts4K H_inner b A lim ext where
  bytesMerge3 : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr bytesMerge3Name)
    ((bytesMerge3RawBudgetSpec M A lim).inImage img)
  epochDirectionMerge : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr epochDirectionMergeName)
    ((epochDirectionMergeSpec A lim).inImage img)
  v1StateMerge : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr v1StateMergeName)
    ((v1StateMergeSpec A lim b).inImage img)

theorem DecodeStateCalleeContracts.to4K {H_inner : V1InnerHeapPred} {b : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContracts H_inner b A lim ext) :
    DecodeStateCalleeContracts4K H_inner b A lim ext :=
  { b_page_aligned := hc.b_page_aligned
    of_drop_inner := hc.of_drop_inner
    of_cap_inner := hc.of_cap_inner
    alloc := ⟨hc.alloc.dealloc, hc.alloc.memcpy, hc.alloc.session_memcpy⟩
    decodeErrorFrom := hc.decodeErrorFrom
    decodeErrorPush := hc.decodeErrorPush
    decodeVarint2 := hc.decodeVarint2
    skipField3 := hc.skipField3
    chainParamsMerge := hc.chainParamsMerge
    growOneChainEpoch := hc.growOneChainEpoch
    dropOptProtoInnerState := hc.dropOptProtoInnerState
    dropProtoPqRatchetState := hc.dropProtoPqRatchetState }

theorem DecodeStateCalleeContractsX.to4K {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsX H_inner img b A lim ext) :
    DecodeStateCalleeContractsX4K H_inner img b A lim ext :=
  { hc.toDecodeStateCalleeContracts.to4K with
    bytesMerge3 := hc.bytesMerge3
    epochDirectionMerge := hc.epochDirectionMerge
    v1StateMerge := hc.v1StateMerge }

/-- Envelope-parameterized budget-threaded specification of `spqr::decode_state` against
trusted `spqrDecodeState` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def decodeStateSpecXOfEnv (H_inner : V1InnerHeapPred) (b : BitVec 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop) :
    Spec (DecodeStateGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outPtr ∧
      s.readReg64 .x0 = x.st.v ∧
      x.st.bytes.length < 2 ^ 32 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      v1StateJumpTablesAt b ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st s ∗ stackAt s.sp decodeStateStackX
  post := fun (x, st) s0 sf =>
    (∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
      A.pool lim (M.stepEvents evs st) sf) ∗
      v1StateJumpTablesAt b ∗
      x.st.at A.repAlloc ∗
      decodeStateResultAt H_inner A.repAlloc x.outPtr (spqrDecodeState x.st.bytes) ∗
      stackAt s0.sp decodeStateStackX

def decodeStateSpecX (H_inner : V1InnerHeapPred) (b : BitVec 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DecodeStateGhost × M.σ) :=
  decodeStateSpecXOfEnv H_inner b A lim DecodeStateEnv DecodeStateEnv

/-- Envelope-parameterized `subroutine_ok` predicate for `spqr::decode_state` on `img`. -/
def DecodeStateOkXOfEnv (H_inner : V1InnerHeapPred) (img : Obj.Image) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr decodeStateName)
    ((decodeStateSpecXOfEnv H_inner img.base A lim PreEnv PostEnv).inImage img)

/-- `spqr::decode_state` meets `(decodeStateSpecX H_inner img.base A lim).inImage img` on
`tripleRatchetProgAtExt img.base ext`. -/
def DecodeStateOkX (H_inner : V1InnerHeapPred) (img : Obj.Image) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  DecodeStateOkXOfEnv H_inner img A lim DecodeStateEnv DecodeStateEnv ext

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
