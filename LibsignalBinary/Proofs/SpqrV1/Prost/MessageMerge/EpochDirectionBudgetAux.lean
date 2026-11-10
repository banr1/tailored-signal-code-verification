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
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.DefsClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergeCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23BudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
public import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Budget Envelopes, Contracts, and Exit Helpers for `EpochDirection::merge` (Block `299`)

Defines the shrinking-slice allocator event envelopes (`EpochDirectionLoopEnv`,
`EpochDirectionOkEnv`, `EpochDirectionMergeEnv`, `EpochDirectionMergePostEnv`), budget contracts
`epochDirectionMergeSpecOfEnv` and `epochDirectionMergeSpec`, and relocatable Block `299` exit and
tag-1 arm lemmas.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open CryptoVerification.SpqrV1.Prost.MessageMerge (EpochDirectionMergeGhost WppPost blkPC_299 blkPl_299 codecWireTypeToProto decodeErrorWith_one_entails_le1 decodeErrorWith_zero_entails_le1 epochDirectionMergeStack epochDirectionPBAt_entails_exists epochDirectionPBCapOkAt epochDirectionPBCapOkAt_entails_epochDirectionPBAt epochDirectionPBCapOkAt_mono iwt_cbnz_true_of_ne_varint memRegion8_memRegion40_entails_48 memRegion_48_wtErr96 pointsTo64_memRegion40_entails_48 sepConj_memRegion_48_split_96 setWidth8_ofNat64_wt skipBelow3_98_eq_stackAt_97 vecU8CapOkAt_mono wtErr96_entails_memRegion40)
open CryptoVerification.SpqrV1.Varint (skipBelow3 skipBelow3_err skipBelow3_err_entails skipBelow3_leaf skipBelow3_leaf_entails stackAt_skipField3)

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement extract_withLsCodeLoaded lsmpl
   withLsCodeLoaded)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap LibsignalCodeRoLoaded decodeErrorAtStackLen extract_withLsCodeRoLoaded
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost HighCalleeSaved IsDropSuffix SkipFieldGhost
   pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join sliceCursorAfter
   sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1 (EpochDirectionPB)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.ProtoRepr (epochDirectionPBAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   fitsEvents_append rustAllocEvents)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv DecodeErrorPushEnv decodeErrorFromBudgetSpec decodeErrorPushBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env BytesMerge3EnvCore WppBudgetPanic bytesMerge3RawBudgetSpec wppBudgetPanic_false)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (SkipField3Env skipField3Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23BudgetAux (mergeBytes_length_sum)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv SkipFieldEnv decodeVarintSliceEvents skipFieldEventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)

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

/-! ## 1. Shrinking-Slice Allocator Event Envelopes & Budget Specifications (Block `299`) -/

/-- Shrinking-slice allocator event envelope of `EpochDirection::merge` (Block `299`) on a
remaining byte slice of length at most `rem`:
- `nil`: `Ok` return (`cur.length = limit`), `0` events;
- `errFrom`: `DecodeError::from` return (`72`-byte `Box<Inner>`);
- `errFromPush`: `DecodeError::from` followed by `DecodeError::push` at stack length `0`;
- `stepBytes`: successful `bytes::merge` (`tag = 2` or `tag = 3`) on a sub-slice `bs` with
  `bs.length ≤ rem` and effective `valCap.toNat ≤ bs.length`, followed by `EpochDirectionLoopEnv rem`. -/
inductive EpochDirectionLoopEnv : Nat → List AllocEvent → Prop where
  | nil {rem : Nat} : EpochDirectionLoopEnv rem []
  | errFrom {rem : Nat} : EpochDirectionLoopEnv rem (rustAllocEvents 72 8)
  | errFromPush {rem : Nat} {evs_p : List AllocEvent} :
      DecodeErrorPushEnv 0 evs_p →
      EpochDirectionLoopEnv rem (rustAllocEvents 72 8 ++ evs_p)
  | stepBytes {rem : Nat} (wt : WireType) (valCap : BitVec 64) (bs : List (BitVec 8))
      {evs₁ evs₂ : List AllocEvent} :
      bs.length ≤ rem →
      valCap.toNat ≤ bs.length →
      BytesMerge3EnvCore wt valCap bs evs₁ →
      EpochDirectionLoopEnv rem evs₂ →
      EpochDirectionLoopEnv (rem + 1) (evs₁ ++ evs₂)

/-- Successful-return allocator event envelope of `EpochDirection::merge` (Block `299`),
bounded simultaneously by remaining slice length `rem` and consumed byte count `consumed`. -/
inductive EpochDirectionOkEnv : Nat → Nat → List AllocEvent → Prop where
  | nil {rem consumed : Nat} : EpochDirectionOkEnv rem consumed []
  | stepBytes {rem consumed : Nat} (wt : WireType) (valCap : BitVec 64) (bs : List (BitVec 8))
      {evs₁ evs₂ : List AllocEvent} :
      bs.length ≤ rem →
      valCap.toNat ≤ bs.length →
      BytesMerge3EnvCore wt valCap bs evs₁ →
      EpochDirectionOkEnv rem consumed evs₂ →
      EpochDirectionOkEnv (rem + 1) (consumed + 1) (evs₁ ++ evs₂)

theorem EpochDirectionLoopEnv.mono {rem₁ rem₂ : Nat} {evs : List AllocEvent}
    (hle : rem₁ ≤ rem₂) (h : EpochDirectionLoopEnv rem₁ evs) :
    EpochDirectionLoopEnv rem₂ evs := by
  induction h generalizing rem₂ with
  | nil => exact .nil
  | errFrom => exact .errFrom
  | errFromPush hp => exact .errFromPush hp
  | @stepBytes rem wt valCap bs evs₁ evs₂ hbs hcap hbm _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, rem₂ = k + 1 := ⟨rem₂ - 1, by omega⟩
    exact .stepBytes wt valCap bs (Nat.le_trans hbs (by omega)) hcap hbm (ih (by omega))

theorem EpochDirectionOkEnv.mono {rem₁ rem₂ c₁ c₂ : Nat} {evs : List AllocEvent}
    (hrem : rem₁ ≤ rem₂) (hc : c₁ ≤ c₂) (h : EpochDirectionOkEnv rem₁ c₁ evs) :
    EpochDirectionOkEnv rem₂ c₂ evs := by
  induction h generalizing rem₂ c₂ with
  | nil => exact .nil
  | @stepBytes rem consumed wt valCap bs evs₁ evs₂ hbs hcap hbm _ ih =>
    obtain ⟨kr, rfl⟩ : ∃ kr, rem₂ = kr + 1 := ⟨rem₂ - 1, by omega⟩
    obtain ⟨kc, rfl⟩ : ∃ kc, c₂ = kc + 1 := ⟨c₂ - 1, by omega⟩
    exact .stepBytes wt valCap bs (Nat.le_trans hbs (by omega)) hcap hbm
      (ih (by omega) (by omega))

theorem EpochDirectionOkEnv.toLoop {rem consumed : Nat} {evs : List AllocEvent}
    (h : EpochDirectionOkEnv rem consumed evs) :
    EpochDirectionLoopEnv rem evs := by
  induction h with
  | nil => exact .nil
  | stepBytes wt valCap bs hbs hcap hbm _ ih =>
    exact .stepBytes wt valCap bs hbs hcap hbm ih

/-- Precondition allocator event envelope of `EpochDirection::merge` (Block `299`). -/
def EpochDirectionMergeEnv (x : EpochDirectionMergeGhost) (evs : List AllocEvent) : Prop :=
  EpochDirectionLoopEnv x.bs.length evs

/-- Postcondition allocator event envelope of `EpochDirection::merge` (Block `299`):
`EpochDirectionOkEnv x.bs.length (x.bs.length - rest.length)` on `Ok`, and
`EpochDirectionLoopEnv x.bs.length` on `Err`. -/
def EpochDirectionMergePostEnv (x : EpochDirectionMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
  | some (_, rest) => EpochDirectionOkEnv x.bs.length (x.bs.length - rest.length) evs
  | none => EpochDirectionLoopEnv x.bs.length evs

theorem epochDirectionMergePostEnv_imp_pre {x : EpochDirectionMergeGhost} {evs : List AllocEvent}
    (h : EpochDirectionMergePostEnv x evs) :
    EpochDirectionMergeEnv x evs := by
  dsimp only [EpochDirectionMergePostEnv, EpochDirectionMergeEnv] at h ⊢
  split at h
  · exact h.toLoop
  · exact h

theorem decodeVarint2Env_of_some {bs : List (BitVec 8)} {p : BitVec 64 × List (BitVec 8)}
    {evs : List AllocEvent} (hdv : decodeVarint bs = some p) (h : DecodeVarint2Env bs evs) :
    evs = [] := by
  change DecodeVarintSliceEnv bs evs at h
  simpa [DecodeVarintSliceEnv, decodeVarintSliceEvents, hdv] using h

theorem decodeVarint2Env_of_none {bs : List (BitVec 8)} {evs : List AllocEvent}
    (hdv : decodeVarint bs = none) (h : DecodeVarint2Env bs evs) :
    evs = rustAllocEvents 72 8 := by
  change DecodeVarintSliceEnv bs evs at h
  simpa [DecodeVarintSliceEnv, decodeVarintSliceEvents, hdv] using h

theorem skipField3Env_of_some {g : SkipFieldGhost} {rest' : List (BitVec 8)}
    {evs : List AllocEvent}
    (hsf : skipField (2 * g.bs.length + 2) g.depth g.tag g.wt g.bs = some rest')
    (h : SkipField3Env g evs) :
    evs = [] := by
  change SkipFieldEnv g evs at h
  simpa [SkipFieldEnv, skipFieldEventsCore, hsf] using h

theorem skipField3Env_of_none {g : SkipFieldGhost} {evs : List AllocEvent}
    (hsf : skipField (2 * g.bs.length + 2) g.depth g.tag g.wt g.bs = none)
    (h : SkipField3Env g evs) :
    evs = rustAllocEvents 72 8 := by
  change SkipFieldEnv g evs at h
  simpa [SkipFieldEnv, skipFieldEventsCore, hsf] using h

/-- Effective-capacity reduction for `bytesMergeEventsCore`: when `mergeBytes wt bs = some (v, rest')`
with `bs.length < 2 ^ 63`, any capacity `valCap` with `v.length ≤ valCap.toNat` emits `[]` in
`doReserveClearEvents`, coinciding with `effCap := BitVec.ofNat 64 v.length` (`effCap.toNat ≤ bs.length`). -/
theorem bytesMergeEventsCore_effCap (wt : WireType) (valCap : BitVec 64)
    (bs : List (BitVec 8)) (hbs_lt : bs.length < 2 ^ 63) :
    (mergeBytes wt bs = none → bytesMergeEventsCore wt valCap bs = rustAllocEvents 72 8) ∧
    (∀ v rest', mergeBytes wt bs = some (v, rest') →
      ∃ effCap : BitVec 64,
        effCap.toNat ≤ bs.length ∧
        bytesMergeEventsCore wt valCap bs = bytesMergeEventsCore wt effCap bs) := by
  refine ⟨fun hmb => by simp [bytesMergeEventsCore, hmb], fun v rest' hmb => ?_⟩
  have hsum : 1 + v.length + rest'.length ≤ bs.length := mergeBytes_length_sum hmb
  have hv_le : v.length ≤ bs.length := by omega
  by_cases hcap : valCap.toNat ≤ v.length
  · exact ⟨valCap, Nat.le_trans hcap hv_le, rfl⟩
  · refine ⟨BitVec.ofNat 64 v.length, ?_, ?_⟩
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hv_le
    · have hle : v.length ≤ valCap.toNat := by omega
      have htn : v.length % 18446744073709551616 = v.length :=
        Nat.mod_eq_of_lt (by omega)
      simp [bytesMergeEventsCore, hmb, hle, htn, doReserveClearEvents]

theorem EpochDirectionLoopEnv.of_bytesMerge3 {rem : Nat} {g : BytesMergeGhost}
    {evs : List AllocEvent} (hbs : g.bs.length ≤ rem) (hlt : g.bs.length < 2 ^ 63)
    (hbm : BytesMerge3Env g evs) :
    EpochDirectionLoopEnv (rem + 1) evs := by
  obtain ⟨hnone_eq, hsome_eq⟩ := bytesMergeEventsCore_effCap g.wt g.valCap g.bs hlt
  cases hmb : mergeBytes g.wt g.bs with
  | none =>
    have heq : evs = rustAllocEvents 72 8 := by
      change evs = bytesMergeEventsCore g.wt g.valCap g.bs at hbm
      rw [hbm, hnone_eq hmb]
    rw [heq]; exact .errFrom
  | some p =>
    rcases p with ⟨v, rest'⟩
    obtain ⟨effCap, heff_le, heq_core⟩ := hsome_eq v rest' hmb
    have hbm_eff : BytesMerge3EnvCore g.wt effCap g.bs evs := by
      change evs = bytesMergeEventsCore g.wt g.valCap g.bs at hbm
      change evs = bytesMergeEventsCore g.wt effCap g.bs
      simpa [← heq_core] using hbm
    simpa using EpochDirectionLoopEnv.stepBytes g.wt effCap g.bs hbs heff_le hbm_eff .nil

theorem FitsEnv.epochDirection_decodeErrorFrom {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {rem : Nat} (hFit : FitsEnv M lim st (EpochDirectionLoopEnv rem)) :
    FitsEnv M lim st DecodeErrorFromEnv := by
  intro evs he; rw [he]; exact hFit _ .errFrom

theorem FitsEnv.epochDirection_decodeVarint2 {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {rem : Nat} (bs : List (BitVec 8))
    (hFit : FitsEnv M lim st (EpochDirectionLoopEnv rem)) :
    FitsEnv M lim st (DecodeVarint2Env bs) := by
  intro evs he
  cases hdv : decodeVarint bs with
  | none => rw [decodeVarint2Env_of_none hdv he]; exact hFit _ .errFrom
  | some p => rw [decodeVarint2Env_of_some hdv he]; exact hFit _ .nil

theorem FitsEnv.epochDirection_skipField3 {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {rem : Nat} (g : SkipFieldGhost)
    (hFit : FitsEnv M lim st (EpochDirectionLoopEnv rem)) :
    FitsEnv M lim st (SkipField3Env g) := by
  intro evs he
  cases hsf : skipField (2 * g.bs.length + 2) g.depth g.tag g.wt g.bs with
  | none => rw [skipField3Env_of_none hsf he]; exact hFit _ .errFrom
  | some rest' => rw [skipField3Env_of_some hsf he]; exact hFit _ .nil

theorem FitsEnv.epochDirection_push0_after_from {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {rem : Nat} (hFit : FitsEnv M lim st (EpochDirectionLoopEnv rem)) :
    FitsEnv M lim (M.stepEvents (rustAllocEvents 72 8) st) (DecodeErrorPushEnv 0) :=
  fun evs_p hp =>
    ((fitsEvents_append M lim (rustAllocEvents 72 8) evs_p st).mp
      (hFit (rustAllocEvents 72 8 ++ evs_p) (.errFromPush hp))).2

theorem FitsEnv.epochDirection_bytesMerge3 {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {rem : Nat} {g : BytesMergeGhost}
    (hbs : g.bs.length ≤ rem) (hlt : g.bs.length < 2 ^ 63)
    (hFit : FitsEnv M lim st (EpochDirectionLoopEnv (rem + 1))) :
    FitsEnv M lim st (BytesMerge3Env g) :=
  fun evs hbm => hFit evs (EpochDirectionLoopEnv.of_bytesMerge3 hbs hlt hbm)

/-- Envelope-parameterized budget-threaded contract of
`prost::encoding::message::merge::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, &mut &[u8]>`
(Block `299`). -/
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
      match (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          epochDirectionPBCapOkAt A.repAlloc x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 1⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : EpochDirectionPB, epochDirectionPBAt A.repAlloc x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of
`prost::encoding::message::merge::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, &mut &[u8]>`
(Block `299`, `onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def epochDirectionMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (EpochDirectionMergeGhost × M.σ) :=
  epochDirectionMergeSpecOfEnv A lim EpochDirectionMergeEnv EpochDirectionMergePostEnv

/-- Envelope monotonicity for `epochDirectionMergeSpecOfEnv`. -/
theorem subroutine_ok_epochDirectionMergeOfEnv {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    {Pre₁ Post₁ Pre₂ Post₂ : EpochDirectionMergeGhost → List AllocEvent → Prop}
    (hpre : ∀ x evs, Pre₁ x evs → Pre₂ x evs)
    (hpost : ∀ x evs, Post₁ x evs → Post₂ x evs)
    (h : subroutine_ok prog entry (epochDirectionMergeSpecOfEnv A lim Pre₁ Post₁)) :
    subroutine_ok prog entry (epochDirectionMergeSpecOfEnv A lim Pre₂ Post₂) := by
  refine subroutine_ok_mono h
    (fun ⟨x, st⟩ R s0 hp => ?_)
    (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · dsimp only [epochDirectionMergeSpecOfEnv] at hp ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1, hp.1.2.2.2.2.mono (hpre x)⟩, hp.2⟩
  · dsimp only [epochDirectionMergeSpecOfEnv] at hq ⊢
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (Entails.sepExists_mono fun evs =>
        Entails.pure_left fun h1 => Entails.pure_right (hpost x evs h1) (Entails.of_eq rfl)))))) hq

/-- `withLsCodeLoaded` envelope monotonicity for `epochDirectionMergeSpecOfEnv`. -/
theorem subroutine_ok_withLsCodeLoaded_epochDirectionMergeOfEnv {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {pl : Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64}
    {Pre₁ Post₁ Pre₂ Post₂ : EpochDirectionMergeGhost → List AllocEvent → Prop}
    (hpre : ∀ x evs, Pre₁ x evs → Pre₂ x evs)
    (hpost : ∀ x evs, Post₁ x evs → Post₂ x evs)
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (epochDirectionMergeSpecOfEnv A lim Pre₁ Post₁))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (epochDirectionMergeSpecOfEnv A lim Pre₂ Post₂)) := by
  refine subroutine_ok_mono h
    (fun ⟨x, st⟩ R s0 hp => ?_)
    (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · obtain ⟨hcl, hp⟩ := extract_withLsCodeLoaded hp
    dsimp only [withLsCodeLoaded, epochDirectionMergeSpecOfEnv] at hp ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1, hp.1.2.2.2.2.mono (hpre x)⟩, hp.2⟩
  · dsimp only [withLsCodeLoaded, epochDirectionMergeSpecOfEnv] at hq ⊢
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (Entails.sepExists_mono fun evs =>
        Entails.pure_left fun h1 => Entails.pure_right (hpost x evs h1) (Entails.of_eq rfl)))))) hq

/-- `withLsCodeRoLoaded` envelope monotonicity for `epochDirectionMergeSpecOfEnv`. -/
theorem subroutine_ok_withLsCodeRoLoaded_epochDirectionMergeOfEnv {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {pl : Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64}
    {Pre₁ Post₁ Pre₂ Post₂ : EpochDirectionMergeGhost → List AllocEvent → Prop}
    (hpre : ∀ x evs, Pre₁ x evs → Pre₂ x evs)
    (hpost : ∀ x evs, Post₁ x evs → Post₂ x evs)
    (h : subroutine_ok prog entry (withLsCodeRoLoaded pl (epochDirectionMergeSpecOfEnv A lim Pre₁ Post₁))) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl (epochDirectionMergeSpecOfEnv A lim Pre₂ Post₂)) := by
  refine subroutine_ok_mono h
    (fun ⟨x, st⟩ R s0 hp => ?_)
    (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · obtain ⟨hcro, hp⟩ := extract_withLsCodeRoLoaded hp
    dsimp only [withLsCodeRoLoaded, epochDirectionMergeSpecOfEnv] at hp ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1, hp.1.2.2.2.2.mono (hpre x)⟩, hp.2⟩
  · dsimp only [withLsCodeRoLoaded, epochDirectionMergeSpecOfEnv] at hq ⊢
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (Entails.sepExists_mono fun evs =>
        Entails.pure_left fun h1 => Entails.pure_right (hpost x evs h1) (Entails.of_eq rfl)))))) hq

/-! ## 2. Loop & Error-Exit Separation-Logic Bundles and Shared Exit/Arm Lemmas (Block `299`) -/

/-- Budget-threaded loop-header separation-logic bundle at `+0x0a0` (`(blkPl_299).base + 160#64`). -/
def epochDirectionLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s0 s : State) (msgPtr bufRef slot ptr : BitVec 64)
    (m : EpochDirectionPB) (bs cur : List (BitVec 8)) : SepProp :=
  epochDirectionPBCapOkAt A.repAlloc msgPtr cur.length m ∗
    memRegion (s0.sp - 96#64) 48 ∗ skipBelow3 s0.sp 98 ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
    (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗ A.pool lim st s

/-- Budget-threaded error-exit separation-logic bundle at `+0x068`, `+0x074`, `+0x204`, `+0x224`
of Block `299`. -/
def epochDirectionErrFrame {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s0 s : State) (msgPtr bufRef slot ptr : BitVec 64)
    (m : EpochDirectionPB) (bs : List (BitVec 8)) : SepProp :=
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
    epochDirectionPBAt A.repAlloc msgPtr m ∗ (bufRef ↦₆₄ slot) ∗
    memRegion slot 16 ∗ (ptr ↦ₛ bs) ∗ A.pool lim st s

/-- Placed shared exit from `+0x074` (`(blkPl_299).base + 116#64`) when `x1 = err ≠ 0#64` owns
`decodeErrorAtStackLen A.repAlloc err 0`. -/
theorem epochDirection_err0_ret_exit_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop}
    {x : EpochDirectionMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : EpochDirectionPB} {err : BitVec 64}
    (hnone : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hevs : ∃ evs, PostEnv x evs ∧ st_cur = M.stepEvents evs st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_299).base + 116#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (herr : err ≠ 0#64) (hcs : HighCalleeSaved s0 s) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err 0 ∗ memRegion (s0.sp - 96#64) 48 ∗
        skipBelow3 s0.sp 98 ∗
        epochDirectionErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  rcases hevs with ⟨evs, hevs_post, rfl⟩
  apply SepWPp.of_sepWP_ret
  unfold WppPost epochDirectionMergeSpecOfEnv
  simp only [hnone, stackAt_skipField3 _ 98 (by decide), epochDirectionErrFrame,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx1]
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A.repAlloc err) (by sep_focus)
  apply SepWP.fold (epochDirectionPBAt_entails_exists A.repAlloc x.msgPtr m) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  wp_done

/-- Code-loaded placed shared exit from `+0x068` (`(blkPl_299).base + 104#64`): calls
`DecodeError::from` on `(s0.sp - 96#64, w, st_cur)` and returns at `+0x070..+0x088`. -/
theorem epochDirection_from_err_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop}
    (hFromCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : EpochDirectionMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : EpochDirectionPB} {w : BitVec 64}
    (hnone : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hw : KindNoHeap w)
    (hfits_from : FitsEnv M lim st_cur DecodeErrorFromEnv)
    (hevs_from : ∀ evs_f, DecodeErrorFromEnv evs_f →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_f st_cur = M.stepEvents evs st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_299).base + 104#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hcs : HighCalleeSaved s0 s)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 96#64) ↦₆₄ w) ∗ memRegion (s0.sp - 88#64) 40 ∗
        skipBelow3 s0.sp 98 ∗
        epochDirectionErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := lsmpl.base 261) hinv
  conv => arg 4; rw [skipBelow3_err s0.sp 98 (by decide), epochDirectionErrFrame]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 261)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.call_frame_lscro (spec := decodeErrorFromBudgetSpec M A lim)
    (x := (s0.sp - 96#64, w, st_cur))
    (ret_pc := (blkPl_299).base + 112#64) hFromCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp], hw, hfits_from⟩ (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm _hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hspm hx19 hx20 hx21 hx22 hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp hvregs_m
  apply SepWPp.of_sepWP_ret
  unfold WppPost epochDirectionMergeSpecOfEnv
  simp only [decodeErrorFromBudgetSpec, hnone, stackAt_skipField3 _ 98 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, htr, hsp, hspm]
  apply SepWP.exists_elim; intro evs_f
  wp_focus_pure; rintro ⟨_herr, htrm⟩
  wp_focus_pure; intro hevs_f
  obtain ⟨evs, hevs_post, hst_eq⟩ := hevs_from evs_f hevs_f
  conv => arg 4; simp only [hst_eq, arm64_norm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 98 (by decide)) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48 s0.sp) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A.repAlloc _) (by sep_focus)
  apply SepWP.fold (epochDirectionPBAt_entails_exists A.repAlloc x.msgPtr m) (by sep_focus)
  wp_done

/-- Code-loaded placed shared exit from `+0x224` (`(blkPl_299).base + 548#64`): calls
`DecodeError::push` on `(s0.sp - 96#64, err, 0, st_cur)` and returns at `+0x228..+0x088`. -/
theorem epochDirection_push_err_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop}
    (hPushCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    {x : EpochDirectionMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : EpochDirectionPB} {err : BitVec 64}
    (hnone : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64)
    (hfits_push : FitsEnv M lim st_cur (DecodeErrorPushEnv 0))
    (hevs_push : ∀ evs_p, DecodeErrorPushEnv 0 evs_p →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_p st_cur = M.stepEvents evs st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_299).base + 548#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 96#64)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 96#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗
        memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗
        epochDirectionErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := lsmpl.base 257) hinv
  conv => arg 4; rw [skipBelow3_err s0.sp 98 (by decide), epochDirectionErrFrame]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 257)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.call_frame_lscro (spec := decodeErrorPushBudgetSpec M A lim)
    (x := (s0.sp - 96#64, err, 0, st_cur))
    (ret_pc := (blkPl_299).base + 552#64) hPushCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp, hx0], by decide, hfits_push⟩ (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm _hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hspm hx19 hx20 hx21 hx22 hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp hvregs_m
  apply SepWPp.of_sepWP_ret
  unfold WppPost epochDirectionMergeSpecOfEnv
  simp only [decodeErrorPushBudgetSpec, hnone, stackAt_skipField3 _ 98 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, htr, hsp, hspm]
  apply SepWP.exists_elim; intro evs_p
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_p
  obtain ⟨evs, hevs_post, hst_eq⟩ := hevs_push evs_p hevs_p
  conv => arg 4; simp only [hst_eq, arm64_norm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 98 (by decide)) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  apply SepWP.fold (decodeErrorWith_one_entails_le1 A.repAlloc err) (by sep_focus)
  apply SepWP.fold (epochDirectionPBAt_entails_exists A.repAlloc x.msgPtr m) (by sep_focus)
  apply SepWP.fold (pointsTo64_memRegion40_entails_48 s0.sp err) (by sep_focus)
  wp_done

/-- Code-loaded placed step lemma for unknown field tags (`tag ∉ {1, 2, 3}`) at `+0x08c`
(`(blkPl_299).base + 140#64`). -/
theorem epochDirection_skip_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop}
    (hSkipCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : EpochDirectionMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : EpochDirectionPB} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hfits_sf : FitsEnv M lim st_cur
      (SkipField3Env ⟨iwt, tag, 97, x.bufRef, x.slot, x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩))
    (hevs_sf_err : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      ∀ evs_sf,
        SkipField3Env ⟨iwt, tag, 97, x.bufRef, x.slot, x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_sf →
        ∃ evs, PostEnv x evs ∧ M.stepEvents evs_sf st_cur = M.stepEvents evs st0)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_299).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s'
        (epochDirectionLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_299).base + 140#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := lsmpl.base 263) hinv
  conv => arg 4; rw [epochDirectionLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_98_eq_stackAt_97 s0.sp]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 263)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.call_frame_lscro (spec := skipField3Spec A lim)
    (x := (⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_299).base + 152#64) hSkipCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl
    ⟨by simp only [arm64_norm, hsp, hx0, setWidth8_ofNat64_wt],
     by simp only [arm64_norm, hsp, hx1], htag_lt,
     by simp only [arm64_norm, hsp, hx19],
     by simp only [arm64_norm, hsp], (by decide : 97 < 2 ^ 32), hrest_lt, hfits_sf⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 97 tag iwt rest with
  | none =>
    have hnone := hnone_of_sf hsf
    apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 116#64) hinvm
    (conv => arg 4; simp only [skipField3Spec, hsf, ← skipBelow3_98_eq_stackAt_97,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_sf
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_sf
    wp_focus_pure; intro hsm0
    conv => arg 4; simp only [arm64_norm, hsp]
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A.repAlloc x.msgPtr rest.length m) (by sep_focus)
    wp_steps_sync_pool ((blkPl_299).base + 116#64)
    simp only [State.setMem_setMem]
    wp_reach; intro _hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [epochDirectionErrFrame]; sep_ac_rfl))
      (epochDirection_err0_ret_exit_placed hnone (hevs_sf_err hsf evs_sf hevs_sf) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) hsm0
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩)
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 160#64) hinvm
    (conv => arg 4; simp only [skipField3Spec, hsf, ← skipBelow3_98_eq_stackAt_97,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_sf
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_sf
    wp_focus_pure; intro hsm0
    have hevs_nil : evs_sf = [] := skipField3Env_of_some hsf hevs_sf
    subst hevs_nil
    conv => arg 4; dsimp only [LibsignalBinary.Heap.AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (epochDirectionPBCapOkAt_mono hrest'_le) (by sep_focus)
    wp_steps_sync_pool ((blkPl_299).base + 160#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [epochDirectionLoopPre]; sep_ac_rfl))
      (hcont rest' _ hsf
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm')

/-- Code-loaded placed shared exit for tag 1 (`ctr`) from `+0x204` (`(blkPl_299).base + 516#64`). -/
theorem epochDirection_tag1_push_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop}
    (hPushCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    {x : EpochDirectionMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : EpochDirectionPB} {err : BitVec 64}
    (hnone : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64)
    (hfits_push : FitsEnv M lim st_cur (DecodeErrorPushEnv 0))
    (hevs_push : ∀ evs_p, DecodeErrorPushEnv 0 evs_p →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_p st_cur = M.stepEvents evs st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_299).base + 516#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx8 : s.readReg64 (Reg.gpr 8#5) = err)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err 0 ∗ memRegion (s0.sp - 96#64) 48 ∗
        skipBelow3 s0.sp 98 ∗
        epochDirectionErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 548#64) hinv
  conv => arg 4; rw [sepConj_memRegion_48_split_96, epochDirectionErrFrame]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_stk0
  wp_steps_sync_pool ((blkPl_299).base + 548#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.weaken_pre (by dsimp only [epochDirectionErrFrame]; sep_entail)
    (epochDirection_push_err_exit_cl_placed hPushCall hnone herr hfits_push hevs_push hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hsp])
      ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24],
       by simp only [arm64_norm, hx25], by simp only [arm64_norm, hx26],
       by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28],
       by simp only [arm64_norm, hvregs]⟩ hinv)

/-- Code-loaded placed step lemma for tag 1 (`ctr`) at `+0x11c` (`(blkPl_299).base + 284#64`)
when `iwt ≠ .varint`. -/
theorem epochDirection_tag1_wt_err_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop}
    (hFromCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    {x : EpochDirectionMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : EpochDirectionPB} {rest : List (BitVec 8)} {iwt : WireType}
    (hiwt : iwt ≠ .varint) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hfits_from : FitsEnv M lim st_cur DecodeErrorFromEnv)
    (hfits_push : FitsEnv M lim (M.stepEvents (rustAllocEvents 72 8) st_cur) (DecodeErrorPushEnv 0))
    (hevs_from_push : ∀ evs_p, DecodeErrorPushEnv 0 evs_p →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs_p (M.stepEvents (rustAllocEvents 72 8) st_cur) = M.stepEvents evs st0)
    (hnone : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hpc : s.pc = (blkPl_299).base + 284#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hcbnz := iwt_cbnz_true_of_ne_varint hiwt
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := lsmpl.base 261) hinv
  conv => arg 4; rw [epochDirectionLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    sliceCursorAt, memRegion_48_wtErr96 s0.sp, skipBelow3_err s0.sp 98 (by decide)]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
  wp_steps_sync_pool (lsmpl.base 261)
  simp only [State.setMem_setMem]
  apply SepWP.fold (wtErr96_entails_memRegion40 s0.sp _ _) (by sep_focus)
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
  apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A.repAlloc x.msgPtr rest.length m) (by sep_focus)
  wp_reach; intro hinv
  refine CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.call_frame_lscro (spec := decodeErrorFromBudgetSpec M A lim)
    (x := (s0.sp - 96#64, 0x8000000000000006#64, st_cur))
    (ret_pc := (blkPl_299).base + 512#64) hFromCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp], (by decide : KindNoHeap 0x8000000000000006#64), hfits_from⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 516#64) hinvm
  (conv => arg 4; simp only [decodeErrorFromBudgetSpec, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro evs_f
  wp_focus_pure; rintro ⟨hve_ne, htrm⟩
  wp_focus_pure; intro hevs_f
  rw [hevs_f]
  conv => arg 4; simp only [arm64_norm, hsp]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 98 (by decide)) (by sep_focus)
  wp_steps_sync_pool ((blkPl_299).base + 516#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinvm
  refine SepWPp.weaken_pre (by dsimp only [epochDirectionErrFrame]; sep_entail)
    (epochDirection_tag1_push_exit_cl_placed hPushCall hnone hve_ne hfits_push hevs_from_push hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm)

/-- Code-loaded placed step lemma for tag 1 (`ctr`) at `+0x11c` (`(blkPl_299).base + 284#64`)
when `iwt = .varint`. -/
theorem epochDirection_tag1_varint_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop}
    (hPushCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : EpochDirectionMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : EpochDirectionPB} {rest : List (BitVec 8)} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hfits_dv : FitsEnv M lim st_cur (DecodeVarint2Env rest))
    (hfits_push : decodeVarint rest = none →
      FitsEnv M lim (M.stepEvents (rustAllocEvents 72 8) st_cur) (DecodeErrorPushEnv 0))
    (hevs_dv_push : decodeVarint rest = none →
      ∀ evs_p, DecodeErrorPushEnv 0 evs_p →
        ∃ evs, PostEnv x evs ∧
          M.stepEvents evs_p (M.stepEvents (rustAllocEvents 72 8) st_cur) = M.stepEvents evs st0)
    (hnone_of_dv : decodeVarint rest = none →
      (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_299).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s'
        (epochDirectionLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with ctr := v.truncate 32 } x.bs rest')
        (WppPost (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_299).base + 284#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
  conv => arg 4; rw [epochDirectionLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_leaf s0.sp 98 (by decide)]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_299).base + 296#64) hVarintCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp, hx19], hrest_lt, hfits_dv⟩ (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hdv : decodeVarint rest with
  | none =>
    have hnone := hnone_of_dv hdv
    apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 516#64) hinvm
    (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_dv
    wp_focus_pure; intro hsm0
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_dv
    wp_focus_pure; intro hsm1
    rw [decodeVarint2Env_of_none hdv hevs_dv]
    conv => arg 4; simp only [arm64_norm, hsp]
    have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A.repAlloc x.msgPtr rest.length m) (by sep_focus)
    wp_steps_sync_pool ((blkPl_299).base + 516#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm
    refine SepWPp.weaken_pre (by dsimp only [epochDirectionErrFrame]; sep_entail)
      (epochDirection_tag1_push_exit_cl_placed hPushCall hnone hsm1
        (hfits_push hdv) (hevs_dv_push hdv) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm)
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
    apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 160#64) hinvm
    (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv, epochDirectionPBCapOkAt,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_dv
    wp_focus_pure; rintro ⟨hsm0, hsm1⟩
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_dv
    have hevs_nil : evs_dv = [] := decodeVarint2Env_of_some hdv hevs_dv
    subst hevs_nil
    conv => arg 4; dsimp only [LibsignalBinary.Heap.AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (@vecU8CapOkAt_mono A.repAlloc x.msgPtr rest.length rest'.length m.next hrest'_le) (by sep_focus)
    apply SepWP.fold (@vecU8CapOkAt_mono A.repAlloc (x.msgPtr + 0x18#64) rest.length rest'.length m.prev hrest'_le) (by sep_focus)
    wp_steps_sync_pool ((blkPl_299).base + 160#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm
    refine SepWPp.weaken_pre (by dsimp only [epochDirectionLoopPre, epochDirectionPBCapOkAt]; sep_entail)
      (hcont v rest' _ hdv
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux
