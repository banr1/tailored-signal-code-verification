/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.DefsClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergeCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Shared Budget Envelopes & Contracts for `PolynomialDecoder::merge` and `PolynomialEncoder::merge`

Defines `BytesMerge3Env`, `PolyMergeIterEnv`, `PolyMergeLoopEnv`, budget contracts
`polyDecoderMergeSpec{OfEnv,}` and `polyEncoderMergeSpec{OfEnv,}`, loop/error frames, and
relocatable Block `296` shared exit and unknown-tag skip lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint mergeBytes skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap LibsignalCodeRoLoaded decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost IsDropSuffix pointsToBytes_prefix_join
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1 (GrowOneCall PolynomialDecoder PolynomialEncoder)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Poly (protoPolynomialDecoderAt protoPolynomialEncoderAt)
open CryptoVerification.SpqrV1.Prost.BytesMerge (bytesMerge3Stack)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (PolyCalleeSaved PolyDecoderMergeGhost PolyEncoderMergeGhost SepWPp.call_frame_lscro
   SepWPp.of_sepWP_lscro WppPost blkPC_296 blkPl_296 codecWireTypeToProto
   decodeErrorWith_one_entails_le1 decodeErrorWith_zero_entails_le1
   memRegion8_memRegion40_entails_48_160 pointsTo64_memRegion40_entails_48_160 polyBelowStack
   polyBelow_decodeErrorHook polyBelow_decodeErrorHook_entails polyDecoderToProto
   polyEncoderToProto polyMergeStack polySavedRegs polySavedRegsAny
   protoPolynomialDecoderAt_entails_exists protoPolynomialEncoderAt_entails_exists
   setWidth8_ofNat64_wt stackAt_polyMerge_epilogue)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   fitsEvents_append rustAllocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (GrowOneVecU8Env growOneVecU8BudgetSpec)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (DecodeErrorPushMergeEnv SpqrMergeLoopEnv SpqrMergeSmallStep
   decodeErrorPushMergeBudgetSpec mergeBytes_len_bound
   spqrMergeLoopEnv_fitsEnv_witness spqrMergeWitnessLimits spqrWitnessBytes)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (DecodeVarint2Env decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (SkipField3Env skipField3Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv SkipFieldEnv decodeVarintSliceEvents skipFieldEventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (bytesMergeEventsCore)

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

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre calleeSavedVRegs_setMem_pre

/-! ## 1. `BytesMerge3` Budget Contract & Callee-Closed `PolyMergeLoopEnv` -/

/-- Callee-fixed pointer-independent allocator event envelope of
`prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>` (Block `290`, definitionally equal to
`ChunkedDefsBudget.BytesMerge3EnvCore` and matching `MergeDefsBudget.bytesMergeEventsCore`). -/
abbrev BytesMerge3EnvCore : WireType → BitVec 64 → List (BitVec 8) → List AllocEvent → Prop :=
  LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget.BytesMerge3EnvCore

/-- Allocator event envelope of `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>` (Block `290`). -/
abbrev BytesMerge3Env (x : BytesMergeGhost) : List AllocEvent → Prop :=
  BytesMerge3EnvCore x.wt x.valCap x.bs

/-- Budget-threaded raw contract of `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>`
(Block `290`, counterpart of `CryptoVerification.SpqrV1.Prost.BytesMerge.bytesMerge3RawSpec`). -/
def bytesMerge3RawBudgetSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BytesMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      BytesMergeCapOk x.valCap x.bs.length ∧ FitsEnv M lim st (BytesMerge3Env x)⌝ ∗
      vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp bytesMerge3Stack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜BytesMerge3Env x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp bytesMerge3Stack ∗
      match mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
            ⌜BytesMergeCapOk cap' rest.length⌝ ∗ vecU8At A.repAlloc x.valPtr cap' ptr' v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Single constant- or capacity-bounded step inside `PolynomialDecoder::merge` /
`PolynomialEncoder::merge` with `Vec<Vec<u8>>` capacity bounded by `polyCapBound`. -/
inductive PolyMergeSmallStep (polyCapBound : Nat) : List AllocEvent → Prop where
  | nil : PolyMergeSmallStep polyCapBound []
  | fromErr : PolyMergeSmallStep polyCapBound (rustAllocEvents 72 8)
  | pushErr {n : Nat} {evs : List AllocEvent} :
      n ≤ 1 → DecodeErrorPushMergeEnv n evs → PolyMergeSmallStep polyCapBound evs
  | bytesMergeErr (wt : WireType) (valCap : BitVec 64) (bs : List (BitVec 8))
      {evs : List AllocEvent} :
      mergeBytes wt bs = none →
      BytesMerge3EnvCore wt valCap bs evs → PolyMergeSmallStep polyCapBound evs
  | growVecU8 (g : GrowOneCall) {evs : List AllocEvent} :
      g.cap.toNat < polyCapBound → GrowOneVecU8Env g evs → PolyMergeSmallStep polyCapBound evs

/-- Single non-payload step envelope (`nil`, `fromErr`, `pushErr`, `bytesMergeErr`, `growVecU8`) at capacity bound `polyCapBound`. -/
abbrev PolyMergeIterEnv (_maxLen polyCapBound : Nat) : List AllocEvent → Prop :=
  PolyMergeSmallStep polyCapBound

theorem PolyMergeSmallStep.mono {poly₁ poly₂ : Nat} {evs : List AllocEvent}
    (hpoly : poly₁ ≤ poly₂) (h : PolyMergeSmallStep poly₁ evs) :
    PolyMergeSmallStep poly₂ evs := by
  cases h with
  | nil => exact .nil
  | fromErr => exact .fromErr
  | pushErr hn hp => exact .pushErr hn hp
  | bytesMergeErr wt valCap bs hm hb => exact .bytesMergeErr wt valCap bs hm hb
  | growVecU8 g hc hg => exact .growVecU8 g (Nat.lt_of_lt_of_le hc hpoly) hg

theorem PolyMergeIterEnv.mono {maxLen₁ maxLen₂ poly₁ poly₂ : Nat} {evs : List AllocEvent}
    (_hlen : maxLen₁ ≤ maxLen₂) (hpoly : poly₁ ≤ poly₂)
    (h : PolyMergeIterEnv maxLen₁ poly₁ evs) :
    PolyMergeIterEnv maxLen₂ poly₂ evs :=
  PolyMergeSmallStep.mono hpoly h

theorem PolyMergeIterEnv.of_decodeErrorFrom {maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (h : DecodeErrorFromEnv evs) : PolyMergeIterEnv maxLen polyCapBound evs := by
  rw [h]; exact .fromErr

theorem PolyMergeIterEnv.of_decodeErrorPush0 {maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (h : DecodeErrorPushMergeEnv 0 evs) : PolyMergeIterEnv maxLen polyCapBound evs :=
  .pushErr (Nat.zero_le 1) h

theorem PolyMergeIterEnv.of_decodeVarint2 {maxLen polyCapBound : Nat} {bs : List (BitVec 8)}
    {evs : List AllocEvent} (h : DecodeVarint2Env bs evs) :
    PolyMergeIterEnv maxLen polyCapBound evs := by
  change DecodeVarintSliceEnv bs evs at h
  rw [h]; unfold decodeVarintSliceEvents
  cases decodeVarint bs
  · exact .fromErr
  · exact .nil

theorem PolyMergeIterEnv.of_skipField3 {maxLen polyCapBound : Nat}
    {x : CryptoVerification.LibsignalTripleRatchet.Prost.SkipFieldGhost}
    {evs : List AllocEvent} (h : SkipFieldEnv x evs) :
    PolyMergeIterEnv maxLen polyCapBound evs := by
  rw [h]; unfold skipFieldEventsCore
  cases skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs
  · exact .fromErr
  · exact .nil

theorem PolyMergeIterEnv.of_bytesMerge3Err {maxLen polyCapBound : Nat} {x : BytesMergeGhost}
    {evs : List AllocEvent} (hm : mergeBytes x.wt x.bs = none) (h : BytesMerge3Env x evs) :
    PolyMergeIterEnv maxLen polyCapBound evs :=
  .bytesMergeErr x.wt x.valCap x.bs hm h

theorem PolyMergeIterEnv.of_growOneVecU8 {maxLen polyCapBound : Nat} {g : GrowOneCall}
    {evs : List AllocEvent} (hc : g.cap.toNat < polyCapBound) (h : GrowOneVecU8Env g evs) :
    PolyMergeIterEnv maxLen polyCapBound evs :=
  .growVecU8 g hc h

/-- Linear-budget sequential allocation envelope of `PolynomialDecoder::merge` /
`PolynomialEncoder::merge` on an input slice of length at most `maxLen` with `Vec<Vec<u8>>`
capacity bounded by `polyCapBound`:
* `step` charges `1` budget unit for a bounded `PolyMergeSmallStep polyCapBound` event list;
* `bytesStep` charges `2 * v.length + 1` budget units for a successful
  `mergeBytes wt bs = some (v, rest)` on `bs.length ≤ maxLen`. -/
inductive PolyMergeLoopEnv : Nat → Nat → Nat → List AllocEvent → Prop where
  | nil {fuel maxLen polyCapBound : Nat} : PolyMergeLoopEnv fuel maxLen polyCapBound []
  | step {fuel maxLen polyCapBound : Nat} {evs₁ evs₂ : List AllocEvent} :
      PolyMergeSmallStep polyCapBound evs₁ →
      PolyMergeLoopEnv fuel maxLen polyCapBound evs₂ →
      PolyMergeLoopEnv (fuel + 1) maxLen polyCapBound (evs₁ ++ evs₂)
  | bytesStep {fuel maxLen polyCapBound : Nat} (wt : WireType) (valCap : BitVec 64)
      (bs v rest : List (BitVec 8)) {evs₁ evs₂ : List AllocEvent} :
      mergeBytes wt bs = some (v, rest) →
      bs.length ≤ maxLen →
      BytesMerge3EnvCore wt valCap bs evs₁ →
      PolyMergeLoopEnv fuel maxLen polyCapBound evs₂ →
      PolyMergeLoopEnv (fuel + 2 * v.length + 1) maxLen polyCapBound (evs₁ ++ evs₂)

theorem PolyMergeLoopEnv.single {fuel maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (h : PolyMergeIterEnv maxLen polyCapBound evs) :
    PolyMergeLoopEnv (fuel + 1) maxLen polyCapBound evs := by
  simpa using PolyMergeLoopEnv.step (fuel := fuel) (maxLen := maxLen) h .nil

theorem PolyMergeLoopEnv.bytesSingle {fuel maxLen polyCapBound : Nat}
    {wt : WireType} {valCap : BitVec 64} {bs v rest : List (BitVec 8)} {evs : List AllocEvent}
    (hm : mergeBytes wt bs = some (v, rest))
    (hbs : bs.length ≤ maxLen)
    (hb : BytesMerge3EnvCore wt valCap bs evs) :
    PolyMergeLoopEnv (fuel + 2 * v.length + 1) maxLen polyCapBound evs := by
  simpa using
    PolyMergeLoopEnv.bytesStep (fuel := fuel) (maxLen := maxLen) (polyCapBound := polyCapBound)
      wt valCap bs v rest hm hbs hb .nil

theorem PolyMergeLoopEnv.mono_fuel {fuel₁ fuel₂ maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (hle : fuel₁ ≤ fuel₂) (h : PolyMergeLoopEnv fuel₁ maxLen polyCapBound evs) :
    PolyMergeLoopEnv fuel₂ maxLen polyCapBound evs := by
  induction h generalizing fuel₂ with
  | nil => exact .nil
  | @step fuel _ _ evs₁ evs₂ h1 _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, fuel₂ = k + 1 := ⟨fuel₂ - 1, by omega⟩
    exact .step h1 (ih (by omega))
  | @bytesStep fuel _ _ wt valCap bs v rest evs₁ evs₂ hm hbs hb _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, fuel₂ = k + 2 * v.length + 1 :=
      ⟨fuel₂ - (2 * v.length + 1), by omega⟩
    exact .bytesStep wt valCap bs v rest hm hbs hb (ih (by omega))

theorem PolyMergeLoopEnv.mono {f₁ f₂ maxLen₁ maxLen₂ poly₁ poly₂ : Nat} {evs : List AllocEvent}
    (hf : f₁ ≤ f₂) (hlen : maxLen₁ ≤ maxLen₂) (hpoly : poly₁ ≤ poly₂)
    (h : PolyMergeLoopEnv f₁ maxLen₁ poly₁ evs) :
    PolyMergeLoopEnv f₂ maxLen₂ poly₂ evs := by
  induction h generalizing f₂ with
  | nil => exact .nil
  | @step fuel _ _ evs₁ evs₂ h1 _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, f₂ = k + 1 := ⟨f₂ - 1, by omega⟩
    exact .step (h1.mono hpoly) (ih (by omega) hlen hpoly)
  | @bytesStep fuel _ _ wt valCap bs v rest evs₁ evs₂ hm hbs hb _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, f₂ = k + 2 * v.length + 1 :=
      ⟨f₂ - (2 * v.length + 1), by omega⟩
    exact .bytesStep wt valCap bs v rest hm (Nat.le_trans hbs hlen) hb (ih (by omega) hlen hpoly)

theorem PolyMergeLoopEnv.append {f₁ f₂ maxLen polyCapBound : Nat} {evs₁ evs₂ : List AllocEvent}
    (h₁ : PolyMergeLoopEnv f₁ maxLen polyCapBound evs₁)
    (h₂ : PolyMergeLoopEnv f₂ maxLen polyCapBound evs₂) :
    PolyMergeLoopEnv (f₁ + f₂) maxLen polyCapBound (evs₁ ++ evs₂) := by
  induction h₁ with
  | @nil fuel _ _ =>
    simpa using h₂.mono_fuel (Nat.le_add_left f₂ fuel)
  | @step fuel _ _ e₁ e₂ head _ ih =>
    rw [List.append_assoc, show fuel + 1 + f₂ = (fuel + f₂) + 1 by omega]
    exact .step head (ih h₂)
  | @bytesStep fuel _ _ wt valCap bs v rest e₁ e₂ hm hbs hb _ ih =>
    rw [List.append_assoc,
      show fuel + 2 * v.length + 1 + f₂ = (fuel + f₂) + 2 * v.length + 1 by omega]
    exact .bytesStep wt valCap bs v rest hm hbs hb (ih h₂)

theorem polyMergeSmallStep_to_spqr {p₁ p₂ : Nat} {evs : List AllocEvent}
    (hpoly : p₁ ≤ p₂) (h : PolyMergeSmallStep p₁ evs) :
    SpqrMergeSmallStep p₂ evs := by
  cases h with
  | nil => exact .nil
  | fromErr => exact .fromErr
  | pushErr hn hp => exact .pushErr (Nat.le_trans hn (by decide : 1 ≤ 4)) hp
  | bytesMergeErr wt valCap bs hm hb => exact .bytesMergeErr wt valCap bs hm hb
  | growVecU8 g hc hg => exact .growVecU8 g (Nat.lt_of_lt_of_le hc hpoly) hg

theorem polyMergeLoopEnv_to_spqr {fuel len maxLen p₁ p₂ : Nat} {evs : List AllocEvent}
    (hlen : len ≤ maxLen) (hpoly : p₁ ≤ p₂)
    (h : PolyMergeLoopEnv fuel len p₁ evs) :
    SpqrMergeLoopEnv fuel maxLen p₂ evs := by
  induction h with
  | nil => exact .nil
  | step h1 _ ih => exact .step (polyMergeSmallStep_to_spqr hpoly h1) (ih hlen hpoly)
  | bytesStep wt valCap bs v rest hm hbs hb _ ih =>
    exact .bytesStep wt valCap bs v rest hm (Nat.le_trans hbs hlen) hb (ih hlen hpoly)

theorem FitsEnv.polyMergeLoop_head {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen polyCapBound : Nat} {E : List AllocEvent → Prop}
    (hsub : ∀ evs, E evs → PolyMergeIterEnv maxLen polyCapBound evs)
    (hFit : FitsEnv M lim st (PolyMergeLoopEnv (fuel + 1) maxLen polyCapBound)) :
    FitsEnv M lim st E :=
  fun evs he => hFit evs (PolyMergeLoopEnv.single (maxLen := maxLen) (hsub evs he))

theorem FitsEnv.polyMergeLoop_tail {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen polyCapBound : Nat} {evs₁ : List AllocEvent}
    (h1 : PolyMergeIterEnv maxLen polyCapBound evs₁)
    (hFit : FitsEnv M lim st (PolyMergeLoopEnv (fuel + 1) maxLen polyCapBound)) :
    FitsEnv M lim (M.stepEvents evs₁ st) (PolyMergeLoopEnv fuel maxLen polyCapBound) :=
  fun evs₂ h2 =>
    ((fitsEvents_append M lim evs₁ evs₂ st).mp (hFit (evs₁ ++ evs₂) (.step h1 h2))).2

theorem FitsEnv.polyMergeLoop_bytesHead {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen polyCapBound : Nat} {wt : WireType} {valCap : BitVec 64} {bs : List (BitVec 8)}
    (hbs : bs.length ≤ maxLen)
    (hfuel : max 1 (2 * bs.length) ≤ fuel)
    (hFit : FitsEnv M lim st (PolyMergeLoopEnv fuel maxLen polyCapBound)) :
    FitsEnv M lim st (BytesMerge3EnvCore wt valCap bs) := by
  intro evs hb
  cases hm : mergeBytes wt bs with
  | none =>
    have h1 : PolyMergeLoopEnv 1 maxLen polyCapBound evs :=
      PolyMergeLoopEnv.single (fuel := 0) (maxLen := maxLen)
        (.bytesMergeErr wt valCap bs hm hb)
    exact hFit evs (h1.mono_fuel (by omega))
  | some p =>
    rcases p with ⟨v, rest⟩
    have hbound := mergeBytes_len_bound hm
    have h1 : PolyMergeLoopEnv (0 + 2 * v.length + 1) maxLen polyCapBound evs :=
      PolyMergeLoopEnv.bytesSingle (fuel := 0) (maxLen := maxLen) (polyCapBound := polyCapBound)
        hm hbs hb
    exact hFit evs (h1.mono_fuel (by omega))

theorem FitsEnv.polyMergeLoop_bytesTail {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen polyCapBound : Nat} {wt : WireType} {valCap : BitVec 64}
    {bs v rest : List (BitVec 8)} {evs₁ : List AllocEvent}
    (hm : mergeBytes wt bs = some (v, rest))
    (hbs : bs.length ≤ maxLen)
    (hb : BytesMerge3EnvCore wt valCap bs evs₁)
    (hFit : FitsEnv M lim st (PolyMergeLoopEnv (fuel + 2 * v.length + 1) maxLen polyCapBound)) :
    FitsEnv M lim (M.stepEvents evs₁ st) (PolyMergeLoopEnv fuel maxLen polyCapBound) :=
  fun evs₂ h2 =>
    ((fitsEvents_append M lim evs₁ evs₂ st).mp
      (hFit (evs₁ ++ evs₂) (.bytesStep wt valCap bs v rest hm hbs hb h2))).2

theorem FitsEnv.polyMergeLoop_split {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {f₁ f₂ maxLen polyCapBound : Nat} {evs₁ : List AllocEvent}
    (h₁ : PolyMergeLoopEnv f₁ maxLen polyCapBound evs₁)
    (hFit : FitsEnv M lim st (PolyMergeLoopEnv (f₁ + f₂) maxLen polyCapBound)) :
    FitsEnv M lim (M.stepEvents evs₁ st) (PolyMergeLoopEnv f₂ maxLen polyCapBound) :=
  fun evs₂ h₂ =>
    ((fitsEvents_append M lim evs₁ evs₂ st).mp (hFit (evs₁ ++ evs₂) (h₁.append h₂))).2

theorem FitsEnv.polyMergeLoop_mono {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {f₁ f₂ maxLen₁ maxLen₂ poly₁ poly₂ : Nat}
    (hf : f₁ ≤ f₂) (hlen : maxLen₁ ≤ maxLen₂) (hpoly : poly₁ ≤ poly₂)
    (hFit : FitsEnv M lim st (PolyMergeLoopEnv f₂ maxLen₂ poly₂)) :
    FitsEnv M lim st (PolyMergeLoopEnv f₁ maxLen₁ poly₁) :=
  hFit.mono fun _ h => h.mono hf hlen hpoly

/-! ## 2. Budget-Threaded `PolynomialDecoder::merge` & `PolynomialEncoder::merge` Specifications -/

/-- Uniform `growVecU8` capacity upper bound for `PolynomialDecoder::merge`. -/
def polyDecoderCapBound (x : PolyDecoderMergeGhost) : Nat :=
  x.msg.pts.length + x.bs.length

/-- Precondition allocation envelope of `PolynomialDecoder::merge`. -/
def PolyDecoderMergeEnv (x : PolyDecoderMergeGhost) (evs : List AllocEvent) : Prop :=
  PolyMergeLoopEnv (2 * x.bs.length + 2) x.bs.length (polyDecoderCapBound x) evs

/-- Postcondition allocation envelope of `PolynomialDecoder::merge`: proportional to consumed bytes
`x.bs.length - rest.length` on `Ok`, and bounded by `2 * x.bs.length + 2` on `Err`. -/
def PolyDecoderMergePostEnv (x : PolyDecoderMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
  | some (_, rest) => PolyMergeLoopEnv (2 * (x.bs.length - rest.length)) x.bs.length (polyDecoderCapBound x) evs
  | none => PolyMergeLoopEnv (2 * x.bs.length + 2) x.bs.length (polyDecoderCapBound x) evs

theorem polyDecoderMergePostEnv_imp_pre {x : PolyDecoderMergeGhost} {evs : List AllocEvent}
    (h : PolyDecoderMergePostEnv x evs) :
    PolyDecoderMergeEnv x evs := by
  dsimp only [PolyDecoderMergePostEnv, PolyDecoderMergeEnv] at h ⊢
  split at h
  · exact h.mono_fuel (by omega)
  · exact h

/-- Envelope-parameterized budget-threaded contract of `PolynomialDecoder::merge` (`Block 296`). -/
def polyDecoderMergeSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : PolyDecoderMergeGhost → List AllocEvent → Prop) :
    Spec (PolyDecoderMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.msg.pts.length + x.bs.length < 2 ^ 56 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      protoPolynomialDecoderAt A.repAlloc x.msgPtr (polyDecoderToProto x.msg) ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp polyMergeStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp polyMergeStack ∗
      match (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          protoPolynomialDecoderAt A.repAlloc x.msgPtr (polyDecoderToProto m') ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 1⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : PolynomialDecoder, protoPolynomialDecoderAt A.repAlloc x.msgPtr (polyDecoderToProto m')) ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `PolynomialDecoder::merge` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def polyDecoderMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (PolyDecoderMergeGhost × M.σ) :=
  polyDecoderMergeSpecOfEnv A lim PolyDecoderMergeEnv PolyDecoderMergePostEnv

/-- Uniform `growVecU8` capacity upper bound for `PolynomialEncoder::merge`. -/
def polyEncoderCapBound (x : PolyEncoderMergeGhost) : Nat :=
  Nat.max x.msg.pts.length x.msg.polys.length + x.bs.length

/-- Precondition allocation envelope of `PolynomialEncoder::merge`. -/
def PolyEncoderMergeEnv (x : PolyEncoderMergeGhost) (evs : List AllocEvent) : Prop :=
  PolyMergeLoopEnv (2 * x.bs.length + 2) x.bs.length (polyEncoderCapBound x) evs

/-- Postcondition allocation envelope of `PolynomialEncoder::merge`. -/
def PolyEncoderMergePostEnv (x : PolyEncoderMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
  | some (_, rest) => PolyMergeLoopEnv (2 * (x.bs.length - rest.length)) x.bs.length (polyEncoderCapBound x) evs
  | none => PolyMergeLoopEnv (2 * x.bs.length + 2) x.bs.length (polyEncoderCapBound x) evs

theorem polyEncoderMergePostEnv_imp_pre {x : PolyEncoderMergeGhost} {evs : List AllocEvent}
    (h : PolyEncoderMergePostEnv x evs) :
    PolyEncoderMergeEnv x evs := by
  dsimp only [PolyEncoderMergePostEnv, PolyEncoderMergeEnv] at h ⊢
  split at h
  · exact h.mono_fuel (by omega)
  · exact h

/-- Envelope-parameterized budget-threaded contract of `PolynomialEncoder::merge` (`Block 297`). -/
def polyEncoderMergeSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : PolyEncoderMergeGhost → List AllocEvent → Prop) :
    Spec (PolyEncoderMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.msg.pts.length + x.bs.length < 2 ^ 56 ∧
      x.msg.polys.length + x.bs.length < 2 ^ 56 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      protoPolynomialEncoderAt A.repAlloc x.msgPtr (polyEncoderToProto x.msg) ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp polyMergeStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp polyMergeStack ∗
      match (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          protoPolynomialEncoderAt A.repAlloc x.msgPtr (polyEncoderToProto m') ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 1⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : PolynomialEncoder, protoPolynomialEncoderAt A.repAlloc x.msgPtr (polyEncoderToProto m')) ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `PolynomialEncoder::merge` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def polyEncoderMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (PolyEncoderMergeGhost × M.σ) :=
  polyEncoderMergeSpecOfEnv A lim PolyEncoderMergeEnv PolyEncoderMergePostEnv

/-! ## 2b. `FitsEnv fineCostModel` & Non-Empty Inhabitation Witnesses -/

def polyDecoderWitnessGhost : PolyDecoderMergeGhost :=
  { wt := .varint, msgPtr := 0#64, msg := default, bufRef := 0#64, slot := 0#64,
    ptr := 0#64, bs := spqrWitnessBytes }

def polyEncoderWitnessGhost : PolyEncoderMergeGhost :=
  { wt := .varint, msgPtr := 0#64, msg := default, bufRef := 0#64, slot := 0#64,
    ptr := 0#64, bs := spqrWitnessBytes }

theorem polyMergeSmallStep_inhabited :
    ∃ evs : List AllocEvent, evs ≠ [] ∧ PolyMergeSmallStep 1 evs :=
  ⟨rustAllocEvents 72 8, by decide, .fromErr⟩

theorem polyMergeIterEnv_inhabited :
    ∃ evs : List AllocEvent, evs ≠ [] ∧ PolyMergeIterEnv 4 1 evs :=
  polyMergeSmallStep_inhabited

theorem polyMergeLoopEnv_inhabited {fuel polyCapBound : Nat} (hf : 7 ≤ fuel) :
    ∃ evs : List AllocEvent, evs ≠ [] ∧ PolyMergeLoopEnv fuel 4 polyCapBound evs := by
  refine ⟨bytesMergeEventsCore .lengthDelimited 0#64 spqrWitnessBytes, by decide, ?_⟩
  have hm : mergeBytes .lengthDelimited spqrWitnessBytes = some ([1#8, 2#8, 3#8], []) := by
    decide
  have h1 : PolyMergeLoopEnv (0 + 2 * [1#8, 2#8, 3#8].length + 1) 4 polyCapBound
      (bytesMergeEventsCore .lengthDelimited 0#64 spqrWitnessBytes) :=
    PolyMergeLoopEnv.bytesSingle (fuel := 0) (maxLen := 4) (polyCapBound := polyCapBound)
      hm (by decide) rfl
  exact h1.mono_fuel (by simpa using hf)

theorem polyMergeLoopEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init (PolyMergeLoopEnv 36 4 4) :=
  spqrMergeLoopEnv_fitsEnv_witness.mono fun _ h =>
    polyMergeLoopEnv_to_spqr (Nat.le_refl 4) (Nat.le_refl 4) h

theorem polyMergeSmallStep_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init (PolyMergeSmallStep 1) :=
  polyMergeLoopEnv_fitsEnv_witness.mono fun _ h =>
    (PolyMergeLoopEnv.single (fuel := 0) (maxLen := 4) h).mono (by decide) (by decide) (by decide)

theorem polyMergeIterEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init (PolyMergeIterEnv 4 1) :=
  polyMergeSmallStep_fitsEnv_witness

theorem polyDecoderMergePostEnv_inhabited :
    ∃ evs : List AllocEvent,
      evs ≠ [] ∧ PolyDecoderMergePostEnv polyDecoderWitnessGhost evs :=
  polyMergeLoopEnv_inhabited (by decide)

theorem polyDecoderMergeEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init
      (PolyDecoderMergeEnv polyDecoderWitnessGhost) :=
  polyMergeLoopEnv_fitsEnv_witness.mono fun _ h => h.mono (by decide) (by decide) (by decide)

theorem polyDecoderMergePostEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init
      (PolyDecoderMergePostEnv polyDecoderWitnessGhost) :=
  polyDecoderMergeEnv_fitsEnv_witness.mono fun _ => polyDecoderMergePostEnv_imp_pre

theorem polyEncoderMergePostEnv_inhabited :
    ∃ evs : List AllocEvent,
      evs ≠ [] ∧ PolyEncoderMergePostEnv polyEncoderWitnessGhost evs :=
  polyMergeLoopEnv_inhabited (by decide)

theorem polyEncoderMergeEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init
      (PolyEncoderMergeEnv polyEncoderWitnessGhost) :=
  polyMergeLoopEnv_fitsEnv_witness.mono fun _ h => h.mono (by decide) (by decide) (by decide)

theorem polyEncoderMergePostEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init
      (PolyEncoderMergePostEnv polyEncoderWitnessGhost) :=
  polyEncoderMergeEnv_fitsEnv_witness.mono fun _ => polyEncoderMergePostEnv_imp_pre

/-! ## 3. Loop & Error-Exit Separation-Logic Bundles -/

/-- Budget-threaded loop-header separation-logic bundle at `+0x0a4` of `PolynomialDecoder::merge`. -/
def polyDecoderLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s0 s : State) (msgPtr bufRef slot ptr : BitVec 64)
    (m : PolynomialDecoder) (bs cur : List (BitVec 8)) : SepProp :=
  stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗
    memRegion (s0.sp - 128#64) 48 ∗ polySavedRegsAny s0.sp s0 ∗
    protoPolynomialDecoderAt A.repAlloc msgPtr (polyDecoderToProto m) ∗
    (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗ A.pool lim st s

/-- Budget-threaded error-exit separation-logic bundle at `+0x070`, `+0x07c`, `+0x380` of `PolynomialDecoder::merge`. -/
def polyDecoderErrFrame {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s0 s : State) (msgPtr bufRef slot ptr : BitVec 64)
    (m : PolynomialDecoder) (bs : List (BitVec 8)) : SepProp :=
  polySavedRegsAny s0.sp s0 ∗ protoPolynomialDecoderAt A.repAlloc msgPtr (polyDecoderToProto m) ∗
    (bufRef ↦₆₄ slot) ∗ memRegion slot 16 ∗ (ptr ↦ₛ bs) ∗ A.pool lim st s

/-- Budget-threaded loop-header separation-logic bundle at `+0x0a4` of `PolynomialEncoder::merge`. -/
def polyEncoderLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s0 s : State) (msgPtr bufRef slot ptr : BitVec 64)
    (m : PolynomialEncoder) (bs cur : List (BitVec 8)) : SepProp :=
  stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗
    memRegion (s0.sp - 128#64) 48 ∗ polySavedRegsAny s0.sp s0 ∗
    protoPolynomialEncoderAt A.repAlloc msgPtr (polyEncoderToProto m) ∗
    (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗ A.pool lim st s

/-- Budget-threaded error-exit separation-logic bundle at `+0x070`, `+0x07c`, `+0x344` of `PolynomialEncoder::merge`. -/
def polyEncoderErrFrame {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s0 s : State) (msgPtr bufRef slot ptr : BitVec 64)
    (m : PolynomialEncoder) (bs : List (BitVec 8)) : SepProp :=
  polySavedRegsAny s0.sp s0 ∗ protoPolynomialEncoderAt A.repAlloc msgPtr (polyEncoderToProto m) ∗
    (bufRef ↦₆₄ slot) ∗ memRegion slot 16 ∗ (ptr ↦ₛ bs) ∗ A.pool lim st s

/-! ## 4. Panic Predicate & Relocatable `[LibsignalPlacement]` Shared Exit/Skip Lemmas (Block `296`) -/

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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
/-- Placed shared exit from `+0x07c` (`(blkPl_296).base + 124#64`) when `x1 = err ≠ 0#64` owns
`decodeErrorAtStackLen A.repAlloc err 0`. -/
theorem polyDecoder_err0_ret_exit_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyDecoderMergeGhost → List AllocEvent → Prop}
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {err : BitVec 64}
    (hnone : (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hevs : ∃ evs, PostEnv x evs ∧ st_cur = M.stepEvents evs st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_296).base + 124#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = err) (herr : err ≠ 0#64) (hcs : PolyCalleeSaved s0 s) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err 0 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗
        memRegion (s0.sp - 160#64) 32 ∗ memRegion (s0.sp - 128#64) 48 ∗
        polyDecoderErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  rcases hevs with ⟨evs, hevs_post, rfl⟩
  apply SepWPp.of_sepWP_ret
  unfold WppPost polyDecoderMergeSpecOfEnv
  simp only [hnone, polyDecoderErrFrame, polySavedRegsAny, polySavedRegs,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx1]
  apply SepWP.exists_elim; intro v_pad
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A.repAlloc err) (by sep_focus)
  apply SepWP.fold (protoPolynomialDecoderAt_entails_exists A.repAlloc x.msgPtr m) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
  wp_done

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
/-- Code-loaded placed shared exit from `+0x070` (`(blkPl_296).base + 112#64`): calls `DecodeError::from`
on `(s0.sp - 128#64, w, st_cur)` and returns at `+0x078..+0x098`. -/
theorem polyDecoder_from_err_exit_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyDecoderMergeGhost → List AllocEvent → Prop}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {w : BitVec 64}
    (hnone : (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hw : KindNoHeap w)
    (hfits_from : FitsEnv M lim st_cur DecodeErrorFromEnv)
    (hevs_from : ∀ evs_f, DecodeErrorFromEnv evs_f →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_f st_cur = M.stepEvents evs st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_296).base + 112#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64)
    (htr : s.trace = s0.trace) (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗
        polyDecoderErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 261) hinv
  conv => arg 4; rw [polyBelow_decodeErrorHook s0.sp, polyDecoderErrFrame]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 261)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := decodeErrorFromBudgetSpec M A lim)
    (x := (s0.sp - 128#64, w, st_cur))
    (ret_pc := (blkPl_296).base + 120#64) hFromCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp], hw, hfits_from⟩ (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm _hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs]
    at hpcm hspm hx26_m hx27_m hx28_m hvregs_m
  apply SepWPp.of_sepWP_ret
  unfold WppPost polyDecoderMergeSpecOfEnv
  simp only [decodeErrorFromBudgetSpec, hnone, polySavedRegsAny, polySavedRegs,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, htr, hsp, hspm]
  apply SepWP.exists_elim; intro v_pad
  apply SepWP.exists_elim; intro evs_f
  wp_focus_pure; rintro ⟨_herr, htrm⟩
  wp_focus_pure; intro hevs_f
  obtain ⟨evs, hevs_post, hst_eq⟩ := hevs_from evs_f hevs_f
  conv => arg 4; simp only [hst_eq, arm64_norm]
  apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A.repAlloc _) (by sep_focus)
  apply SepWP.fold (protoPolynomialDecoderAt_entails_exists A.repAlloc x.msgPtr m) (by sep_focus)
  apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
  wp_done

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
/-- Code-loaded placed shared exit from `+0x380` (`(blkPl_296).base + 896#64`): calls `DecodeError::push`
on `(s0.sp - 128#64, err, 0, st_cur)` and returns at `+0x384..+0x388` + `+0x07c..+0x098`. -/
theorem polyDecoder_push_err_exit_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyDecoderMergeGhost → List AllocEvent → Prop}
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {err : BitVec 64}
    (hnone : (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64)
    (hfits_push : FitsEnv M lim st_cur
      (DecodeErrorPushMergeEnv 0))
    (hevs_push : ∀ evs_p, DecodeErrorPushMergeEnv 0 evs_p →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_p st_cur = M.stepEvents evs st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_296).base + 896#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗
        memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗
        memRegion (s0.sp - 160#64) 32 ∗
        polyDecoderErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 257) hinv
  conv => arg 4; rw [polyBelow_decodeErrorHook s0.sp, polyDecoderErrFrame]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 257)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := decodeErrorPushMergeBudgetSpec M A lim)
    (x := (s0.sp - 128#64, err, 0, st_cur))
    (ret_pc := (blkPl_296).base + 900#64) hPushCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp, hx0], by decide, hfits_push⟩ (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm _hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs]
    at hpcm hspm hx26_m hx27_m hx28_m hvregs_m
  apply SepWPp.of_sepWP_ret
  unfold WppPost polyDecoderMergeSpecOfEnv
  simp only [decodeErrorPushMergeBudgetSpec, hnone, polySavedRegsAny, polySavedRegs,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, htr, hsp, hspm]
  apply SepWP.exists_elim; intro v_pad
  apply SepWP.exists_elim; intro evs_p
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_p
  obtain ⟨evs, hevs_post, hst_eq⟩ := hevs_push evs_p hevs_p
  conv => arg 4; simp only [hst_eq, arm64_norm]
  apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  apply SepWP.fold (decodeErrorWith_one_entails_le1 A.repAlloc err) (by sep_focus)
  apply SepWP.fold (protoPolynomialDecoderAt_entails_exists A.repAlloc x.msgPtr m) (by sep_focus)
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus)
  apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
  wp_done

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
/-- Code-loaded placed step lemma for unknown field tags (`tag ∉ {1, 2, 3, 4}`) at `+0x140`
(`(blkPl_296).base + 320#64`). -/
theorem polyDecoder_skip_step_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyDecoderMergeGhost → List AllocEvent → Prop}
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
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
      (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_296).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_296).base + 320#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 263) hinv
  conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 263)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := skipField3Spec A lim)
    (x := (⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_296).base + 332#64) hSkipCall hinv
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
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 97 tag iwt rest with
  | none =>
    have hnone := hnone_of_sf hsf
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 124#64) hinvm
    (conv => arg 4; simp only [skipField3Spec, hsf, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_sf
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_sf
    wp_focus_pure; intro hsm0
    conv => arg 4; simp only [arm64_norm, hsp]
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    wp_steps_sync_pool ((blkPl_296).base + 124#64)
    simp only [State.setMem_setMem]
    wp_reach; intro _hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyDecoderErrFrame]; sep_ac_rfl))
      (polyDecoder_err0_ret_exit_placed hnone (hevs_sf_err hsf evs_sf hevs_sf) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) hsm0
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
         by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩)
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 164#64) hinvm
    (conv => arg 4; simp only [skipField3Spec, hsf, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_sf
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_sf
    wp_focus_pure; intro hsm0
    have hevs_nil : evs_sf = [] := by
      change SkipFieldEnv _ evs_sf at hevs_sf
      simpa [SkipFieldEnv, skipFieldEventsCore, hsf] using hevs_sf
    subst hevs_nil
    conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps_sync_pool ((blkPl_296).base + 164#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyDecoderLoopPre]; sep_ac_rfl))
      (hcont rest' _ hsf
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
         by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
