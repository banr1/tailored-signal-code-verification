/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainPushPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainPushPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state` (Block `325`): Budget Relocatable `ChainPB` Dispatch & Loop Body

Budget-threaded relocatable `[LibsignalPlacement]` accumulator bridges, `ChainPB` tag dispatch (`+560`),
and single loop iteration (`+520`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkLib_eq_325 blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarintAux skipField)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeGhost IsDropSuffix SkipFieldGhost sliceCursorAfter
   sliceCursorAfter_eq_split sliceCursorAfter_join suffix_trans)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_mergeBytes_toOption)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (codecWireTypeToProto mergeLoopBin protoPrefixStep_chainPB_mergeField
   protoWireTypeToCodec_codecWireTypeToProto)
open CryptoVerification.LibsignalSpqrV1
  (ChainPB ChainParamsPB PqRatchetState VersionNegotiationPB spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeBytes mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred
   chainPB_mergeField_other chainPB_mergeField_tag1 chainPB_mergeField_tag2
   chainPB_mergeField_tag4 chainPB_mergeField_tag5 chainPB_mergeField_tag6
   decodeStatePlacedEntry decodeStatePlacedProg errFrame_parts_fold
   key_and7_of_wt_none key_and7_of_wt_some key_lsr3_32_eq
   key_lsr32_eq_zero_of_lt key_lsr32_ne_zero_of_ge
   mergeLoopBin_of_decodeVarint_none mergeLoopBin_of_key_ge
   mergeLoopBin_of_key_ok mergeLoopBin_of_tag_zero mergeLoopBin_of_wt_none
   protoPqRatchetStateCapOkAt protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt
   protoPqRatchetStateCapOkAt_mono sp_sub_1392_aligned
   tag_cbz32_false tag_cbz64_false tag_cmp32_of_gt tag_lt_pow29_of_key_lt
   tag_setWidth32_ofNat tag_zeroExtend64_ofNat32 truncate32_zeroExtend64_lsr3
   wt_setWidth8 wt_ult6)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv DecodeErrorPushEnv)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (SkipField3Env skipField3EventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv decodeVarintSliceEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (BytesMergeEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (DecodeVarint2Env)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (ChainParamsMergeEnv ChainParamsMergePostEnv DecodeStateEnv DecodeStateIterEnv
   DecodeStateLoopEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStateCalleeContractsPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget (decodeStateErrFramePlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced
   decodeStatePostPlacedOfEnv decodeState_err_push_53cdc_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudget
  (decodeState_err_53b8c_placed_ofEnv decodeState_err_53b98_placed_ofEnv
   decodeState_err_53ba4_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced decodeStateLoopCommonPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlacedBudget
  (decodeState_chain_skip_537ec_placed_ofEnv decodeState_chain_tag1_537b4_placed_ofEnv
   decodeState_chain_tag2_53804_placed_ofEnv decodeState_chain_tag4_537d4_placed_ofEnv
   decodeState_chain_tag5_53824_placed_ofEnv decodeState_chain_tag6_5378c_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainPushPlacedBudget
  (decodeState_chain_tag3_536ec_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlacedBudgetAux
  (after_decodeVarint2_to_errFrame_placed bytesMerge3Det_of_contractsPlacedX
   decodeState_codecWireTypeToProto_eq err3_env err3_fits1 err3_fits2)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero truncate32_zeroExtend64_lsr3
attribute [local simp] truncate32_zeroExtend64_lsr3

/-! ## Envelope & Accumulator Helpers -/

private theorem decodeVarintAux_length_lt (i : Nat) (acc : BitVec 64)
    (bs rest0 : List (BitVec 8)) (len : BitVec 64)
    (h : decodeVarintAux i acc bs = some (len, rest0)) :
    rest0.length < bs.length := by
  induction bs generalizing i acc with
  | nil => simp [decodeVarintAux] at h
  | cons b bs' ih =>
    unfold decodeVarintAux at h
    dsimp only at h
    split at h
    · split at h
      · contradiction
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        simp
    · split at h
      · contradiction
      · have hlt := ih _ _ h
        simp; omega

private theorem mergeBytes_length_sum {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : CryptoVerification.LibsignalProtoCodec.mergeBytes wt bs = some (v, rest)) :
    1 + v.length + rest.length ≤ bs.length := by
  cases wt <;> try simp [CryptoVerification.LibsignalProtoCodec.mergeBytes] at h
  cases hvar : decodeVarint bs with
  | none => simp [hvar] at h
  | some p =>
    rcases p with ⟨len, rest0⟩
    rw [hvar] at h
    dsimp only at h
    split at h
    · contradiction
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h1 : rest0.length < bs.length := decodeVarintAux_length_lt 0 0 bs rest0 len hvar
      have h2 : (rest0.take len.toNat).length + (rest0.drop len.toNat).length = rest0.length := by
        rw [← List.length_append, List.take_append_drop]
      omega

private theorem proto_mergeBytes_length_sum {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : (mergeBytes (codecWireTypeToProto wt) bs).toOption = some (v, rest)) :
    1 + v.length + rest.length ≤ bs.length := by
  have heq : CryptoVerification.LibsignalProtoCodec.mergeBytes wt bs =
      (mergeBytes (codecWireTypeToProto wt) bs).toOption := by
    have h0 := proto_mergeBytes_toOption (codecWireTypeToProto wt) bs
    rw [protoWireTypeToCodec_codecWireTypeToProto] at h0
    exact h0.symm
  exact mergeBytes_length_sum (heq.trans h)

theorem decodeVarint2Env_eq_nil_of_some {bs rest : List (BitVec 8)} {v : BitVec 64}
    {evs : List AllocEvent}
    (hdv : decodeVarint bs = some (v, rest)) (hevs : DecodeVarint2Env bs evs) :
    evs = [] := by
  simp only [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hdv] at hevs
  exact hevs

private theorem skipField3Env_eq_nil_of_some {x : SkipFieldGhost} {rest : List (BitVec 8)}
    {evs : List AllocEvent}
    (hsf : skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs = some rest)
    (hevs : SkipField3Env x evs) :
    evs = [] := by
  simp only [SkipField3Env, skipField3EventsCore, hsf] at hevs
  exact hevs

theorem decodeErrorFromEnv_iter {maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (h : DecodeErrorFromEnv evs) :
    DecodeStateIterEnv maxLen polyCapBound evs := by
  rw [h]
  exact .of_decodeErrorFrom

private theorem err4_fits1 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen polyCapBound : Nat} {E1 : List AllocEvent → Prop}
    (hf : 4 ≤ fuel)
    (h1 : ∀ evs, E1 evs → DecodeStateIterEnv maxLen polyCapBound evs)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv fuel maxLen polyCapBound)) :
    FitsEnv M lim st E1 :=
  SpecsBudget.FitsEnv.decodeStateLoop_head (fuel := 3) h1
    (SpecsBudget.FitsEnv.decodeStateLoop_mono (f₁ := 4) hf (Nat.le_refl _) (Nat.le_refl _) hFit)

private theorem err4_fits2 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen polyCapBound : Nat} {E1 : List AllocEvent → Prop} {evs1 : List AllocEvent}
    (hf : 4 ≤ fuel)
    (h1 : ∀ evs, E1 evs → DecodeStateIterEnv maxLen polyCapBound evs)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv fuel maxLen polyCapBound))
    (he1 : E1 evs1) :
    FitsEnv M lim (M.stepEvents evs1 st) (DecodeErrorPushEnv 0) :=
  SpecsBudget.FitsEnv.decodeStateLoop_head (fuel := 2)
    (fun _ hp => .of_decodeErrorPush (by decide) hp)
    (SpecsBudget.FitsEnv.decodeStateLoop_tail (fuel := 3) (h1 evs1 he1)
      (SpecsBudget.FitsEnv.decodeStateLoop_mono (f₁ := 4) hf (Nat.le_refl _) (Nat.le_refl _) hFit))

private theorem err4_fits3 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen polyCapBound : Nat} {E1 : List AllocEvent → Prop}
    {evs1 evs_p1 : List AllocEvent}
    (hf : 4 ≤ fuel)
    (h1 : ∀ evs, E1 evs → DecodeStateIterEnv maxLen polyCapBound evs)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv fuel maxLen polyCapBound))
    (he1 : E1 evs1) (hp1 : DecodeErrorPushEnv 0 evs_p1) :
    FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs1 st)) (DecodeErrorPushEnv 1) :=
  SpecsBudget.FitsEnv.decodeStateLoop_head (fuel := 1)
    (fun _ hp2 => .of_decodeErrorPush (by decide) hp2)
    (SpecsBudget.FitsEnv.decodeStateLoop_tail (fuel := 2) (.of_decodeErrorPush (by decide) hp1)
      (SpecsBudget.FitsEnv.decodeStateLoop_tail (fuel := 3) (h1 evs1 he1)
        (SpecsBudget.FitsEnv.decodeStateLoop_mono (f₁ := 4) hf (Nat.le_refl _) (Nat.le_refl _)
          hFit)))

private theorem err4_env {M : AllocCostModel} {PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {x : DecodeStateGhost} {st0 st : M.σ} {fuel maxLen polyCapBound : Nat}
    {E1 : List AllocEvent → Prop} {evs1 evs_p1 evs_p2 evs_f : List AllocEvent}
    (hf : 4 ≤ fuel)
    (h1 : ∀ evs, E1 evs → DecodeStateIterEnv maxLen polyCapBound evs)
    (henv : ∀ evs_err, DecodeStateLoopEnv fuel maxLen polyCapBound evs_err →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = M.stepEvents evs_err st)
    (he1 : E1 evs1) (hp1 : DecodeErrorPushEnv 0 evs_p1)
    (hp2 : DecodeErrorPushEnv 1 evs_p2) (hfree : FreeOnlyEvs evs_f) :
    ∃ evs, PostEnv x evs ∧
      M.stepEvents evs st0 =
        M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs1 st))) := by
  have hloop4 : DecodeStateLoopEnv 4 maxLen polyCapBound (evs1 ++ (evs_p1 ++ (evs_p2 ++ evs_f))) :=
    DecodeStateLoopEnv.step (h1 evs1 he1)
      (DecodeStateLoopEnv.step (.of_decodeErrorPush (by decide) hp1)
        (DecodeStateLoopEnv.step (.of_decodeErrorPush (by decide) hp2)
          (DecodeStateLoopEnv.single (.of_freeOnly hfree))))
  obtain ⟨evs, hpost, hstep⟩ := henv _ (hloop4.mono_fuel hf)
  exact ⟨evs, hpost,
    by rw [hstep, M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]⟩

theorem acc_henv_err {M : AllocCostModel}
    {PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {x : DecodeStateGhost} {st0 st : M.σ} {evs_acc : List AllocEvent} {f k : Nat}
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hf : f + k ≤ 16 * x.st.bytes.length + 32)
    (hpost_env : ∀ evs, DecodeStateEnv x evs → PostEnv x evs) :
    ∀ evs_err,
      DecodeStateLoopEnv k x.st.bytes.length (2 * x.st.bytes.length + 16) evs_err →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = M.stepEvents evs_err st := by
  intro evs_err herr
  refine ⟨evs_acc ++ evs_err, hpost_env _ ((hacc.append herr).mono_fuel hf), ?_⟩
  rw [M.stepEvents_append, hst]

private theorem acc_fits_split {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {rem d maxLen polyCapBound : Nat} {evs_step : List AllocEvent}
    (hd : d ≤ rem)
    (hstep : DecodeStateLoopEnv d maxLen polyCapBound evs_step)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv rem maxLen polyCapBound)) :
    FitsEnv M lim (M.stepEvents evs_step st)
      (DecodeStateLoopEnv (rem - d) maxLen polyCapBound) :=
  SpecsBudget.FitsEnv.decodeStateLoop_split hstep
    (SpecsBudget.FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hFit)

/-! ## `ChainPB` Tag Dispatch (`+560`) -/

/-- Envelope-parameterized tag dispatch for `ChainPB::merge` at `+560` given `1 ≤ tag < 2 ^ 29`
(placed). -/
theorem decodeState_chain_dispatch_536cc_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit tag : Nat) (iwt : WireType)
    (htag1_le : 1 ≤ tag) (htag29 : tag < 2 ^ 29)
    (hrest1_le : rest1.length ≤ x.st.bytes.length) (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hlinks : ch.links.length + rest1.length ≤ 2 * x.st.bytes.length + 4)
    (herr_of_none :
      (match (ChainPB.mergeField ch (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt)
          rest1 99).toOption with
       | none => none
       | some (ch', rest2) =>
         mergeLoopBin ChainPB.mergeField (rest2.length - limit) ch' rest2 limit 99) = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 * rest1.length + 11 ≤ rem)
    (hf : f + 4 * rest1.length + 11 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hpost_env : ∀ evs, DecodeStateEnv x evs → PostEnv x evs)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 560#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨optVn, some ch, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hnext : ∀ (w0' : BitVec 64) (ch' : ChainPB) (rest2 : List (BitVec 8))
        (evs_step : List AllocEvent) (sf : State) (P' : SepProp),
      rest2.length ≤ rest1.length → IsDropSuffix rest1 rest2 →
      ch'.links.length + rest2.length ≤ ch.links.length + rest1.length →
      DecodeStateLoopEnv (f + (4 * (rest1.length - rest2.length) + 1)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_step) →
      M.stepEvents (evs_acc ++ evs_step) st0 = M.stepEvents evs_step st →
      FitsEnv M lim (M.stepEvents evs_step st)
        (DecodeStateLoopEnv (rem - (4 * (rest1.length - rest2.length) + 1)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      (ChainPB.mergeField ch (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 99).toOption =
        some (ch', rest2) →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, some ch', inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_step st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hfits11 : FitsEnv M lim st
      (DecodeStateLoopEnv (4 * rest1.length + 11) x.st.bytes.length
        (2 * x.st.bytes.length + 16)) :=
    SpecsBudget.FitsEnv.decodeStateLoop_mono hrem (Nat.le_refl _) (Nat.le_refl _) hFit
  have henv_err11 : ∀ evs_err,
      DecodeStateLoopEnv (4 * rest1.length + 11) x.st.bytes.length
        (2 * x.st.bytes.length + 16) evs_err →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = M.stepEvents evs_err st :=
    acc_henv_err hacc hst (by omega) hpost_env
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  have hwt8 := wt_setWidth8 iwt
  by_cases htag1 : tag = 1
  · subst htag1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 792#64)
    wp_steps 4
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    refine decodeState_chain_tag1_537b4_placed_ofEnv
      (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := 8#64)
      hc.toDecodeStateCalleeContractsPlaced x st0 st w0 optVn ch inner rest1 limit iwt
      hrest1_le hrest1_suf hlen_bound
      (fun hne => herr_of_none (by
        rw [← decodeState_codecWireTypeToProto_eq, show BitVec.ofNat 32 1 = 1#32 from rfl,
          chainPB_mergeField_tag1]
        simp only [hne, ↓reduceIte]))
      (fun hwt_eq hnone => herr_of_none (by
        rw [← decodeState_codecWireTypeToProto_eq, show BitVec.ofNat 32 1 = 1#32 from rfl,
          chainPB_mergeField_tag1]
        simp only [hwt_eq, ↓reduceIte, hnone]; rfl))
      s0 _ _ R post hpost
      (fun _ => err4_fits1 (by omega) (fun _ => .of_decodeVarint2) hfits11)
      (fun evs_dv _ _ hevs_dv =>
        err4_fits2 (by omega) (fun _ => .of_decodeVarint2) hfits11 hevs_dv)
      (fun evs_dv evs_p1 _ _ hevs_dv hp1 =>
        err4_fits3 (by omega) (fun _ => .of_decodeVarint2) hfits11 hevs_dv hp1)
      (fun evs_dv evs_p1 evs_p2 evs_f _ _ hevs_dv hp1 hp2 hfree =>
        err4_env (by omega) (fun _ => .of_decodeVarint2) henv_err11 hevs_dv hp1 hp2 hfree)
      (fun _ => err4_fits1 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits11)
      (fun _ evs_fr hfr =>
        err4_fits2 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits11 hfr)
      (fun _ evs_fr evs_p1 hfr hp1 =>
        err4_fits3 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits11 hfr hp1)
      (fun _ evs_fr evs_p1 evs_p2 evs_f hfr hp1 hp2 hfree =>
        err4_env (by omega) (fun _ => decodeErrorFromEnv_iter) henv_err11 hfr hp1 hp2 hfree)
      hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, Reg.x0, hx0])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
      (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
      (by simp only [arm64_norm, hx29])
      (by dsimp only [decodeStateLoopCommonPlaced]; simp only [wp_norm, arm64_norm]; try sep_ac_rfl)
      ?_
    intro v rest2 evs_dv sf P' hwt_eq hdv2 hevs_dv hle2 hsuf2 hpc'
    have hevs_nil := decodeVarint2Env_eq_nil_of_some hdv2 hevs_dv
    subst hevs_nil
    have hstep_env : DecodeStateLoopEnv (4 * (rest1.length - rest2.length) + 1)
        x.st.bytes.length (2 * x.st.bytes.length + 16) [] := .nil
    exact hnext w0 { ch with direction := v.truncate 32 } rest2 [] sf P' hle2 hsuf2
      (by dsimp only; omega)
      (hacc.append hstep_env)
      (by rw [M.stepEvents_append, hst])
      (acc_fits_split (by omega) hstep_env hFit)
      (by rw [← decodeState_codecWireTypeToProto_eq, show BitVec.ofNat 32 1 = 1#32 from rfl,
            chainPB_mergeField_tag1]
          simp only [hwt_eq, ↓reduceIte, hdv2]; rfl)
      hpc'
  · by_cases htag2 : tag = 2
    · subst htag2
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 872#64)
      wp_steps 6
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      refine decodeState_chain_tag2_53804_placed_ofEnv
        (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := 8#64)
        hc.toDecodeStateCalleeContractsPlaced x st0 st w0 optVn ch inner rest1 limit iwt
        hrest1_le hrest1_suf hlen_bound
        (fun hne => herr_of_none (by
          rw [← decodeState_codecWireTypeToProto_eq, show BitVec.ofNat 32 2 = 2#32 from rfl,
            chainPB_mergeField_tag2]
          simp only [hne, ↓reduceIte]))
        (fun hwt_eq hnone => herr_of_none (by
          rw [← decodeState_codecWireTypeToProto_eq, show BitVec.ofNat 32 2 = 2#32 from rfl,
            chainPB_mergeField_tag2]
          simp only [hwt_eq, ↓reduceIte, hnone]; rfl))
        s0 _ _ R post hpost
        (fun _ => err4_fits1 (by omega) (fun _ => .of_decodeVarint2) hfits11)
        (fun evs_dv _ _ hevs_dv =>
          err4_fits2 (by omega) (fun _ => .of_decodeVarint2) hfits11 hevs_dv)
        (fun evs_dv evs_p1 _ _ hevs_dv hp1 =>
          err4_fits3 (by omega) (fun _ => .of_decodeVarint2) hfits11 hevs_dv hp1)
        (fun evs_dv evs_p1 evs_p2 evs_f _ _ hevs_dv hp1 hp2 hfree =>
          err4_env (by omega) (fun _ => .of_decodeVarint2) henv_err11 hevs_dv hp1 hp2 hfree)
        (fun _ => err4_fits1 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits11)
        (fun _ evs_fr hfr =>
          err4_fits2 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits11 hfr)
        (fun _ evs_fr evs_p1 hfr hp1 =>
          err4_fits3 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits11 hfr hp1)
        (fun _ evs_fr evs_p1 evs_p2 evs_f hfr hp1 hp2 hfree =>
          err4_env (by omega) (fun _ => decodeErrorFromEnv_iter) henv_err11 hfr hp1 hp2 hfree)
        hs0A
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
        (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, Reg.x0, hx0])
        (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
        (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
        (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
        (by simp only [arm64_norm, hx29])
        (by dsimp only [decodeStateLoopCommonPlaced]; simp only [wp_norm, arm64_norm]; try sep_ac_rfl)
        ?_
      intro v rest2 evs_dv sf P' hwt_eq hdv2 hevs_dv hle2 hsuf2 hpc'
      have hevs_nil := decodeVarint2Env_eq_nil_of_some hdv2 hevs_dv
      subst hevs_nil
      have hstep_env : DecodeStateLoopEnv (4 * (rest1.length - rest2.length) + 1)
          x.st.bytes.length (2 * x.st.bytes.length + 16) [] := .nil
      exact hnext w0 { ch with currentEpoch := v } rest2 [] sf P' hle2 hsuf2
        (by dsimp only; omega)
        (hacc.append hstep_env)
        (by rw [M.stepEvents_append, hst])
        (acc_fits_split (by omega) hstep_env hFit)
        (by rw [← decodeState_codecWireTypeToProto_eq, show BitVec.ofNat 32 2 = 2#32 from rfl,
              chainPB_mergeField_tag2]
            simp only [hwt_eq, ↓reduceIte, hdv2]; rfl)
        hpc'
    · by_cases htag3 : tag = 3
      · subst htag3
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 592#64)
        wp_steps 8
        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        refine decodeState_chain_tag3_536ec_placed_ofEnv
          (PreEnv := PreEnv) (PostEnv := PostEnv)
          hc x st0 st evs_acc f rem w0 optVn ch inner iwt rest1 limit
          hrest1_le hrest1_suf hlen_bound (by omega)
          (fun hnone => herr_of_none (by
            rw [decodeState_codecWireTypeToProto_eq] at hnone
            rw [show BitVec.ofNat 32 3 = 3#32 from rfl, hnone]))
          hacc hst hFit (by omega) (by omega)
          s0 _ _ R post hpost hpost_env hs0A
          (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
          (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
          (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, Reg.x0, hx0])
          (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
          (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
          (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
          (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
          (by simp only [arm64_norm, hx28]) (by simp only [arm64_norm, hx29])
          (by dsimp only [decodeStateLoopCommonPlaced]; simp only [wp_norm, arm64_norm]; try sep_ac_rfl)
          ?_
        intro w0' ch' rest2 evs_tag3 sf P' hok_tag3 hlinks_eq hlt2 hle2 hsuf2
          hacc_tag3 hst_tag3 hFit_tag3 hpc'
        rw [decodeState_codecWireTypeToProto_eq] at hok_tag3
        exact hnext w0' ch' rest2 evs_tag3 sf P' hle2 hsuf2
          (by omega)
          (hacc_tag3.mono_fuel (by omega))
          hst_tag3 hFit_tag3
          (by rw [show BitVec.ofNat 32 3 = 3#32 from rfl]; exact hok_tag3)
          hpc'
      · by_cases htag4 : tag = 4
        · subst htag4
          have hbm_iter : ∀ (valCap valBuf : BitVec 64) evs,
              BytesMergeEnv ⟨iwt, s0.sp - 968#64, valCap, valBuf, ch.nextRoot,
                s0.sp - 336#64, s0.sp - 1056#64,
                x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs →
              DecodeStateIterEnv x.st.bytes.length (2 * x.st.bytes.length + 16) evs :=
            fun valCap valBuf _ h =>
              DecodeStateIterEnv.of_bytesMergeEnv hrest1_le (by omega)
                (fun v r hmb => by
                  dsimp only at hmb
                  have := mergeBytes_length_sum hmb
                  omega)
                h
          apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 824#64)
          wp_steps 4
          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          refine decodeState_chain_tag4_537d4_placed_ofEnv
            (BmPreEnv := BytesMergeEnv) (BmPostEnv := BytesMergeEnv)
            (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := 8#64)
            hc.toDecodeStateCalleeContractsPlaced (bytesMerge3Det_of_contractsPlacedX hc)
            x st0 st w0 optVn ch inner rest1 limit iwt
            hrest1_le hrest1_suf hlen_bound
            (fun hnone => herr_of_none (by
              rw [← decodeState_codecWireTypeToProto_eq, show BitVec.ofNat 32 4 = 4#32 from rfl,
                chainPB_mergeField_tag4, decodeState_codecWireTypeToProto_eq, hnone]
              rfl))
            s0 _ _ R post hpost
            (fun valCap valBuf _ => err4_fits1 (by omega) (hbm_iter valCap valBuf) hfits11)
            (fun valCap valBuf evs_bm _ _ hevs_bm =>
              err4_fits2 (by omega) (hbm_iter valCap valBuf) hfits11 hevs_bm)
            (fun valCap valBuf evs_bm evs_p1 _ _ hevs_bm hp1 =>
              err4_fits3 (by omega) (hbm_iter valCap valBuf) hfits11 hevs_bm hp1)
            (fun valCap valBuf evs_bm evs_p1 evs_p2 evs_f _ _ hevs_bm hp1 hp2 hfree =>
              err4_env (by omega) (hbm_iter valCap valBuf) henv_err11 hevs_bm hp1 hp2 hfree)
            hs0A
            (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
            (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
            (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, Reg.x0, hx0, hwt8])
            (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
            (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
            (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
            (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
            (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
            (by simp only [arm64_norm, hx29])
            (by dsimp only [decodeStateLoopCommonPlaced]; simp only [wp_norm, arm64_norm]; try sep_ac_rfl)
            ?_
          intro bs' rest2 valCap valBuf evs_bm sf P' hmb _ hevs_bm hle2 hsuf2 hpc'
          have hsum := proto_mergeBytes_length_sum hmb
          have hstep_env :
              DecodeStateLoopEnv (4 * (rest1.length - rest2.length) + 1) x.st.bytes.length
                (2 * x.st.bytes.length + 16) evs_bm :=
            (DecodeStateLoopEnv.single (fuel := 0)
              (hbm_iter valCap valBuf evs_bm hevs_bm)).mono_fuel (by omega)
          exact hnext w0 { ch with nextRoot := bs' } rest2 evs_bm sf P' hle2 hsuf2
            (by dsimp only; omega)
            (hacc.append hstep_env)
            (by rw [M.stepEvents_append, hst])
            (acc_fits_split (by omega) hstep_env hFit)
            (by rw [← decodeState_codecWireTypeToProto_eq, show BitVec.ofNat 32 4 = 4#32 from rfl,
                  chainPB_mergeField_tag4, decodeState_codecWireTypeToProto_eq, hmb]
                rfl)
            hpc'
        · by_cases htag5 : tag = 5
          · subst htag5
            apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 904#64)
            wp_steps 6
            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            refine decodeState_chain_tag5_53824_placed_ofEnv
              (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := 8#64)
              hc.toDecodeStateCalleeContractsPlaced x st0 st w0 optVn ch inner rest1 limit iwt
              hrest1_le hrest1_suf hlen_bound
              (fun hne => herr_of_none (by
                rw [← decodeState_codecWireTypeToProto_eq, show BitVec.ofNat 32 5 = 5#32 from rfl,
                  chainPB_mergeField_tag5]
                simp only [hne, ↓reduceIte]))
              (fun hwt_eq hnone => herr_of_none (by
                rw [← decodeState_codecWireTypeToProto_eq, show BitVec.ofNat 32 5 = 5#32 from rfl,
                  chainPB_mergeField_tag5]
                simp only [hwt_eq, ↓reduceIte, hnone]; rfl))
              s0 _ _ R post hpost
              (fun _ => err4_fits1 (by omega) (fun _ => .of_decodeVarint2) hfits11)
              (fun evs_dv _ _ hevs_dv =>
                err4_fits2 (by omega) (fun _ => .of_decodeVarint2) hfits11 hevs_dv)
              (fun evs_dv evs_p1 _ _ hevs_dv hp1 =>
                err4_fits3 (by omega) (fun _ => .of_decodeVarint2) hfits11 hevs_dv hp1)
              (fun evs_dv evs_p1 evs_p2 evs_f _ _ hevs_dv hp1 hp2 hfree =>
                err4_env (by omega) (fun _ => .of_decodeVarint2) henv_err11 hevs_dv hp1 hp2 hfree)
              (fun _ => err4_fits1 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits11)
              (fun _ evs_fr hfr =>
                err4_fits2 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits11 hfr)
              (fun _ evs_fr evs_p1 hfr hp1 =>
                err4_fits3 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits11 hfr hp1)
              (fun _ evs_fr evs_p1 evs_p2 evs_f hfr hp1 hp2 hfree =>
                err4_env (by omega) (fun _ => decodeErrorFromEnv_iter) henv_err11 hfr hp1 hp2 hfree)
              hs0A
              (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
              (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
              (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, Reg.x0, hx0])
              (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
              (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
              (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
              (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
              (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
              (by simp only [arm64_norm, hx29])
              (by dsimp only [decodeStateLoopCommonPlaced]; simp only [wp_norm, arm64_norm]; try sep_ac_rfl)
              ?_
            intro v rest2 evs_dv sf P' hwt_eq hdv2 hevs_dv hle2 hsuf2 hpc'
            have hevs_nil := decodeVarint2Env_eq_nil_of_some hdv2 hevs_dv
            subst hevs_nil
            have hstep_env : DecodeStateLoopEnv (4 * (rest1.length - rest2.length) + 1)
                x.st.bytes.length (2 * x.st.bytes.length + 16) [] := .nil
            exact hnext w0 { ch with sendEpoch := v } rest2 [] sf P' hle2 hsuf2
              (by dsimp only; omega)
              (hacc.append hstep_env)
              (by rw [M.stepEvents_append, hst])
              (acc_fits_split (by omega) hstep_env hFit)
              (by rw [← decodeState_codecWireTypeToProto_eq, show BitVec.ofNat 32 5 = 5#32 from rfl,
                    chainPB_mergeField_tag5]
                  simp only [hwt_eq, ↓reduceIte, hdv2]; rfl)
              hpc'
          · by_cases htag6 : tag = 6
            · subst htag6
              have hfits_cp :
                  FitsEnv M lim st
                    (ChainParamsMergeEnv ⟨iwt, s0.sp - 924#64, ch.params.getD default,
                      s0.sp - 336#64, s0.sp - 1056#64,
                      x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩) :=
                SpecsBudget.FitsEnv.decodeStateLoop_mono (by dsimp only; omega) hrest1_le
                  (Nat.zero_le _) hfits11
              have hcp_none_tail : ∀ evs_cp,
                  (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt)
                    (ch.params.getD default) rest1 99).toOption = none →
                  ChainParamsMergePostEnv ⟨iwt, s0.sp - 924#64, ch.params.getD default,
                    s0.sp - 336#64, s0.sp - 1056#64,
                    x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_cp →
                  DecodeStateLoopEnv (4 * rest1.length + 8) x.st.bytes.length
                    (2 * x.st.bytes.length + 16) evs_cp := by
                intro evs_cp hnone hcp
                dsimp only [ChainParamsMergePostEnv] at hcp
                rw [hnone] at hcp
                exact hcp.mono (Nat.le_refl _) hrest1_le (Nat.zero_le _)
              apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 752#64)
              wp_steps 8
              apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
              refine decodeState_chain_tag6_5378c_placed_ofEnv
                (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := 8#64)
                hc.toDecodeStateCalleeContractsPlaced x st0 st w0 optVn ch inner rest1 limit iwt
                hrest1_le hrest1_suf hlen_bound
                (fun hnone => herr_of_none (by
                  rw [← decodeState_codecWireTypeToProto_eq, show BitVec.ofNat 32 6 = 6#32 from rfl,
                    chainPB_mergeField_tag6, decodeState_codecWireTypeToProto_eq, hnone]
                  rfl))
                s0 _ _ R post hpost
                hfits_cp
                (fun n evs_cp hnone hn hcp => by
                  have htail3 : FitsEnv M lim (M.stepEvents evs_cp st)
                      (DecodeStateLoopEnv 3 x.st.bytes.length (2 * x.st.bytes.length + 16)) :=
                    SpecsBudget.FitsEnv.decodeStateLoop_split (f₁ := 4 * rest1.length + 8) (f₂ := 3)
                      (hcp_none_tail evs_cp hnone hcp) hfits11
                  exact SpecsBudget.FitsEnv.decodeStateLoop_head (fuel := 2)
                    (fun _ hp1 => .of_decodeErrorPush (by omega) hp1) htail3)
                (fun n evs_cp evs_p1 hnone hn hcp hp1 => by
                  have htail3 : FitsEnv M lim (M.stepEvents evs_cp st)
                      (DecodeStateLoopEnv 3 x.st.bytes.length (2 * x.st.bytes.length + 16)) :=
                    SpecsBudget.FitsEnv.decodeStateLoop_split (f₁ := 4 * rest1.length + 8) (f₂ := 3)
                      (hcp_none_tail evs_cp hnone hcp) hfits11
                  exact SpecsBudget.FitsEnv.decodeStateLoop_head (fuel := 1)
                    (fun _ hp2 => .of_decodeErrorPush (by omega) hp2)
                    (SpecsBudget.FitsEnv.decodeStateLoop_tail (fuel := 2)
                      (.of_decodeErrorPush (by omega) hp1) htail3))
                (fun n evs_cp evs_p1 evs_p2 evs_f hnone hn hcp hp1 hp2 hfree => by
                  have hcp_loop := hcp_none_tail evs_cp hnone hcp
                  have h3 : DecodeStateLoopEnv 3 x.st.bytes.length (2 * x.st.bytes.length + 16)
                      (evs_p1 ++ (evs_p2 ++ evs_f)) :=
                    DecodeStateLoopEnv.step (.of_decodeErrorPush (by omega) hp1)
                      (DecodeStateLoopEnv.step (.of_decodeErrorPush (by omega) hp2)
                        (DecodeStateLoopEnv.single (.of_freeOnly hfree)))
                  obtain ⟨evs, hpost_evs, hstep⟩ := henv_err11 _ (hcp_loop.append h3)
                  exact ⟨evs, hpost_evs,
                    by rw [hstep, M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]⟩)
                hs0A
                (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
                (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
                (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, Reg.x0, hx0, hwt8])
                (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
                (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
                (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
                (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
                (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
                (by simp only [arm64_norm, hx29])
                (by dsimp only [decodeStateLoopCommonPlaced]; simp only [wp_norm, arm64_norm]; try sep_ac_rfl)
                ?_
              intro cp' rest2 evs_cp sf P' hcp hcp_env hle2 hsuf2 hpc'
              have hstep_env :
                  DecodeStateLoopEnv (4 * (rest1.length - rest2.length) + 1) x.st.bytes.length
                    (2 * x.st.bytes.length + 16) evs_cp := by
                dsimp only [ChainParamsMergePostEnv] at hcp_env
                rw [hcp] at hcp_env
                exact hcp_env.mono (by omega) hrest1_le (Nat.zero_le _)
              exact hnext w0 { ch with params := some cp' } rest2 evs_cp sf P' hle2 hsuf2
                (by dsimp only; omega)
                (hacc.append hstep_env)
                (by rw [M.stepEvents_append, hst])
                (acc_fits_split (by omega) hstep_env hFit)
                (by rw [← decodeState_codecWireTypeToProto_eq, show BitVec.ofNat 32 6 = 6#32 from rfl,
                      chainPB_mergeField_tag6, decodeState_codecWireTypeToProto_eq, hcp]
                    rfl)
                hpc'
            · have ⟨hgt3, hsle3, _, _, _, _⟩ := tag_cmp32_of_gt (c := 3) (by omega) htag29
              have ⟨_, _, _, _, hbeq4, hbne4⟩ := tag_cmp32_of_gt (c := 4) (by omega) htag29
              have ⟨_, _, _, _, hbeq5, hbne5⟩ := tag_cmp32_of_gt (c := 5) (by omega) htag29
              have ⟨_, _, _, _, hbeq6, hbne6⟩ := tag_cmp32_of_gt (c := 6) (by omega) htag29
              have htw32 := tag_setWidth32_ofNat tag
              apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 848#64)
              wp_steps 8
              apply SepWP.done
                (by simp only [arm64_norm, Reg.x1, hx1, htw32, hgt3, hsle3, hbeq4, hbne4, hbeq5,
                      hbne5, hbeq6, hbne6])
                (by simp only [arm64_norm, hrun])
              refine decodeState_chain_skip_537ec_placed_ofEnv
                (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := 8#64)
                hc.toDecodeStateCalleeContractsPlaced x st0 st w0 optVn ch inner rest1 limit tag iwt
                ⟨by omega, by omega⟩ hrest1_le hrest1_suf hlen_bound
                (fun hnone => herr_of_none (by
                  rw [← decodeState_codecWireTypeToProto_eq,
                    chainPB_mergeField_other ch tag htag1 htag2 htag3 htag4 htag5 htag6
                      (by omega) iwt rest1 99, hnone]
                  rfl))
                s0 _ _ R post hpost
                (err3_fits1 (by omega) (fun _ => .of_skipField3) hfits11)
                (fun evs_sf _ hevs_sf =>
                  err3_fits2 (by omega) (fun _ => .of_skipField3) hfits11 evs_sf hevs_sf)
                (fun evs_sf evs_p evs_f _ hevs_sf hp hfree =>
                  err3_env (by omega) (fun _ => .of_skipField3) henv_err11 evs_sf evs_p evs_f
                    hevs_sf hp hfree)
                hs0A
                (by dsimp only [decodeStatePlacedEntry]
                    simp only [arm64_norm, Reg.x1, hx1, htw32, hgt3, hsle3, hbeq4, hbne4, hbeq5,
                      hbne5, hbeq6, hbne6])
                (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
                (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, Reg.x0, hx0, hwt8])
                (by simp only [arm64_norm, Reg.x1, hx1, htw32])
                (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
                (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
                (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
                (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
                (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
                (by simp only [arm64_norm, hx29])
                (by dsimp only [decodeStateLoopCommonPlaced]; simp only [wp_norm, arm64_norm]; try sep_ac_rfl)
                ?_
              intro rest2 evs_sf sf P' hsf hevs_sf hle2 hsuf2 hpc'
              have hevs_nil := skipField3Env_eq_nil_of_some hsf hevs_sf
              subst hevs_nil
              have hstep_env : DecodeStateLoopEnv (4 * (rest1.length - rest2.length) + 1)
                  x.st.bytes.length (2 * x.st.bytes.length + 16) [] := .nil
              exact hnext w0 ch rest2 [] sf P' hle2 hsuf2
                (by omega)
                (hacc.append hstep_env)
                (by rw [M.stepEvents_append, hst])
                (acc_fits_split (by omega) hstep_env hFit)
                (by rw [← decodeState_codecWireTypeToProto_eq,
                      chainPB_mergeField_other ch tag htag1 htag2 htag3 htag4 htag5 htag6
                        (by omega) iwt rest1 99, hsf]
                    rfl)
                hpc'

theorem decodeState_chain_dispatch_536cc_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit tag : Nat) (iwt : WireType)
    (htag1_le : 1 ≤ tag) (htag29 : tag < 2 ^ 29)
    (hrest1_le : rest1.length ≤ x.st.bytes.length) (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hlinks : ch.links.length + rest1.length ≤ 2 * x.st.bytes.length + 4)
    (herr_of_none :
      (match (ChainPB.mergeField ch (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt)
          rest1 99).toOption with
       | none => none
       | some (ch', rest2) =>
         mergeLoopBin ChainPB.mergeField (rest2.length - limit) ch' rest2 limit 99) = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 * rest1.length + 11 ≤ rem)
    (hf : f + 4 * rest1.length + 11 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 560#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨optVn, some ch, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hnext : ∀ (w0' : BitVec 64) (ch' : ChainPB) (rest2 : List (BitVec 8))
        (evs_step : List AllocEvent) (sf : State) (P' : SepProp),
      rest2.length ≤ rest1.length → IsDropSuffix rest1 rest2 →
      ch'.links.length + rest2.length ≤ ch.links.length + rest1.length →
      DecodeStateLoopEnv (f + (4 * (rest1.length - rest2.length) + 1)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_step) →
      M.stepEvents (evs_acc ++ evs_step) st0 = M.stepEvents evs_step st →
      FitsEnv M lim (M.stepEvents evs_step st)
        (DecodeStateLoopEnv (rem - (4 * (rest1.length - rest2.length) + 1)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      (ChainPB.mergeField ch (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest1 99).toOption =
        some (ch', rest2) →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, some ch', inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_step st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_chain_dispatch_536cc_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st evs_acc f rem w0 optVn ch inner rest1 limit tag iwt
    htag1_le htag29 hrest1_le hrest1_suf hlen_bound hlinks herr_of_none
    hacc hst hFit hrem hf s0 s P R post hpost (fun _ h => h) hs0A
    hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hnext

/-! ## Single Loop Iteration of `ChainPB::merge` (`+520`) -/

/-- Envelope-parameterized one field-key decode + tag dispatch step of `ChainPB` at `+520`, when
`¬ cur.length ≤ limit` (placed). -/
theorem decodeState_chain_body_536a4_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (cur : List (BitVec 8)) (limit : Nat) (hgt : ¬ cur.length ≤ limit)
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hlinks : ch.links.length + cur.length ≤ 2 * x.st.bytes.length + 4)
    (herr_of_none :
      mergeLoopBin ChainPB.mergeField (cur.length - limit) ch cur limit 99 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 * cur.length + 8 ≤ rem)
    (hf : f + 4 * cur.length + 8 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hpost_env : ∀ evs, DecodeStateEnv x evs → PostEnv x evs)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 520#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length
        ⟨optVn, some ch, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hnext : ∀ (w0' : BitVec 64) (ch' : ChainPB) (rest2 : List (BitVec 8))
        (evs_step : List AllocEvent) (sf : State) (P' : SepProp),
      rest2.length < cur.length → rest2.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes rest2 →
      ch'.links.length + rest2.length ≤ ch.links.length + cur.length →
      DecodeStateLoopEnv (f + 4 * (cur.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_step) →
      M.stepEvents (evs_acc ++ evs_step) st0 = M.stepEvents evs_step st →
      FitsEnv M lim (M.stepEvents evs_step st)
        (DecodeStateLoopEnv (rem - 4 * (cur.length - rest2.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      mergeLoopBin ChainPB.mergeField (cur.length - limit) ch cur limit 99 =
        mergeLoopBin ChainPB.mergeField (rest2.length - limit) ch' rest2 limit 99 →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, some ch', inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_step st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hfits8 : FitsEnv M lim st
      (DecodeStateLoopEnv (4 * cur.length + 8) x.st.bytes.length
        (2 * x.st.bytes.length + 16)) :=
    SpecsBudget.FitsEnv.decodeStateLoop_mono hrem (Nat.le_refl _) (Nat.le_refl _) hFit
  have henv_err8 : ∀ evs_err,
      DecodeStateLoopEnv (4 * cur.length + 8) x.st.bytes.length
        (2 * x.st.bytes.length + 16) evs_err →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = M.stepEvents evs_err st :=
    acc_henv_err hacc hst (by omega) hpost_env
  have hdv_call := hc.decodeVarint2
  subst hP
  rw [sliceCursorAfter_eq_split hcur_le hcur_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced]
    at hpc hdv_call ⊢
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
  wp_steps_sync_pool (lsmpl.base 291)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpIPlaced.call_decodeVarint2 hdv_call
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur st
    (ret_pc := (blkPl_325).base + 528#64)
    (hpc := by simp only [wp_norm, arm64_norm]) (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm]) (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hfits := err3_fits1 (by omega) (fun _ => .of_decodeVarint2) hfits8)
    (hP := by sep_focus) ?_ ?_
  · intro s1 key rest1 evs_dv hdv hevs_dv hlt1 hsuf1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_key
    have hevs_nil := decodeVarint2Env_eq_nil_of_some hdv hevs_dv
    subst hevs_nil
    simp only [M.stepEvents_nil]
    have hle1 : rest1.length ≤ cur.length := Nat.le_of_lt hlt1
    have hrest1_le : rest1.length ≤ x.st.bytes.length := Nat.le_trans hle1 hcur_le
    have hrest1_suf : IsDropSuffix x.st.bytes rest1 := suffix_trans hcur_le hcur_suf hle1 hsuf1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx1_key hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
    simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    by_cases hk : 2 ^ 32 ≤ key.toNat
    · have hk_ne : (key >>> 32 == 0#64) = false := key_lsr32_ne_zero_of_ge hk
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1776#64)
      wp_steps 3
      refine SepWP.fold (after_decodeVarint2_to_errFrame_placed H_inner A lim st x hcur_le hcur_suf
        hle1 ⟨optVn, some ch, inner⟩ s0 s1)
        (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, hx0_0, hx1_key, hk_ne])
        (by simp only [arm64_norm, hrun1])
      exact SepWPpIPlaced.of_sepWPp (decodeState_err_53b8c_placed_ofEnv
        hc.toDecodeStateCalleeContractsPlaced x st0 st ⟨optVn, some ch, inner⟩ w0 s0 _ _ R post
        hpost
        (herr_of_none (mergeLoopBin_of_key_ge protoPrefixStep_chainPB_mergeField hgt hdv hk))
        (err3_fits1 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits8)
        (err3_fits2 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits8)
        (err3_env (by omega) (fun _ => decodeErrorFromEnv_iter) henv_err8)
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hx1_key, hk_ne])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
        (by simp only [arm64_norm, htr1])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by
          unfold decodeStateErrFramePlaced
          dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26,
            Reg.x27, Reg.x28, Reg.x29, Reg.x30]
          simp only [wp_norm, arm64_norm]
          try sep_ac_rfl))
    · have hk_zero : key >>> 32 = 0#64 := key_lsr32_eq_zero_of_lt hk
      rcases hwt : WireType.ofNat? (key.toNat % 8) with _ | iwt
      · rcases key_and7_of_wt_none hwt with hand7 | hand7
        · apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1788#64)
          wp_steps 6
          refine SepWP.fold (after_decodeVarint2_to_errFrame_placed H_inner A lim st x hcur_le
            hcur_suf hle1 ⟨optVn, some ch, inner⟩ s0 s1)
            (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7])
            (by simp only [arm64_norm, hrun1])
          exact SepWPpIPlaced.of_sepWPp (decodeState_err_53b98_placed_ofEnv
            hc.toDecodeStateCalleeContractsPlaced x st0 st ⟨optVn, some ch, inner⟩ w0 s0 _ _ R post
            hpost
            (herr_of_none (mergeLoopBin_of_wt_none protoPrefixStep_chainPB_mergeField
              hgt hdv hk hwt))
            (err3_fits1 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits8)
            (err3_fits2 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits8)
            (err3_env (by omega) (fun _ => decodeErrorFromEnv_iter) henv_err8)
            (by dsimp only [decodeStatePlacedEntry]
                simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7])
            (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
            (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
            (by
              unfold decodeStateErrFramePlaced
              dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26,
                Reg.x27, Reg.x28, Reg.x29, Reg.x30]
              simp only [wp_norm, arm64_norm]
              try sep_ac_rfl))
        · apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1788#64)
          wp_steps 6
          refine SepWP.fold (after_decodeVarint2_to_errFrame_placed H_inner A lim st x hcur_le
            hcur_suf hle1 ⟨optVn, some ch, inner⟩ s0 s1)
            (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7])
            (by simp only [arm64_norm, hrun1])
          exact SepWPpIPlaced.of_sepWPp (decodeState_err_53b98_placed_ofEnv
            hc.toDecodeStateCalleeContractsPlaced x st0 st ⟨optVn, some ch, inner⟩ w0 s0 _ _ R post
            hpost
            (herr_of_none (mergeLoopBin_of_wt_none protoPrefixStep_chainPB_mergeField
              hgt hdv hk hwt))
            (err3_fits1 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits8)
            (err3_fits2 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits8)
            (err3_env (by omega) (fun _ => decodeErrorFromEnv_iter) henv_err8)
            (by dsimp only [decodeStatePlacedEntry]
                simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7])
            (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
            (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
            (by
              unfold decodeStateErrFramePlaced
              dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26,
                Reg.x27, Reg.x28, Reg.x29, Reg.x30]
              simp only [wp_norm, arm64_norm]
              try sep_ac_rfl))
      · have hand7 : key &&& 7#64 = BitVec.ofNat 64 iwt.toNat := key_and7_of_wt_some hwt
        have ⟨hwt_ult, hwt_ule⟩ := wt_ult6 iwt
        have hlsr3 : BitVec.truncate 32 key >>> 3 = BitVec.ofNat 32 (key.toNat / 8) :=
          key_lsr3_32_eq hk
        have htag29 : key.toNat / 8 < 2 ^ 29 := tag_lt_pow29_of_key_lt hk
        have hze :
            BitVec.zeroExtend 64 (BitVec.ofNat 32 (key.toNat / 8)) =
              BitVec.ofNat 64 (key.toNat / 8) :=
          tag_zeroExtend64_ofNat32 htag29
        have htw32 :
            BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) =
              BitVec.ofNat 32 (key.toNat / 8) :=
          tag_setWidth32_ofNat (key.toNat / 8)
        by_cases htag0 : key.toNat / 8 < 1
        · have htag_eq0 : key.toNat / 8 = 0 := by omega
          apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1800#64)
          wp_steps 8
          refine SepWP.fold (after_decodeVarint2_to_errFrame_placed H_inner A lim st x hcur_le
            hcur_suf hle1 ⟨optVn, some ch, inner⟩ s0 s1)
            (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
          apply SepWP.done
            (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3,
                  hze, htw32, htag_eq0])
            (by simp only [arm64_norm, hrun1])
          exact SepWPpIPlaced.of_sepWPp (decodeState_err_53ba4_placed_ofEnv
            hc.toDecodeStateCalleeContractsPlaced x st0 st ⟨optVn, some ch, inner⟩ w0 s0 _ _ R post
            hpost
            (herr_of_none (mergeLoopBin_of_tag_zero protoPrefixStep_chainPB_mergeField
              hgt hdv hk hwt htag0))
            (err3_fits1 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits8)
            (err3_fits2 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits8)
            (err3_env (by omega) (fun _ => decodeErrorFromEnv_iter) henv_err8)
            (by dsimp only [decodeStatePlacedEntry]
                simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3,
                  hze, htw32, htag_eq0])
            (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
            (by simp only [arm64_norm, htr1])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by
              unfold decodeStateErrFramePlaced
              dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26,
                Reg.x27, Reg.x28, Reg.x29, Reg.x30]
              simp only [wp_norm, arm64_norm]
              try sep_ac_rfl))
        · have hloop_step := mergeLoopBin_of_key_ok protoPrefixStep_chainPB_mergeField
            (m := ch) (depth' := 99) hgt hdv hk hwt htag0
          rw [decodeState_codecWireTypeToProto_eq] at hloop_step
          have hcbz64 := tag_cbz64_false (by omega : 1 ≤ key.toNat / 8) htag29
          have hcbz32 := tag_cbz32_false (by omega : 1 ≤ key.toNat / 8) htag29
          apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 560#64)
          wp_steps 8
          refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
            hcur_le hcur_suf hle1) (by sep_focus) ?_
          refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
            (a := s0.sp - 1040#64) (rem1 := cur.length) (rem2 := rest1.length)
            (st := ⟨optVn, some ch, inner⟩) hle1) (by sep_focus) ?_
          apply SepWP.done
            (by simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3,
                  hze, htw32, hcbz64, hcbz32])
            (by simp only [arm64_norm, hrun1])
          refine decodeState_chain_dispatch_536cc_placed_ofEnv
            (PreEnv := PreEnv) (PostEnv := PostEnv)
            hc x st0 st evs_acc f rem w0 optVn ch inner rest1 limit (key.toNat / 8) iwt
            (by omega) htag29 hrest1_le hrest1_suf hlen_bound (by omega)
            (fun hnone => herr_of_none (by
              rw [hloop_step]
              revert hnone
              rcases (ch.mergeField (BitVec.ofNat 32 (key.toNat / 8)) (codecWireTypeToProto iwt)
                rest1 99).toOption with _ | ⟨_, _⟩ <;>
                intro hnone <;> exact hnone))
            hacc hst hFit (by omega) (by omega)
            s0 _ _ R post hpost hpost_env hs0A
            (by dsimp only [decodeStatePlacedEntry]
                simp only [arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3,
                  hze, htw32, hcbz64, hcbz32])
            (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
            (by simp only [arm64_norm, htr1])
            (by simp only [arm64_norm, Reg.x0, hand7, *])
            (by simp only [arm64_norm, Reg.x1, hlsr3, hze, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by dsimp only [decodeStateLoopCommonPlaced]; simp only [wp_norm, arm64_norm]; try sep_ac_rfl)
            ?_
          intro w0' ch' rest2 evs_step sf P' hle2 hsuf2 hlinks2 hacc2 hst2 hFit2 hmf
          exact hnext w0' ch' rest2 evs_step sf P'
            (Nat.lt_of_le_of_lt hle2 hlt1) (Nat.le_trans hle2 hrest1_le)
            (suffix_trans hrest1_le hrest1_suf hle2 hsuf2)
            (by omega)
            (hacc2.mono_fuel (by omega))
            hst2
            (SpecsBudget.FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _)
              hFit2)
            (by rw [hloop_step, hmf])
  · intro s1 evs_dv hdv hevs_dv hpc1 hrun1 hsp1 htr1 hcs1 hx0_1 hx1_ne
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_1 hx1_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
    simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2112#64)
    wp_steps 1
    refine SepWP.fold (errFrame_parts_fold A.repAlloc x s0 hcur_le hcur_suf) (by sep_focus) ?_
    refine SepWP.fold (protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A.repAlloc
      (s0.sp - 1040#64) cur.length ⟨optVn, some ch, inner⟩) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hx0_1]) (by simp only [arm64_norm, hrun1])
    exact SepWPpIPlaced.of_sepWPp (decodeState_err_push_53cdc_placed_ofEnv
      hc.toDecodeStateCalleeContractsPlaced x st0 (M.stepEvents evs_dv st)
      ⟨optVn, some ch, inner⟩ w0 0 s0 _ _ R post hpost
      (herr_of_none (mergeLoopBin_of_decodeVarint_none protoPrefixStep_chainPB_mergeField
        hgt hdv))
      (by decide)
      (err3_fits2 (by omega) (fun _ => .of_decodeVarint2) hfits8 evs_dv hevs_dv)
      (fun evs_p evs_f hp hfree =>
        err3_env (by omega) (fun _ => .of_decodeVarint2) henv_err8 evs_dv evs_p evs_f
          hevs_dv hp hfree)
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_1])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
      (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
      (by
        dsimp only [Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
          Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        simp only [wp_norm, arm64_norm]
        try sep_ac_rfl))

theorem decodeState_chain_body_536a4_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (cur : List (BitVec 8)) (limit : Nat) (hgt : ¬ cur.length ≤ limit)
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hlinks : ch.links.length + cur.length ≤ 2 * x.st.bytes.length + 4)
    (herr_of_none :
      mergeLoopBin ChainPB.mergeField (cur.length - limit) ch cur limit 99 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 * cur.length + 8 ≤ rem)
    (hf : f + 4 * cur.length + 8 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 520#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length
        ⟨optVn, some ch, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hnext : ∀ (w0' : BitVec 64) (ch' : ChainPB) (rest2 : List (BitVec 8))
        (evs_step : List AllocEvent) (sf : State) (P' : SepProp),
      rest2.length < cur.length → rest2.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes rest2 →
      ch'.links.length + rest2.length ≤ ch.links.length + cur.length →
      DecodeStateLoopEnv (f + 4 * (cur.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_step) →
      M.stepEvents (evs_acc ++ evs_step) st0 = M.stepEvents evs_step st →
      FitsEnv M lim (M.stepEvents evs_step st)
        (DecodeStateLoopEnv (rem - 4 * (cur.length - rest2.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      mergeLoopBin ChainPB.mergeField (cur.length - limit) ch cur limit 99 =
        mergeLoopBin ChainPB.mergeField (rest2.length - limit) ch' rest2 limit 99 →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, some ch', inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_step st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_chain_body_536a4_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st evs_acc f rem w0 optVn ch inner cur limit hgt hcur_le hcur_suf hlen_bound hlinks
    herr_of_none hacc hst hFit hrem hf s0 s P R post hpost (fun _ h => h) hs0A
    hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hnext

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlacedBudgetAux
