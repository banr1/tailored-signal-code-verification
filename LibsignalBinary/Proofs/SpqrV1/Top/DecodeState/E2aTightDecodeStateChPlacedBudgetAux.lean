/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.E2aTightBytesZeroAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochClPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoopClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainPushClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightChainParamsClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStateEpochPlacedBudgetR2
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopClPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopClPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbChain
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbLeaf
import ProofLib.SepLogic.WPp

/-!
# Canonical Guarded-Tight `ChainPB` Stepping Helpers (`Block 325`)

Proves canonical wire decompositions, zero-error-branch `SepWPpIPlaced` call wrappers,
parametric key-decode steppers (`+116`, `+508`, `+984`), `ChainEpochPB` merge (`+592 -> +624`),
and bounded `Vec<ChainEpochPB>::push` (`0..3` links) for `E2aTightDecodeStateChPlacedBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStateChPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.RustHeap (RustAlloc arrayAt vecAt vecBuf vecHeader vecOf vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost IsDropSuffix decodeVarint_suffix
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt suffix_trans)
open CryptoVerification.SpqrV1.ProtoRepr
  (chainEpochPBAt chainEpochPBSize chainLinksVecAt chainParamsPBAt optChainParamsPBAt)
open CryptoVerification.SpqrV1.Prost.BytesMerge
  (bytesMerge3Stack proto_mergeBytes_toOption)
open CryptoVerification.SpqrV1.Prost.MessageMerge (codecWireTypeToProto v1StateMergeStack)
open CryptoVerification.LibsignalSpqrV1
  (Bytes ChainEpochPB ChainPB ChainParamsPB EpochDirectionPB PqRatchetState VersionNegotiationPB)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeBytesField encodeBytesUncond encodeInt32Field encodeKey encodeMessage encodeOptMessage
   encodeRepeatedMessage encodeUint64Field encodeVarint mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState
  (ChainParamsMergeGhost DecodeStateGhost EpochDirectionMergeGhost Quads14 TraceVRegs
   V1InnerHeapPred bv_len_sub_limit chainEpochPBAt_entails_quads14 chainEpochPBCapOkAt
   chainEpochPBCapOkAt_entails_chainEpochPBAt chainEpochPBCapOkAt_eq_placed
   chainEpochPBCapOkAt_mono chainEpochPBHeap cmp_len_limit_of_eq cmp_len_limit_of_gt
   decodeStatePlacedEntry decodeStatePlacedProg epochDirectionMergeStack epochDirectionPBCapOkAt
   key_and7_of_wt_some key_lsr3_32_eq key_lsr32_eq_zero_of_lt len_ult_of_ge
   memRegion_112_eq_quads14At optChainPBCapOkAt optChainParamsPBAt_some_default_init
   optEpochDirectionPBCapOkAt optEpochDirectionPBCapOkAt_mono optProtoPqRatchetInnerCapOkAt
   optProtoPqRatchetInnerCapOkAt_mono optVersionNegotiationPBCapOkAt
   optVersionNegotiationPBCapOkAt_mono protoPqRatchetStateCapOkAt protoPqRatchetStateCapOkAt_mono
   proto_mergeBytes_suffix proto_mergeMessage_suffix quads14At quads14_entails_chainEpochPBAt
   quads7At quads7At_entails_memRegion_56 quads7_entails_head_and_memRegion_48
   relocArrayAtChainEpochPB sp_sub_1392_aligned stackAt_of_callee stackAt_to_callee
   tag_cbz32_false tag_cbz64_false tag_lt_pow29_of_key_lt
   tag_setWidth32_ofNat tag_zeroExtend64_ofNat32 truncate32_zeroExtend64_lsr3
   vecU8At_nil_zero_one vecU8CapOkAt
   vecU8CapOkAt_mono wt_ult6)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochClPlacedBudgetAux
  (SepWPpIPlaced.call_growOneChainEpoch_cl)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochPlacedBudget
  (chainEpochPBCapOkAt_eq optEpochDirectionPBCapOkAt_none optEpochDirectionPBCapOkAt_some
   optEpochDirectionPB_none_split48)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlacedBudgetAux1
  (optChainParamsPBAt_some_ch_eq protoPqRatchetStateCapOkAt_some_ch_eq_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightChainParamsClPlacedBudget
  (E2aChainParamsCanonicalPostEnv E2aChainParamsCanonicalPreEnv e2a_ChainParamsCanonicalDom
   e2a_chainParamsMerge_cl_placed_ok_canonical e2a_fitsEnv_chainParams_canonical
   e2a_mergeMessage_chainParams_encode)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStateEpochPlacedBudgetR2
  (E2ar2EpochDirCanonicalOk e2ar2_ValidChainEpochPB e2ar2_epoch_merge_tight_536f4)
open CryptoVerification.SpqrV1Sync.Codec
  (loopsTo_chainParams loopsTo_epochDirection mergeMessage_encode)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget (GrowOneStrideEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.E2aTightBytesZeroAux
  (e2a_bytesMergeEventsCore_zero_tight_32 e2a_decodeKey_encodeKey e2a_decodeVarint2Env_eq_nil
   e2a_decodeVarint_encodeVarint e2a_decodeVarint_lenPrefixed e2a_encodeBytesField_append_of_ne
   e2a_encodeBytesField_of_nil e2a_encodeInt32Field_append_of_ne e2a_encodeInt32Field_of_zero
   e2a_encodeUint64Field_append_of_ne e2a_encodeUint64Field_of_zero e2a_fitsEnv_decodeVarint2_of_some
   e2a_fitsEnv_tight_split e2a_growOneChainEpoch_zero_tight e2a_lenPrefixed e2a_mergeBytes_encode)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv bytesMergeEventsCore)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlacedOfEnv decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced bytesMerge3DetBudgetSpec bytesMerge3RawBudgetSpecOfEnv
   decodeStateLoopCommonPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonClPlacedBudget
  (SepWPpIPlaced.call_chainParamsMerge_cl_ofEnv SepWPpIPlaced.call_decodeVarint2_cl)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (epochDirectionMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopClPlacedBudgetAux
  (bytesMerge3Det_of_contractsClPlacedX)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "pool_reg_norm" : tactic =>
  `(tactic| try simp only [RustCliAllocBudget.pool_setPC_norm,
    RustCliAllocBudget.pool_advancePC_norm, RustCliAllocBudget.pool_setPState_norm,
    RustCliAllocBudget.pool_writeReg64_norm, RustCliAllocBudget.pool_writeReg32_norm,
    RustCliAllocBudget.pool_writeReg_norm, RustCliAllocBudget.pool_writeVReg128_norm,
    RustCliAllocBudget.pool_writeVReg64_norm])

private theorem bv_ofNat_mul_112 (ptr : BitVec 64) (n : Nat) :
    ptr + BitVec.ofNat 64 n * 112#64 = ptr + BitVec.ofNat 64 (n * 112) := by
  rw [← BitVec.ofNat_mul]

private theorem bv_ofNat_add_one (n : Nat) :
    BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
  rw [← BitVec.ofNat_add]

attribute [local simp, local arm64_norm] bv_ofNat_mul_112 bv_ofNat_add_one

/-! ## 1. Canonical Wire Decomposition & Round-Trip Helpers -/

theorem e2ar_mergeMessage_epochDirection_encode (m : EpochDirectionPB) (rest : Bytes)
    (hlt : (e2a_lenPrefixed (EpochDirectionPB.encodeRaw m) rest).length < 2 ^ 63) :
    (mergeMessage EpochDirectionPB.mergeField .lengthDelimited default
      (e2a_lenPrefixed (EpochDirectionPB.encodeRaw m) rest) 98).toOption = some (m, rest) := by
  have hlen : (EpochDirectionPB.encodeRaw m).length < 2 ^ 64 := by
    unfold e2a_lenPrefixed at hlt; simp only [List.length_append] at hlt; omega
  unfold e2a_lenPrefixed
  rw [List.append_assoc, mergeMessage_encode EpochDirectionPB.mergeField 0
    EpochDirectionPB.encodeRaw default m 98 rest (loopsTo_epochDirection m hlen) hlen (by decide)]
  rfl

theorem e2ar_encodeMessage_append {α : Type} (enc : α → Bytes) (tag : BitVec 32) (m : α)
    (rest : Bytes) :
    encodeMessage enc tag m ++ rest =
      encodeKey tag .lengthDelimited ++ e2a_lenPrefixed (enc m) rest := by
  dsimp only [encodeMessage, encodeBytesUncond, e2a_lenPrefixed]
  simp only [List.append_assoc]

theorem e2ar_encodeOptMessage_some_append {α : Type} (enc : α → Bytes) (tag : BitVec 32) (m : α)
    (rest : Bytes) :
    encodeOptMessage enc tag (some m) ++ rest =
      encodeKey tag .lengthDelimited ++ e2a_lenPrefixed (enc m) rest := by
  simpa [encodeOptMessage] using e2ar_encodeMessage_append enc tag m rest

theorem e2ar_encodeRepeatedMessage_cons_append {α : Type} (enc : α → Bytes) (tag : BitVec 32)
    (m : α) (ms : List α) (rest : Bytes) :
    encodeRepeatedMessage enc tag (m :: ms) ++ rest =
      encodeKey tag .lengthDelimited ++
        e2a_lenPrefixed (enc m) (encodeRepeatedMessage enc tag ms ++ rest) := by
  change (encodeMessage enc tag m ++ encodeRepeatedMessage enc tag ms) ++ rest = _
  rw [List.append_assoc]
  exact e2ar_encodeMessage_append enc tag m (encodeRepeatedMessage enc tag ms ++ rest)

/-! ## 2. Zero-Error-Branch `SepWPpIPlaced` Call Wrappers -/

theorem e2ar_call_decodeVarint2_some_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget.decodeVarint2Spec A lim)))
    (bufRef slot ptr : BitVec 64) (bs rest : Bytes) (v : BitVec 64) (st : M.σ)
    {n c r : Nat}
    (hd : decodeVarint bs = some (v, rest))
    (hFit : FitsEnv M lim st (SpqrTightEvs n c r))
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = bufRef) (hlen : bs.length < 2 ^ 63)
    (hP : P = ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State),
      rest.length < bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 → sf.readReg64 .x1 = v →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim st sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp := by
  refine SepWPpIPlaced.call_decodeVarint2_cl hcall bufRef slot ptr bs st
    hpc hrun hsp hs0A hlr htr hx0 hlen
    (e2a_fitsEnv_decodeVarint2_of_some hd hFit) hP ?_ ?_
  · intro sf v' rest' evs hdv hevs hlt hsuf hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_v
    have hv : v' = v ∧ rest' = rest := by
      rw [hd] at hdv; exact Prod.mk.inj (Option.some.inj hdv.symm)
    rcases hv with ⟨rfl, rfl⟩
    have hevs0 : evs = [] := e2a_decodeVarint2Env_eq_nil hd hevs
    subst hevs0
    rw [M.stepEvents_nil]
    exact hok sf hlt hsuf hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_v
  · intro _ _ hnone
    rw [hd] at hnone; cases hnone

theorem e2ar_call_bytesMerge3_zero_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (bytesMerge3DetBudgetSpec A lim)))
    (valPtr valBuf bufRef slot ptr : BitVec 64) (bs v rest : Bytes) (st : M.σ)
    (hm : mergeBytes .lengthDelimited bs = some (v, rest))
    (hv_le : v.length ≤ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs 2 1476 32))
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc) (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = valPtr) (hx2 : s.readReg64 .x2 = bufRef)
    (hlen : bs.length < 2 ^ 63)
    (hP : P = (vecU8At A.repAlloc valPtr 0#64 valBuf [] ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (evs : List AllocEvent),
      SpqrTightEvs 2 1476 32 evs →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          vecU8CapOkAt A.repAlloc valPtr rest.length v ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp := by
  intro hinv R' hm_sat hL
  let sp_cur := s0.sp - 1392#64
  let x_bm : BytesMergeGhost := ⟨.lengthDelimited, valPtr, 0#64, valBuf, [], bufRef, slot, ptr, bs⟩
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - bytesMerge3Stack) ∗ F
  have hcap_ok : BytesMergeCapOk 0#64 bs.length := Or.inl rfl
  have htight_evs : SpqrTightEvs 2 1476 32 (bytesMergeEventsCore .lengthDelimited 0#64 bs) :=
    e2a_bytesMergeEventsCore_zero_tight_32 hm hv_le
  have hfits_bm : FitsEnv M lim st (BytesMergeEnv x_bm) := by
    intro evs hevs
    rw [hevs]
    exact hFit _ htight_evs
  have hpre : s.mem ⊨
      (withLsCodeRoLoaded lsmpl (bytesMerge3DetBudgetSpec A lim)).pre (x_bm, st) s ∗ (F_ext ∗ R') := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    dsimp only [bytesMerge3DetBudgetSpec, bytesMerge3RawBudgetSpecOfEnv, x_bm]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen, hcap_ok, hfits_bm⟩, ?_⟩
    rw [hP] at hm_sat
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur bytesMerge3Stack (by decide)))))))) hm_sat
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; sep_ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome (x_bm, st) (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ (bytesMerge3DetBudgetSpec A lim).post (x_bm, st) s sm ∗ (F_ext ∗ R') at hpost
    dsimp only [bytesMerge3DetBudgetSpec, bytesMerge3RawBudgetSpecOfEnv, x_bm] at hpost
    rw [hm, hsp] at hpost
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨cap', ptr', evs, hpost⟩
    have hpost_pure : sm.mem ⊨ ⌜BytesMergeEnv x_bm evs⌝ ∗
        (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64⌝ ∗
          (⌜BytesMergeCapOk cap' rest.length⌝ ∗
            (vecU8At A.repAlloc valPtr cap' ptr' v ∗
              (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
                (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
                  (v1StateMergeStack - bytesMerge3Stack) ∗
                  stackAt sp_cur bytesMerge3Stack) ∗
                sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R')))) := by
      refine Satisfies.mono (Entails.of_eq ?_) hpost
      dsimp only [sp_cur, F_ext]; sep_ac_rfl
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj,
      satisfies_pure_sepConj] at hpost_pure
    rcases hpost_pure with ⟨hevs, htrm, hx0_0, hcap', hpost1⟩
    rw [hlr] at hpcm; rw [hsp] at hspm
    have hvec' : vecU8At A.repAlloc valPtr cap' ptr' v ⊢
        vecU8CapOkAt A.repAlloc valPtr rest.length v := by
      unfold vecU8CapOkAt
      exact Entails.sepExists_right cap'
        (Entails.sepExists_right ptr' (Entails.pure_right hcap' (Entails.refl _)))
    have hpost1' := Satisfies.mono (sepConj_mono hvec' (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (stackAt_of_callee sp_cur bytesMerge3Stack (by decide)))))))) hpost1
    have hpost2 : sm.mem ⊨
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt sp_cur v1StateMergeStack ∗
          vecU8CapOkAt A.repAlloc valPtr rest.length v ∗
          sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R' :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost1'
    have hproto : (CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes .lengthDelimited bs).toOption =
        some (v, rest) := by
      rw [proto_mergeBytes_toOption]; exact hm
    have ⟨hle, hsuf⟩ := proto_mergeBytes_suffix hproto
    have hevs_tight : SpqrTightEvs 2 1476 32 evs := by
      change evs = bytesMergeEventsCore .lengthDelimited 0#64 bs at hevs
      rw [hevs]; exact htight_evs
    obtain ⟨sf, hsteps', hout'⟩ :=
      hok sm evs hevs_tight hle hsuf hpcm hrunm hspm
        (htr.step htrm hcsm) hcsm hx0_0 (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [bytesMerge3DetBudgetSpec, bytesMerge3RawBudgetSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [bytesMerge3DetBudgetSpec, bytesMerge3RawBudgetSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [bytesMerge3DetBudgetSpec, bytesMerge3RawBudgetSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

/-! ## 3. Scratch Split & Parametric Key-Decode Steppers (`+116`, `+508`, `+984`) -/

theorem e2ar_epoch_scratch_split_recv_240 (sp : BitVec 64) :
    memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 ⊢
      ∃∗ w_recv : BitVec 64,
        memRegion (sp - 680#64) 48 ∗
        ((sp - 632#64) ↦₆₄ w_recv) ∗
        memRegion (sp - 624#64) 48 ∗
        memRegion (sp - 576#64) 240 := by
  have hs1 := ProofLib.memRegion_split' (b := sp - 640#64) (n := 8) (k := 296)
    (b' := sp - 632#64) rfl (by bv_omega) (by decide)
  have hs2 := ProofLib.memRegion_split' (b := sp - 632#64) (n := 8) (k := 288)
    (b' := sp - 624#64) rfl (by bv_omega) (by decide)
  have hs3 := ProofLib.memRegion_split' (b := sp - 624#64) (n := 48) (k := 240)
    (b' := sp - 576#64) rfl (by bv_omega) (by decide)
  have hj := ProofLib.memRegion_split' (b := sp - 680#64) (n := 40) (k := 8)
    (b' := sp - 640#64) rfl (by bv_omega) (by decide)
  rw [hs1, hs2, hs3, ProofLib.memRegion_eight (sp - 632#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w_recv
  refine Entails.sepExists_right w_recv ?_
  rw [hj]
  exact Entails.of_eq (by sep_ac_rfl)

theorem e2ar_outer_key_decode_tag2_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (F_state : SepProp)
    {cur rest1 : Bytes} {n c r : Nat}
    (hcur_eq : cur = encodeKey 2#32 .lengthDelimited ++ rest1)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs n c r))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 116#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      F_state ∗ decodeStateLoopCommonPlaced A lim st x s0 s)
    (hok : ∀ (sf : State),
      rest1.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes rest1 →
      sf.pc = decodeStatePlacedEntry + 160#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x0 = BitVec.ofNat 64 WireType.lengthDelimited.toNat →
      sf.readReg64 .x1 = 2#64 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf
        (sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
          F_state ∗ decodeStateLoopCommonPlaced A lim st x s0 sf)
        post (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  have ⟨hdv0, hkey_nat, hk, hwt, hdiv8, htag0⟩ :=
    e2a_decodeKey_encodeKey 2#32 .lengthDelimited rest1 (by decide) (by decide)
  let key := ((2#32 <<< 3) |||
    (CryptoVerification.LibsignalSpqrV1.Proto.WireType.lengthDelimited).toU32).zeroExtend 64
  have hdv : decodeVarint cur = some (key, rest1) := by rw [hcur_eq]; exact hdv0
  have hgt : ¬ cur.length ≤ 0 := by
    have hlt0 := decodeVarint_length hdv; omega
  have ⟨hcmp_ne, hcmp_le⟩ := cmp_len_limit_of_gt hgt (by omega)
  have hdv_call := hc.decodeVarint2
  subst hP
  rw [sliceCursorAfter_eq_split hcur_le hcur_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced]
    at hpc hdv_call ⊢
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
  wp_steps_sync_pool (lsmpl.base 291)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm, hcmp_ne, hcmp_le])
    (by simp only [wp_norm, arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine e2ar_call_decodeVarint2_some_cl hdv_call
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur rest1 key st hdv hFit
    (ret_pc := (blkPl_325).base + 124#64)
    (hpc := by simp only [wp_norm, arm64_norm]) (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm]) (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hP := by pool_reg_norm; sep_focus) ?_
  intro s1 hlt1 hsuf1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_key
  have hle1 : rest1.length ≤ cur.length := Nat.le_of_lt hlt1
  have hrest1_le : rest1.length ≤ x.st.bytes.length := Nat.le_trans hle1 hcur_le
  have hrest1_suf : IsDropSuffix x.st.bytes rest1 := suffix_trans hcur_le hcur_suf hle1 hsuf1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, _⟩
  simp only [arm64_norm, wp_norm] at hx0_0 hx1_key hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
  simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  have hk_zero : key >>> 32 = 0#64 := key_lsr32_eq_zero_of_lt hk
  have hand7 : key &&& 7#64 = BitVec.ofNat 64 WireType.lengthDelimited.toNat := by decide
  have ⟨hwt_ult, hwt_ule⟩ := wt_ult6 WireType.lengthDelimited
  have hlsr3 : BitVec.truncate 32 key >>> 3 = 2#32 := by decide
  have hlsr3_64 : BitVec.zeroExtend 64 (BitVec.truncate 32 key) >>> 3 = 2#64 := by decide
  have hze : BitVec.zeroExtend 64 2#32 = 2#64 := by decide
  have htw32 : BitVec.truncate 32 2#64 = 2#32 := by decide
  have hcbz64 : (2#64 == 0#64) = false := by decide
  have hcbz32 : (2#32 == 0#32) = false := by decide
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 160#64)
  wp_steps 9
  refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
    hcur_le hcur_suf hle1) (by sep_focus) ?_
  apply SepWP.done
    (by simp only [wp_norm, arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule,
          hlsr3, hlsr3_64, hze, htw32, hcbz64, hcbz32])
    (by simp only [wp_norm, arm64_norm, hrun1])
  refine SepWPpIPlaced.mono_pre (Entails.of_eq ?_)
    (hok _ hrest1_le hrest1_suf
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun1])
      (by simp only [wp_norm, arm64_norm, hsp1])
      (by simp only [wp_norm, arm64_norm, htr1])
      (by simp only [wp_norm, arm64_norm, hx0_0, hx1_key, hand7])
      (by simp only [wp_norm, arm64_norm, hx0_0, hx1_key, hlsr3, hze])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]))
  dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; sep_ac_rfl

/-- Zero-allocation canonical `ChainPB` loop exit at `+508 -> +1576` when `cur = rest`
(`cur.length = rest.length`). -/
theorem e2ar_chain_exit_508_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (rest : Bytes)
    (hrest_le : rest.length ≤ x.st.bytes.length)
    (hrest_suf : IsDropSuffix x.st.bytes rest)
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 508#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 rest.length)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest ∗
      protoPqRatchetStateCapOkAt H_i A.repAlloc (s0.sp - 1040#64) rest.length
        ⟨optVn, some ch, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (sf : State) (P' : SepProp),
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 rest.length →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest ∗
        protoPqRatchetStateCapOkAt H_i A.repAlloc (s0.sp - 1040#64) rest.length
          ⟨optVn, some ch, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have ⟨hult, hule, hbeq⟩ := cmp_len_limit_of_eq (rfl : rest.length = rest.length)
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, sliceCursorAfter] at hpc ⊢
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1576#64)
  wp_steps 4
  apply SepWP.done (by simp only [arm64_norm, hult, hule, hbeq])
    (by simp only [arm64_norm, hrun])
  exact hdone _ _
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hbeq])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
    (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
    (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
    (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
    (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
    (by simp only [arm64_norm, hx29])
    (by dsimp only [sliceCursorAfter, decodeStateLoopCommonPlaced]
        pool_reg_norm; try sep_ac_rfl)

/-- Zero-error-branch canonical `ChainParamsPB::merge` (`Block 294`) call wrapper (`evs = []`). -/
theorem e2ar_call_chainParams_canonical_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (msgPtr bufRef slot ptr : BitVec 64) (cp : ChainParamsPB) (bs rest : Bytes) (st : M.σ)
    (hbs_eq : bs = e2a_lenPrefixed (ChainParamsPB.encodeRaw cp) rest)
    {ret ret_pc : BitVec 64}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 294) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc) (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat)
    (hx1 : s.readReg64 .x1 = msgPtr) (hx2 : s.readReg64 .x2 = bufRef)
    (hlen : bs.length < 2 ^ 63)
    (hP : P = (chainParamsPBAt msgPtr default ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State),
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced (decodeStatePlacedProg ext) ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim st sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          chainParamsPBAt msgPtr cp ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp) :
    SepWPpIPlaced (decodeStatePlacedProg ext) ret s P Q Qp := by
  have hcall := e2a_chainParamsMerge_cl_placed_ok_canonical hc.toDecodeStateCalleeContractsClPlaced
  have hdom : e2a_ChainParamsCanonicalDom
      ⟨.lengthDelimited, msgPtr, default, bufRef, slot, ptr, bs⟩ :=
    ⟨rfl, rfl, cp, rest, hbs_eq⟩
  have hmm_canon :
      (mergeMessage ChainParamsPB.mergeField .lengthDelimited default bs 99).toOption =
        some (cp, rest) := by
    rw [hbs_eq, e2a_mergeMessage_chainParams_encode cp rest]; rfl
  dsimp only [decodeStatePlacedProg] at hok ⊢
  refine SepWPpIPlaced.call_chainParamsMerge_cl_ofEnv hcall .lengthDelimited msgPtr default
    bufRef slot ptr bs st hpc hrun hsp hs0A hlr htr hx0 hx1 hx2 hlen
    (e2a_fitsEnv_chainParams_canonical st hdom) hP ?_ ?_
  · intro sf m' rest' evs hmm hevs hle hsuf hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    change (mergeMessage ChainParamsPB.mergeField .lengthDelimited default bs 99).toOption =
      some (m', rest') at hmm
    rw [hmm_canon] at hmm
    have hmr : m' = cp ∧ rest' = rest := Prod.mk.inj (Option.some.inj hmm.symm)
    rcases hmr with ⟨rfl, rfl⟩
    rcases hevs with ⟨_, rfl⟩ | ⟨hnd, _⟩
    · rw [M.stepEvents_nil]
      exact hok sf hle hsuf hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    · exact False.elim (hnd hdom)
  · intro _ _ _ _ hnone
    change (mergeMessage ChainParamsPB.mergeField .lengthDelimited default bs 99).toOption =
      none at hnone
    rw [hmm_canon] at hnone; cases hnone

private theorem e2ar_sepExists_elim [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s : State}
    {α : Type} {P : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ x, SepWPpIPlaced prog ret s (P x) Q Qp) :
    SepWPpIPlaced prog ret s (∃∗ x, P x) Q Qp := by
  intro hinv R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hm⟩
  exact h x hinv R hm hL

private theorem e2ar_pure_sepConj_elim [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s : State}
    {p : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : p → SepWPpIPlaced prog ret s P Q Qp) :
    SepWPpIPlaced prog ret s (⌜p⌝ ∗ P) Q Qp := by
  intro hinv R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 hinv R hm.2 hL

private theorem e2ar_pool_sync_step [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {prog : Program} {ret : BitVec 64} {s s' : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (h : ∀ hp : A.pool lim st s = A.pool lim st s', SepWPpIPlaced prog ret s' P Q Qp)
    (hp : A.pool lim st s = A.pool lim st s' := by pool_reg_norm) :
    SepWPpIPlaced prog ret s' P Q Qp :=
  h hp

private theorem e2ar_arrayAt_112_append_singleton (elem : ChainEpochPB → BitVec 64 → SepProp)
    (p : BitVec 64) (xs : List ChainEpochPB) (ep : ChainEpochPB) :
    arrayAt elem 112 p xs ∗ elem ep (p + BitVec.ofNat 64 (xs.length * 112)) =
      arrayAt elem 112 p (xs ++ [ep]) := by
  induction xs generalizing p with
  | nil =>
    simp only [arrayAt, List.nil_append, List.length_nil, Nat.zero_mul, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero]
    sep_ac_rfl
  | cons y ys ih =>
    simp only [arrayAt, List.cons_append, List.length_cons]
    have haddr : p + 112#64 + BitVec.ofNat 64 (ys.length * 112) =
        p + BitVec.ofNat 64 ((ys.length + 1) * 112) := by
      have hm : (ys.length + 1) * 112 = 112 + ys.length * 112 := by omega
      rw [hm, BitVec.ofNat_add, ← BitVec.add_assoc]
    rw [← haddr, ← ih (p + 112#64)]
    sep_ac_rfl

/-- Canonical Tag 4 (`nextRoot : Bytes`, `ch.nextRoot.length ≤ 32`) handler at `+824 -> +508`
for `ch.nextRoot ≠ []` from zero-capacity `vecU8At ... 0#64 1#64 []` (`SpqrTightEvs 2 1476 32`). -/
theorem e2ar_chain_tag4_call_824_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ)
    (F_state : Nat → SepProp) (hF_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → F_state r1 ⊢ F_state r2)
    (v rest1 restAfter : Bytes)
    (hrest1_eq : rest1 = e2a_lenPrefixed v restAfter)
    (hv_le : v.length ≤ 32)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs 2 1476 32))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 824#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      vecU8At A.repAlloc (s0.sp - 968#64) 0#64 1#64 [] ∗
      F_state rest1.length ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (evs_bm : List AllocEvent) (sf : State) (P' : SepProp),
      SpqrTightEvs 2 1476 32 evs_bm →
      restAfter.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes restAfter →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        vecU8CapOkAt A.repAlloc (s0.sp - 968#64) restAfter.length v ∗
        F_state restAfter.length ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_bm st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hbm_call := bytesMerge3Det_of_contractsClPlacedX hc
  have hm : mergeBytes .lengthDelimited rest1 = some (v, restAfter) := by
    rw [hrest1_eq]; exact e2a_mergeBytes_encode (by omega)
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced]
    at hpc hbm_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 290)
  wp_steps_sync_pool (lsmpl.base 290)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  have hx22_48 : s0.sp - 1040#64 + 72#64 = s0.sp - 968#64 := by bv_omega
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine e2ar_call_bytesMerge3_zero_cl hbm_call (s0.sp - 968#64) 1#64 (s0.sp - 336#64)
    (s0.sp - 1056#64) (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length))
    rest1 v restAfter st hm hv_le hFit
    (ret_pc := (blkPl_325).base + 836#64)
    (hpc := by simp only [wp_norm, arm64_norm]) (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm]) (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx0]; try decide)
    (hx1 := by simp only [wp_norm, arm64_norm, hx22, hx22_48])
    (hx2 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hP := by pool_reg_norm; sep_focus) ?_
  intro s1 evs_bm hevs_bm hle1 hsuf1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
  have hafter_le : restAfter.length ≤ x.st.bytes.length := Nat.le_trans hle1 hrest1_le
  have hafter_suf : IsDropSuffix x.st.bytes restAfter := suffix_trans hrest1_le hrest1_suf hle1 hsuf1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, _⟩
  simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
  simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 508#64)
  wp_steps_sync_pool ((blkPl_325).base + 508#64)
  try simp only [State.setMem_setMem]
  refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
    hrest1_le hrest1_suf hle1) (by sep_focus) ?_
  refine SepWP.fold (hF_mono hle1) (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
  exact hdone evs_bm _ _ hevs_bm hafter_le hafter_suf
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1]) (by simp only [wp_norm, arm64_norm, hsp1])
    (by simp only [wp_norm, arm64_norm, htr1])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; sep_ac_rfl)

theorem e2ar_optChainParams_cells_of_zero (a : BitVec 64) :
    (a ↦₃₂ 0#32) ∗ memRegion (a + 4#64) 8 ⊢
      ∃∗ w64 : BitVec 64, ∃∗ w32 : BitVec 32, (a ↦₆₄ w64) ∗ ((a + 8#64) ↦₃₂ w32) := by
  have h4 : (a ↦₃₂ 0#32) ⊢ memRegion a 4 := by
    rw [ProofLib.memRegion_four a]
    exact Entails.sepExists_right 0#32 (Entails.refl _)
  have hs1 := ProofLib.memRegion_split' (b := a) (n := 4) (k := 8) (b' := a + 4#64)
    rfl (by bv_omega) (by decide)
  have hs2 := ProofLib.memRegion_split' (b := a) (n := 8) (k := 4) (b' := a + 8#64)
    rfl (by bv_omega) (by decide)
  refine Entails.trans (sepConj_mono_left h4) ?_
  rw [← hs1, hs2, ProofLib.memRegion_eight a, ProofLib.memRegion_four (a + 8#64)]
  rw [sepExists_sepConj_left]
  simp only [sepExists_sepConj_right]
  exact Entails.refl _

/-- Canonical Tag 1 (`direction : BitVec 32`) handler at `+792 -> +508` (`evs = []`). -/
theorem e2ar_chain_tag1_call_792_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ)
    (F_state : Nat → SepProp) (hF_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → F_state r1 ⊢ F_state r2)
    (v : BitVec 32) (rest1 restAfter : Bytes) {n c r : Nat}
    (hrest1_eq : rest1 = encodeVarint (v.signExtend 64) ++ restAfter)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs n c r))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 792#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 WireType.varint.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      ((s0.sp - 916#64) ↦₃₂ 0#32) ∗
      F_state rest1.length ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (sf : State) (P' : SepProp),
      restAfter.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes restAfter →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        ((s0.sp - 916#64) ↦₃₂ v) ∗
        F_state restAfter.length ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hdv_call := hc.decodeVarint2
  have hdv : decodeVarint rest1 = some (v.signExtend 64, restAfter) := by
    rw [hrest1_eq]; exact e2a_decodeVarint_encodeVarint (v.signExtend 64) restAfter
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced,
    WireType.toNat] at hpc hdv_call hx0 ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
  wp_steps_sync_pool (lsmpl.base 291)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm, hx0])
    (by simp only [wp_norm, arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine e2ar_call_decodeVarint2_some_cl hdv_call
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length))
    rest1 restAfter (v.signExtend 64) st hdv hFit
    (ret_pc := (blkPl_325).base + 804#64)
    (hpc := by simp only [wp_norm, arm64_norm]) (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm]) (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hP := by pool_reg_norm; sep_focus) ?_
  intro s1 hlt1 hsuf1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_v
  have hle1 : restAfter.length ≤ rest1.length := Nat.le_of_lt hlt1
  have hafter_le : restAfter.length ≤ x.st.bytes.length := Nat.le_trans hle1 hrest1_le
  have hafter_suf : IsDropSuffix x.st.bytes restAfter := suffix_trans hrest1_le hrest1_suf hle1 hsuf1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, _⟩
  simp only [arm64_norm, wp_norm] at hx0_0 hx1_v hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
  simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  have htr32 : BitVec.truncate 32 (v.signExtend 64) = v := by
    ext i hi
    have hi64 : i < 64 := by omega
    simp [BitVec.truncate, BitVec.getElem_signExtend, hi, hi64]
  have hsp476 : s0.sp - 1392#64 + 476#64 = s0.sp - 916#64 := by bv_omega
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 508#64)
  wp_steps_sync_pool ((blkPl_325).base + 508#64)
  try simp only [State.setMem_setMem]
  refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
    hrest1_le hrest1_suf hle1) (by sep_focus) ?_
  refine SepWP.fold (hF_mono hle1) (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm, hx0_0])
    (by simp only [wp_norm, arm64_norm, hrun1])
  exact hdone _ _ hafter_le hafter_suf
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1]) (by simp only [wp_norm, arm64_norm, hsp1])
    (by simp only [wp_norm, arm64_norm, htr1])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by dsimp only [decodeStateLoopCommonPlaced]
        simp only [wp_norm, arm64_norm, hx1_v, htr32, hsp476]
        pool_reg_norm; sep_ac_rfl)

/-- Canonical Tag 2 (`currentEpoch : BitVec 64`) handler at `+872 -> +508` (`evs = []`). -/
theorem e2ar_chain_tag2_call_872_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ)
    (F_state : Nat → SepProp) (hF_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → F_state r1 ⊢ F_state r2)
    (v : BitVec 64) (rest1 restAfter : Bytes) {n c r : Nat}
    (hrest1_eq : rest1 = encodeVarint v ++ restAfter)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs n c r))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 872#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 WireType.varint.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      ((s0.sp - 944#64) ↦₆₄ 0#64) ∗
      F_state rest1.length ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (sf : State) (P' : SepProp),
      restAfter.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes restAfter →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        ((s0.sp - 944#64) ↦₆₄ v) ∗
        F_state restAfter.length ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hdv_call := hc.decodeVarint2
  have hdv : decodeVarint rest1 = some (v, restAfter) := by
    rw [hrest1_eq]; exact e2a_decodeVarint_encodeVarint v restAfter
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced,
    WireType.toNat] at hpc hdv_call hx0 ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
  wp_steps_sync_pool (lsmpl.base 291)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm, hx0])
    (by simp only [wp_norm, arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine e2ar_call_decodeVarint2_some_cl hdv_call
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length))
    rest1 restAfter v st hdv hFit
    (ret_pc := (blkPl_325).base + 884#64)
    (hpc := by simp only [wp_norm, arm64_norm]) (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm]) (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hP := by pool_reg_norm; sep_focus) ?_
  intro s1 hlt1 hsuf1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_v
  have hle1 : restAfter.length ≤ rest1.length := Nat.le_of_lt hlt1
  have hafter_le : restAfter.length ≤ x.st.bytes.length := Nat.le_trans hle1 hrest1_le
  have hafter_suf : IsDropSuffix x.st.bytes restAfter := suffix_trans hrest1_le hrest1_suf hle1 hsuf1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, _⟩
  simp only [arm64_norm, wp_norm] at hx0_0 hx1_v hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
  simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  have hsp448 : s0.sp - 1392#64 + 448#64 = s0.sp - 944#64 := by bv_omega
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 508#64)
  wp_steps_sync_pool ((blkPl_325).base + 508#64)
  try simp only [State.setMem_setMem]
  refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
    hrest1_le hrest1_suf hle1) (by sep_focus) ?_
  refine SepWP.fold (hF_mono hle1) (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm, hx0_0])
    (by simp only [wp_norm, arm64_norm, hrun1])
  exact hdone _ _ hafter_le hafter_suf
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1]) (by simp only [wp_norm, arm64_norm, hsp1])
    (by simp only [wp_norm, arm64_norm, htr1])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by dsimp only [decodeStateLoopCommonPlaced]
        simp only [wp_norm, arm64_norm, hx1_v, hsp448]
        pool_reg_norm; sep_ac_rfl)

/-- Canonical Tag 5 (`sendEpoch : BitVec 64`) handler at `+904 -> +508` (`evs = []`). -/
theorem e2ar_chain_tag5_call_904_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ)
    (F_state : Nat → SepProp) (hF_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → F_state r1 ⊢ F_state r2)
    (v : BitVec 64) (rest1 restAfter : Bytes) {n c r : Nat}
    (hrest1_eq : rest1 = encodeVarint v ++ restAfter)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs n c r))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 904#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 WireType.varint.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      ((s0.sp - 936#64) ↦₆₄ 0#64) ∗
      F_state rest1.length ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (sf : State) (P' : SepProp),
      restAfter.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes restAfter →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        ((s0.sp - 936#64) ↦₆₄ v) ∗
        F_state restAfter.length ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hdv_call := hc.decodeVarint2
  have hdv : decodeVarint rest1 = some (v, restAfter) := by
    rw [hrest1_eq]; exact e2a_decodeVarint_encodeVarint v restAfter
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced,
    WireType.toNat] at hpc hdv_call hx0 ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
  wp_steps_sync_pool (lsmpl.base 291)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm, hx0])
    (by simp only [wp_norm, arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine e2ar_call_decodeVarint2_some_cl hdv_call
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length))
    rest1 restAfter v st hdv hFit
    (ret_pc := (blkPl_325).base + 916#64)
    (hpc := by simp only [wp_norm, arm64_norm]) (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm]) (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hP := by pool_reg_norm; sep_focus) ?_
  intro s1 hlt1 hsuf1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_v
  have hle1 : restAfter.length ≤ rest1.length := Nat.le_of_lt hlt1
  have hafter_le : restAfter.length ≤ x.st.bytes.length := Nat.le_trans hle1 hrest1_le
  have hafter_suf : IsDropSuffix x.st.bytes restAfter := suffix_trans hrest1_le hrest1_suf hle1 hsuf1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, _⟩
  simp only [arm64_norm, wp_norm] at hx0_0 hx1_v hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
  simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  have hsp456 : s0.sp - 1392#64 + 456#64 = s0.sp - 936#64 := by bv_omega
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 508#64)
  wp_steps_sync_pool ((blkPl_325).base + 508#64)
  try simp only [State.setMem_setMem]
  refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
    hrest1_le hrest1_suf hle1) (by sep_focus) ?_
  refine SepWP.fold (hF_mono hle1) (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm, hx0_0])
    (by simp only [wp_norm, arm64_norm, hrun1])
  exact hdone _ _ hafter_le hafter_suf
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1]) (by simp only [wp_norm, arm64_norm, hsp1])
    (by simp only [wp_norm, arm64_norm, htr1])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by dsimp only [decodeStateLoopCommonPlaced]
        simp only [wp_norm, arm64_norm, hx1_v, hsp456]
        pool_reg_norm; sep_ac_rfl)

/-- Canonical Tag 6 (`params : ChainParamsPB`) handler at `+752 -> +508` (`evs = []`). -/
theorem e2ar_chain_tag6_call_752_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred} {v20 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ)
    (F_state : Nat → SepProp) (hF_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → F_state r1 ⊢ F_state r2)
    (cp : ChainParamsPB) (rest1 restAfter : Bytes)
    (hrest1_eq : rest1 = e2a_lenPrefixed (ChainParamsPB.encodeRaw cp) restAfter)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 752#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      optChainParamsPBAt (s0.sp - 928#64) none ∗
      F_state rest1.length ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (sf : State) (P' : SepProp),
      restAfter.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes restAfter →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        optChainParamsPBAt (s0.sp - 928#64) (some cp) ∗
        F_state restAfter.length ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have ha924 : s0.sp - 928#64 + 4#64 = s0.sp - 924#64 := by bv_omega
  have ha920 : s0.sp - 928#64 + 8#64 = s0.sp - 920#64 := by bv_omega
  have hsp464 : s0.sp - 1392#64 + 464#64 = s0.sp - 928#64 := by bv_omega
  have hsp472 : s0.sp - 1392#64 + 472#64 = s0.sp - 920#64 := by bv_omega
  have hx22_74 : s0.sp - 1040#64 + 116#64 = s0.sp - 924#64 := by bv_omega
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  subst hP
  unfold optChainParamsPBAt
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced,
    WireType.toNat] at hpc hx0 ⊢
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 760#64)
  wp_steps_sync_pool ((blkPl_325).base + 760#64)
  try simp only [State.setMem_setMem]
  refine SepWP.fold (e2ar_optChainParams_cells_of_zero (s0.sp - 928#64)) (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply e2ar_sepExists_elim; intro w64
  apply e2ar_sepExists_elim; intro w32
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 768#64)
  wp_steps_sync_pool ((blkPl_325).base + 768#64)
  try simp only [State.setMem_setMem]
  have hinit : ((s0.sp - 928#64) ↦₆₄ 1#64) ∗ ((s0.sp - 920#64) ↦₃₂ 0#32) ⊢
      optChainParamsPBAt (s0.sp - 928#64) (some default) := by
    have h1 := optChainParamsPBAt_some_default_init (s0.sp - 928#64)
    rw [ha920] at h1
    exact h1
  refine SepWP.fold hinit (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  rw [optChainParamsPBAt_some_ch_eq s0.sp default]
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 294)
  wp_steps_sync_pool (lsmpl.base 294)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm, hx0])
    (by simp only [wp_norm, arm64_norm, hrun])
  refine e2ar_call_chainParams_canonical_cl hc (s0.sp - 924#64) (s0.sp - 336#64)
    (s0.sp - 1056#64) (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length))
    cp rest1 restAfter st hrest1_eq
    (ret_pc := (blkPl_325).base + 780#64)
    (hpc := by simp only [wp_norm, arm64_norm]) (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm]) (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx0]; try decide)
    (hx1 := by simp only [wp_norm, arm64_norm, hx22, hx22_74])
    (hx2 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hP := by pool_reg_norm; sep_focus) ?_
  intro s1 hle1 hsuf1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
  have hafter_le : restAfter.length ≤ x.st.bytes.length := Nat.le_trans hle1 hrest1_le
  have hafter_suf : IsDropSuffix x.st.bytes restAfter := suffix_trans hrest1_le hrest1_suf hle1 hsuf1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, _⟩
  simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
  simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 508#64)
  wp_steps_sync_pool ((blkPl_325).base + 508#64)
  try simp only [State.setMem_setMem]
  refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
    hrest1_le hrest1_suf hle1) (by sep_focus) ?_
  refine SepWP.fold (hF_mono hle1) (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm, hx0_0])
    (by simp only [wp_norm, arm64_norm, hrun1])
  exact hdone _ _ hafter_le hafter_suf
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1]) (by simp only [wp_norm, arm64_norm, hsp1])
    (by simp only [wp_norm, arm64_norm, htr1])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by rw [optChainParamsPBAt_some_ch_eq s0.sp cp]
        dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; sep_ac_rfl)

private theorem e2ar_quads14At_sp_688_restore (sp : BitVec 64) (q : Quads14) :
    quads14At (sp - 688#64) q ∗ memRegion (sp - 576#64) 240 ⊢
      ((sp - 688#64) ↦₆₄ q.head) ∗
      memRegion (sp - 680#64) 40 ∗
      memRegion (sp - 640#64) 304 := by
  unfold quads14At Quads14.head
  have h1 := quads7_entails_head_and_memRegion_48 (sp - 688#64) q.1
  have h2 := quads7At_entails_memRegion_56 (sp - 632#64) q.2
  have ha1 : sp - 688#64 + 8#64 = sp - 680#64 := by bv_omega
  have ha2 : sp - 688#64 + 56#64 = sp - 632#64 := by bv_omega
  rw [ha1] at h1; rw [ha2]
  refine Entails.trans (sepConj_mono (sepConj_mono h1 h2) (Entails.refl _)) ?_
  rw [ProofLib.memRegion_split' (b := sp - 680#64) (n := 40) (k := 8)
      (b' := sp - 640#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 640#64) (n := 8) (k := 296)
      (b' := sp - 632#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 632#64) (n := 56) (k := 240)
      (b' := sp - 576#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem e2ar_memRegion_rem_split_112 (ptr : BitVec 64) (len cap : Nat)
    (hlt : len < cap) (hcap63 : cap * 112 < 2 ^ 63) :
    memRegion (ptr + BitVec.ofNat 64 (len * 112)) ((cap - len) * 112) ⊢
      (∃∗ q_dst : Quads14, quads14At (ptr + BitVec.ofNat 64 (len * 112)) q_dst) ∗
      memRegion (ptr + BitVec.ofNat 64 ((len + 1) * 112)) ((cap - (len + 1)) * 112) := by
  have hsplit : (cap - len) * 112 = 112 + (cap - (len + 1)) * 112 := by
    have hsub : cap - len = 1 + (cap - (len + 1)) := by omega
    rw [hsub, Nat.add_mul, Nat.one_mul]
  have haddr : ptr + BitVec.ofNat 64 ((len + 1) * 112) =
      (ptr + BitVec.ofNat 64 (len * 112)) + 112#64 := by
    have hm : (len + 1) * 112 = len * 112 + 112 := by rw [Nat.add_mul, Nat.one_mul]
    rw [hm, BitVec.ofNat_add, BitVec.add_assoc]
  rw [ProofLib.memRegion_split' (b := ptr + BitVec.ofNat 64 (len * 112))
      (n := 112) (k := (cap - (len + 1)) * 112)
      (b' := ptr + BitVec.ofNat 64 ((len + 1) * 112)) hsplit haddr (by omega),
    memRegion_112_eq_quads14At (ptr + BitVec.ofNat 64 (len * 112))]
  exact Entails.refl _

/-! ## 4. Canonical `ChainPB` Key Decode (`+508 -> +560`) & Optional Scalar/Bytes/Params Fields -/

section
attribute [local arm64_norm] truncate32_zeroExtend64_lsr3
attribute [local simp] truncate32_zeroExtend64_lsr3

private theorem e2ar_chain_key_decode_520_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ)
    (F_loop : SepProp)
    (tag : BitVec 32) (wt_p : CryptoVerification.LibsignalSpqrV1.Proto.WireType)
    (wt64 : BitVec 64)
    {cur rest1 : Bytes} {limit n c r : Nat}
    (hcur_eq : cur = encodeKey tag wt_p ++ rest1)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs n c r))
    (htag_pos : 0 < tag.toNat) (htag_lt : tag.toNat < 2 ^ 29)
    (hand7 : (((tag <<< 3) ||| wt_p.toU32).zeroExtend 64) &&& 7#64 = wt64)
    (hwt_ult : BitVec.ult wt64 6#64 = true)
    (hwt_ule : BitVec.ule 6#64 wt64 = false)
    (hlsr3 : BitVec.truncate 32 (((tag <<< 3) ||| wt_p.toU32).zeroExtend 64) >>> 3 = tag)
    (hlsr3_64 :
      BitVec.zeroExtend 64 (BitVec.truncate 32 (((tag <<< 3) ||| wt_p.toU32).zeroExtend 64)) >>> 3 =
        tag.zeroExtend 64)
    (htw32 : BitVec.truncate 32 (tag.zeroExtend 64) = tag)
    (hcbz64 : (tag.zeroExtend 64 == 0#64) = false)
    (hcbz32 : (tag == 0#32) = false)
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 520#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      F_loop ∗ decodeStateLoopCommonPlaced A lim st x s0 s)
    (hok : ∀ (sf : State),
      rest1.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes rest1 →
      sf.pc = decodeStatePlacedEntry + 560#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x0 = wt64 →
      sf.readReg64 .x1 = tag.zeroExtend 64 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf
        (sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
          F_loop ∗ decodeStateLoopCommonPlaced A lim st x s0 sf)
        post (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  have ⟨hdv0, _, hk, _, _, _⟩ := e2a_decodeKey_encodeKey tag wt_p rest1 htag_pos htag_lt
  have hdv : decodeVarint cur = some (((tag <<< 3) ||| wt_p.toU32).zeroExtend 64, rest1) := by
    rw [hcur_eq]; exact hdv0
  have hdv_call := hc.decodeVarint2
  subst hP
  rw [sliceCursorAfter_eq_split hcur_le hcur_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced]
    at hpc hdv_call ⊢
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
  wp_steps_sync_pool (lsmpl.base 291)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine e2ar_call_decodeVarint2_some_cl hdv_call
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur rest1
    (((tag <<< 3) ||| wt_p.toU32).zeroExtend 64) st hdv hFit
    (ret_pc := (blkPl_325).base + 528#64)
    (hpc := by simp only [wp_norm, arm64_norm]) (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm]) (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hP := by pool_reg_norm; sep_focus) ?_
  intro s1 hlt1 hsuf1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_key
  have hle1 : rest1.length ≤ cur.length := Nat.le_of_lt hlt1
  have hrest1_le : rest1.length ≤ x.st.bytes.length := Nat.le_trans hle1 hcur_le
  have hrest1_suf : IsDropSuffix x.st.bytes rest1 := suffix_trans hcur_le hcur_suf hle1 hsuf1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, _⟩
  simp only [arm64_norm, wp_norm] at hx0_0 hx1_key hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
  simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  have hk_zero : (((tag <<< 3) ||| wt_p.toU32).zeroExtend 64) >>> 32 = 0#64 :=
    key_lsr32_eq_zero_of_lt hk
  have hlsr3' : (tag <<< 3 ||| wt_p.toU32) >>> 3 = tag := by
    simpa only [arm64_norm] using hlsr3
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 560#64)
  wp_steps 8
  refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
    hcur_le hcur_suf hle1) (by sep_focus) ?_
  apply SepWP.done
    (by simp only [wp_norm, arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule,
          hlsr3, hlsr3', hlsr3_64, htw32, hcbz64, hcbz32])
    (by simp only [wp_norm, arm64_norm, hrun1])
  refine SepWPpIPlaced.mono_pre (Entails.of_eq ?_)
    (hok _ hrest1_le hrest1_suf
      (by dsimp only [decodeStatePlacedEntry]
          simp only [wp_norm, arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule,
            hlsr3, hlsr3', hlsr3_64, htw32, hcbz64, hcbz32])
      (by simp only [wp_norm, arm64_norm, hrun1])
      (by simp only [wp_norm, arm64_norm, hsp1])
      (by simp only [wp_norm, arm64_norm, htr1])
      (by simp only [wp_norm, arm64_norm, Reg.x0, hx0_0, hx1_key, hand7])
      (by simp only [wp_norm, arm64_norm, Reg.x1, hx0_0, hx1_key, hlsr3, hlsr3', hlsr3_64])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))
  dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; sep_ac_rfl

theorem e2ar_chain_key_decode_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ)
    (F_loop : SepProp)
    (tag : BitVec 32) (wt_p : CryptoVerification.LibsignalSpqrV1.Proto.WireType)
    (wt64 : BitVec 64)
    {cur rest1 : Bytes} {limit n c r : Nat}
    (hcur_eq : cur = encodeKey tag wt_p ++ rest1)
    (hlim_le : limit ≤ rest1.length)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs n c r))
    (htag_pos : 0 < tag.toNat) (htag_lt : tag.toNat < 2 ^ 29)
    (hand7 : (((tag <<< 3) ||| wt_p.toU32).zeroExtend 64) &&& 7#64 = wt64)
    (hwt_ult : BitVec.ult wt64 6#64 = true)
    (hwt_ule : BitVec.ule 6#64 wt64 = false)
    (hlsr3 : BitVec.truncate 32 (((tag <<< 3) ||| wt_p.toU32).zeroExtend 64) >>> 3 = tag)
    (hlsr3_64 :
      BitVec.zeroExtend 64 (BitVec.truncate 32 (((tag <<< 3) ||| wt_p.toU32).zeroExtend 64)) >>> 3 =
        tag.zeroExtend 64)
    (htw32 : BitVec.truncate 32 (tag.zeroExtend 64) = tag)
    (hcbz64 : (tag.zeroExtend 64 == 0#64) = false)
    (hcbz32 : (tag == 0#32) = false)
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 508#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      F_loop ∗ decodeStateLoopCommonPlaced A lim st x s0 s)
    (hok : ∀ (sf : State),
      rest1.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes rest1 →
      sf.pc = decodeStatePlacedEntry + 560#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x0 = wt64 →
      sf.readReg64 .x1 = tag.zeroExtend 64 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf
        (sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
          F_loop ∗ decodeStateLoopCommonPlaced A lim st x s0 sf)
        post (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  have ⟨hdv0, _, _, _, _, _⟩ := e2a_decodeKey_encodeKey tag wt_p rest1 htag_pos htag_lt
  have hdv : decodeVarint cur = some (((tag <<< 3) ||| wt_p.toU32).zeroExtend 64, rest1) := by
    rw [hcur_eq]; exact hdv0
  have hgt : ¬ cur.length ≤ limit := by
    have hlt0 := decodeVarint_length hdv; omega
  have ⟨hult, hule⟩ := cmp_len_limit_of_gt hgt (by omega)
  have hule' : (BitVec.ofNat 64 (encodeKey tag wt_p ++ rest1).length).ule
      (BitVec.ofNat 64 limit) = false := hcur_eq ▸ hule
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, sliceCursorAfter] at hpc ⊢
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 520#64)
  wp_steps 3
  apply SepWP.done (by simp only [arm64_norm, hult, hule, hule']) (by simp only [arm64_norm, hrun])
  exact e2ar_chain_key_decode_520_cl (limit := limit) hc x st0 st F_loop tag wt_p wt64
    hcur_eq hcur_le hcur_suf hlen_bound hFit
    htag_pos htag_lt hand7 hwt_ult hwt_ule hlsr3 hlsr3_64 htw32 hcbz64 hcbz32
    hs0A
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hule'])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
    (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
    (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
    (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
    (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
    (by simp only [arm64_norm, hx29])
    (by
      dsimp only [sliceCursorAfter, decodeStateLoopCommonPlaced]
      simp only [wp_norm, arm64_norm]
      pool_reg_norm
      try sep_ac_rfl)
    hok

end

/-- Optional Tag 1 (`encodeInt32Field 1#32 v ++ restAfter`) at `+508 -> +508` (`evs = []`). -/
theorem e2ar_chain_tag1_opt_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ)
    (F_state : Nat → SepProp) (hF_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → F_state r1 ⊢ F_state r2)
    (v : BitVec 32) {cur restAfter : Bytes} {limit n c r : Nat}
    (hcur_eq : cur = encodeInt32Field 1#32 v ++ restAfter)
    (hlim_le : limit ≤ restAfter.length)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs n c r))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 508#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      ((s0.sp - 916#64) ↦₃₂ 0#32) ∗
      F_state cur.length ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (sf : State) (P' : SepProp),
      restAfter.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes restAfter →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        ((s0.sp - 916#64) ↦₃₂ v) ∗
        F_state restAfter.length ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  by_cases hv : v = 0#32
  · subst hv
    rw [e2a_encodeInt32Field_of_zero, List.nil_append] at hcur_eq
    subst hcur_eq
    exact hdone s P hcur_le hcur_suf hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26
      hx27 hx28 hx29 hP
  · have hcur_split : cur = encodeKey 1#32 .varint ++ (encodeVarint (v.signExtend 64) ++ restAfter) := by
      rw [hcur_eq]; exact e2a_encodeInt32Field_append_of_ne 1#32 v hv restAfter
    let rest1 := encodeVarint (v.signExtend 64) ++ restAfter
    have hlim1 : limit ≤ rest1.length := by dsimp only [rest1]; rw [List.length_append]; omega
    refine e2ar_chain_key_decode_cl hc x st0 st
      (((s0.sp - 916#64) ↦₃₂ 0#32) ∗ F_state cur.length)
      1#32 .varint (BitVec.ofNat 64 WireType.varint.toNat)
      hcur_split hlim1 hcur_le hcur_suf hlen_bound hFit
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hs0A hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
      (by rw [hP]; sep_ac_rfl) ?_
    intro s1 hrest1_le hrest1_suf hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1
      hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    have hle_cur : rest1.length ≤ cur.length := by
      have hlen_eq := congrArg List.length hcur_split
      dsimp only [rest1] at hlen_eq ⊢
      simp only [e2a_lenPrefixed, List.length_append] at hlen_eq ⊢
      omega
    have hsp1A : s1.spAligned = true := by
      rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc1 ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 792#64)
    wp_steps 4
    refine SepWP.fold (hF_mono hle_cur) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hx1_1]) (by simp only [arm64_norm, hrun1])
    exact e2ar_chain_tag1_call_792_cl hc x st0 st F_state hF_mono v rest1 restAfter rfl
      hrest1_le hrest1_suf hlen_bound hFit hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx1_1])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, hx0_1])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; sep_ac_rfl)
      hdone

/-- Optional Tag 2 (`encodeUint64Field 2#32 v ++ restAfter`) at `+508 -> +508` (`evs = []`). -/
theorem e2ar_chain_tag2_opt_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ)
    (F_state : Nat → SepProp) (hF_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → F_state r1 ⊢ F_state r2)
    (v : BitVec 64) {cur restAfter : Bytes} {limit n c r : Nat}
    (hcur_eq : cur = encodeUint64Field 2#32 v ++ restAfter)
    (hlim_le : limit ≤ restAfter.length)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs n c r))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 508#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      ((s0.sp - 944#64) ↦₆₄ 0#64) ∗
      F_state cur.length ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (sf : State) (P' : SepProp),
      restAfter.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes restAfter →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        ((s0.sp - 944#64) ↦₆₄ v) ∗
        F_state restAfter.length ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  by_cases hv : v = 0#64
  · subst hv
    rw [e2a_encodeUint64Field_of_zero, List.nil_append] at hcur_eq
    subst hcur_eq
    exact hdone s P hcur_le hcur_suf hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26
      hx27 hx28 hx29 hP
  · have hcur_split : cur = encodeKey 2#32 .varint ++ (encodeVarint v ++ restAfter) := by
      rw [hcur_eq]; exact e2a_encodeUint64Field_append_of_ne 2#32 v hv restAfter
    let rest1 := encodeVarint v ++ restAfter
    have hlim1 : limit ≤ rest1.length := by dsimp only [rest1]; rw [List.length_append]; omega
    refine e2ar_chain_key_decode_cl hc x st0 st
      (((s0.sp - 944#64) ↦₆₄ 0#64) ∗ F_state cur.length)
      2#32 .varint (BitVec.ofNat 64 WireType.varint.toNat)
      hcur_split hlim1 hcur_le hcur_suf hlen_bound hFit
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hs0A hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
      (by rw [hP]; sep_ac_rfl) ?_
    intro s1 hrest1_le hrest1_suf hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1
      hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    have hle_cur : rest1.length ≤ cur.length := by
      have hlen_eq := congrArg List.length hcur_split
      dsimp only [rest1] at hlen_eq ⊢
      simp only [e2a_lenPrefixed, List.length_append] at hlen_eq ⊢
      omega
    have hsp1A : s1.spAligned = true := by
      rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc1 ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 872#64)
    wp_steps 6
    refine SepWP.fold (hF_mono hle_cur) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hx1_1]) (by simp only [arm64_norm, hrun1])
    exact e2ar_chain_tag2_call_872_cl hc x st0 st F_state hF_mono v rest1 restAfter rfl
      hrest1_le hrest1_suf hlen_bound hFit hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx1_1])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, hx0_1])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; sep_ac_rfl)
      hdone

/-- Optional Tag 4 (`encodeBytesField 4#32 v ++ restAfter`, `v.length ≤ 32`) at `+508 -> +508`
under `SpqrTightEvs 2 1476 32`. -/
theorem e2ar_chain_tag4_opt_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ)
    (F_state : Nat → SepProp) (hF_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → F_state r1 ⊢ F_state r2)
    (v : Bytes) (hv_le : v.length ≤ 32) {cur restAfter : Bytes} {limit : Nat}
    (hcur_eq : cur = encodeBytesField 4#32 v ++ restAfter)
    (hlim_le : limit ≤ restAfter.length)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs 2 1476 32))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 508#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      vecU8At A.repAlloc (s0.sp - 968#64) 0#64 1#64 [] ∗
      F_state cur.length ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (evs_bm : List AllocEvent) (sf : State) (P' : SepProp),
      SpqrTightEvs 2 1476 32 evs_bm →
      restAfter.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes restAfter →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        vecU8CapOkAt A.repAlloc (s0.sp - 968#64) restAfter.length v ∗
        F_state restAfter.length ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_bm st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  by_cases hv : v = []
  · subst hv
    rw [e2a_encodeBytesField_of_nil, List.nil_append] at hcur_eq
    subst hcur_eq
    have hvec_ok :
        vecU8At A.repAlloc (s0.sp - 968#64) 0#64 1#64 [] ⊢
          vecU8CapOkAt A.repAlloc (s0.sp - 968#64) cur.length [] := by
      unfold vecU8CapOkAt
      exact Entails.sepExists_right 0#64
        (Entails.sepExists_right 1#64 (Entails.pure_right (Or.inl rfl) (Entails.refl _)))
    have hevs0 : SpqrTightEvs 2 1476 32 [] := SpqrTightEvs.nil 2 1476 32
    refine SepWPpIPlaced.mono_pre
      (by rw [hP]; exact sepConj_mono_right (sepConj_mono_left hvec_ok)) ?_
    exact hdone [] s _ hevs0 hcur_le hcur_suf hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24
      hx25 hx26 hx27 hx28 hx29 (by rw [M.stepEvents_nil]; try sep_ac_rfl)
  · have hcur_split : cur = encodeKey 4#32 .lengthDelimited ++ e2a_lenPrefixed v restAfter := by
      rw [hcur_eq]; exact e2a_encodeBytesField_append_of_ne 4#32 hv restAfter
    let rest1 := e2a_lenPrefixed v restAfter
    have hlim1 : limit ≤ rest1.length := by
      dsimp only [rest1]; unfold e2a_lenPrefixed; simp only [List.length_append]; omega
    refine e2ar_chain_key_decode_cl hc x st0 st
      (vecU8At A.repAlloc (s0.sp - 968#64) 0#64 1#64 [] ∗ F_state cur.length)
      4#32 .lengthDelimited (BitVec.ofNat 64 WireType.lengthDelimited.toNat)
      hcur_split hlim1 hcur_le hcur_suf hlen_bound hFit
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hs0A hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
      (by rw [hP]; sep_ac_rfl) ?_
    intro s1 hrest1_le hrest1_suf hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1
      hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    have hle_cur : rest1.length ≤ cur.length := by
      have hlen_eq := congrArg List.length hcur_split
      dsimp only [rest1] at hlen_eq ⊢
      simp only [e2a_lenPrefixed, List.length_append] at hlen_eq ⊢
      omega
    have hsp1A : s1.spAligned = true := by
      rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced]
      at hpc1 ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 824#64)
    wp_steps_sync_pool ((blkPl_325).base + 824#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold (hF_mono hle_cur) (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm, hx1_1]) (by simp only [wp_norm, arm64_norm, hrun1])
    exact e2ar_chain_tag4_call_824_cl hc x st0 st F_state hF_mono v rest1 restAfter rfl hv_le
      hrest1_le hrest1_suf hlen_bound hFit hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, hx1_1])
      (by simp only [wp_norm, arm64_norm, hrun1]) (by simp only [wp_norm, arm64_norm, hsp1])
      (by simp only [wp_norm, arm64_norm, htr1]) (by simp only [wp_norm, arm64_norm, hx0_1])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; sep_ac_rfl)
      hdone

/-- Optional Tag 5 (`encodeUint64Field 5#32 v ++ restAfter`) at `+508 -> +508` (`evs = []`). -/
theorem e2ar_chain_tag5_opt_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ)
    (F_state : Nat → SepProp) (hF_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → F_state r1 ⊢ F_state r2)
    (v : BitVec 64) {cur restAfter : Bytes} {limit n c r : Nat}
    (hcur_eq : cur = encodeUint64Field 5#32 v ++ restAfter)
    (hlim_le : limit ≤ restAfter.length)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs n c r))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 508#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      ((s0.sp - 936#64) ↦₆₄ 0#64) ∗
      F_state cur.length ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (sf : State) (P' : SepProp),
      restAfter.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes restAfter →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        ((s0.sp - 936#64) ↦₆₄ v) ∗
        F_state restAfter.length ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  by_cases hv : v = 0#64
  · subst hv
    rw [e2a_encodeUint64Field_of_zero, List.nil_append] at hcur_eq
    subst hcur_eq
    exact hdone s P hcur_le hcur_suf hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26
      hx27 hx28 hx29 hP
  · have hcur_split : cur = encodeKey 5#32 .varint ++ (encodeVarint v ++ restAfter) := by
      rw [hcur_eq]; exact e2a_encodeUint64Field_append_of_ne 5#32 v hv restAfter
    let rest1 := encodeVarint v ++ restAfter
    have hlim1 : limit ≤ rest1.length := by dsimp only [rest1]; rw [List.length_append]; omega
    refine e2ar_chain_key_decode_cl hc x st0 st
      (((s0.sp - 936#64) ↦₆₄ 0#64) ∗ F_state cur.length)
      5#32 .varint (BitVec.ofNat 64 WireType.varint.toNat)
      hcur_split hlim1 hcur_le hcur_suf hlen_bound hFit
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hs0A hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
      (by rw [hP]; sep_ac_rfl) ?_
    intro s1 hrest1_le hrest1_suf hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1
      hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    have hle_cur : rest1.length ≤ cur.length := by
      have hlen_eq := congrArg List.length hcur_split
      dsimp only [rest1] at hlen_eq ⊢
      simp only [e2a_lenPrefixed, List.length_append] at hlen_eq ⊢
      omega
    have hsp1A : s1.spAligned = true := by
      rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced]
      at hpc1 ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 904#64)
    wp_steps_sync_pool ((blkPl_325).base + 904#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold (hF_mono hle_cur) (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm, hx1_1]) (by simp only [wp_norm, arm64_norm, hrun1])
    exact e2ar_chain_tag5_call_904_cl hc x st0 st F_state hF_mono v rest1 restAfter rfl
      hrest1_le hrest1_suf hlen_bound hFit hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, hx1_1])
      (by simp only [wp_norm, arm64_norm, hrun1]) (by simp only [wp_norm, arm64_norm, hsp1])
      (by simp only [wp_norm, arm64_norm, htr1]) (by simp only [arm64_norm, hx0_1])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; sep_ac_rfl)
      hdone

/-- Optional Tag 6 (`encodeOptMessage ChainParamsPB.encodeRaw 6#32 optCp ++ restAfter`) at
`+508 -> +508` (`evs = []`). -/
theorem e2ar_chain_tag6_opt_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ)
    (F_state : Nat → SepProp) (hF_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → F_state r1 ⊢ F_state r2)
    (optCp : Option ChainParamsPB) {cur restAfter : Bytes} {limit n c r : Nat}
    (hcur_eq : cur = encodeOptMessage ChainParamsPB.encodeRaw 6#32 optCp ++ restAfter)
    (hlim_le : limit ≤ restAfter.length)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs n c r))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 508#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      optChainParamsPBAt (s0.sp - 928#64) none ∗
      F_state cur.length ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (sf : State) (P' : SepProp),
      restAfter.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes restAfter →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        optChainParamsPBAt (s0.sp - 928#64) optCp ∗
        F_state restAfter.length ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  cases optCp with
  | none =>
    simp only [encodeOptMessage, List.nil_append] at hcur_eq
    subst hcur_eq
    exact hdone s P hcur_le hcur_suf hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26
      hx27 hx28 hx29 hP
  | some cp =>
    have hcur_split :
        cur = encodeKey 6#32 .lengthDelimited ++ e2a_lenPrefixed (ChainParamsPB.encodeRaw cp) restAfter := by
      rw [hcur_eq]; exact e2ar_encodeOptMessage_some_append ChainParamsPB.encodeRaw 6#32 cp restAfter
    let rest1 := e2a_lenPrefixed (ChainParamsPB.encodeRaw cp) restAfter
    have hlim1 : limit ≤ rest1.length := by
      dsimp only [rest1]; unfold e2a_lenPrefixed; simp only [List.length_append]; omega
    refine e2ar_chain_key_decode_cl hc x st0 st
      (optChainParamsPBAt (s0.sp - 928#64) none ∗ F_state cur.length)
      6#32 .lengthDelimited (BitVec.ofNat 64 WireType.lengthDelimited.toNat)
      hcur_split hlim1 hcur_le hcur_suf hlen_bound hFit
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hs0A hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
      (by rw [hP]; sep_ac_rfl) ?_
    intro s1 hrest1_le hrest1_suf hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1
      hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    have hle_cur : rest1.length ≤ cur.length := by
      have hlen_eq := congrArg List.length hcur_split
      dsimp only [rest1] at hlen_eq ⊢
      simp only [e2a_lenPrefixed, List.length_append] at hlen_eq ⊢
      omega
    have hsp1A : s1.spAligned = true := by
      rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced]
      at hpc1 ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 752#64)
    wp_steps_sync_pool ((blkPl_325).base + 752#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold (hF_mono hle_cur) (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm, hx1_1]) (by simp only [wp_norm, arm64_norm, hrun1])
    exact e2ar_chain_tag6_call_752_cl hc x st0 st F_state hF_mono cp rest1 restAfter rfl
      hrest1_le hrest1_suf hlen_bound hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, hx1_1])
      (by simp only [wp_norm, arm64_norm, hrun1]) (by simp only [wp_norm, arm64_norm, hsp1])
      (by simp only [wp_norm, arm64_norm, htr1]) (by simp only [wp_norm, arm64_norm, hx0_1])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; sep_ac_rfl)
      hdone

/-! ## 5. Canonical `ChainEpochPB` Push (`0..3` Links) & Outer Tag-2 Entry (`+160 -> +508`) -/

theorem e2ar_chainLinksVecAt_nil (A : RustAlloc) (sp : BitVec 64) :
    ((sp - 992#64) ↦₆₄ 0#64) ∗ ((sp - 984#64) ↦₆₄ 8#64) ∗ ((sp - 976#64) ↦₆₄ 0#64) ⊢
      chainLinksVecAt A (sp - 992#64) [] := by
  unfold chainLinksVecAt chainEpochPBSize vecOf vecAt vecHeader vecBuf
  have ha984 : sp - 992#64 + 8#64 = sp - 984#64 := by bv_omega
  have ha976 : sp - 992#64 + 16#64 = sp - 976#64 := by bv_omega
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 8#64 ?_)
  rw [ha984, ha976]
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ↓reduceIte]
  exact Entails.trans (Entails.of_eq (sepConj_emp _).symm)
    (sepConj_mono_right (Entails.pure_right (by decide) (Entails.refl emp)))

theorem e2ar_chainLinksVecAt_fold4 (A : RustAlloc) (sp ptr : BitVec 64)
    (xs : List ChainEpochPB) (hle : xs.length ≤ 4) (hptr : ptr ≠ 0#64) :
    ((sp - 992#64) ↦₆₄ 4#64) ∗ ((sp - 984#64) ↦₆₄ ptr) ∗
      ((sp - 976#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
      A.live ptr (4 * 112) 8 ∗
      arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ∗
      memRegion (ptr + BitVec.ofNat 64 (xs.length * 112)) ((4 - xs.length) * 112) ⊢
      chainLinksVecAt A (sp - 992#64) xs := by
  unfold chainLinksVecAt chainEpochPBSize vecOf vecAt vecHeader vecBuf
  have ha984 : sp - 992#64 + 8#64 = sp - 984#64 := by bv_omega
  have ha976 : sp - 992#64 + 16#64 = sp - 976#64 := by bv_omega
  have hcap0 : (4#64 : BitVec 64) ≠ 0 := by decide
  have hcap_nat : (4#64 : BitVec 64).toNat = 4 := rfl
  refine Entails.sepExists_right 4#64 (Entails.sepExists_right ptr ?_)
  rw [ha984, ha976]
  simp only [hcap0, hcap_nat, ↓reduceIte]
  have hpure :
      (((sp - 992#64) ↦₆₄ 4#64) ∗ ((sp - 984#64) ↦₆₄ ptr) ∗
        ((sp - 976#64) ↦₆₄ BitVec.ofNat 64 xs.length)) ∗
        (⌜xs.length ≤ 4 ∧ 4 * 112 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (A.live ptr (4 * 112) 8 ∗
            arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ∗
            memRegion (ptr + BitVec.ofNat 64 (xs.length * 112)) ((4 - xs.length) * 112))) =
      ⌜xs.length ≤ 4 ∧ 4 * 112 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (((sp - 992#64) ↦₆₄ 4#64) ∗ ((sp - 984#64) ↦₆₄ ptr) ∗
          ((sp - 976#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
          A.live ptr (4 * 112) 8 ∗
          arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ∗
          memRegion (ptr + BitVec.ofNat 64 (xs.length * 112)) ((4 - xs.length) * 112)) := by
    sep_ac_rfl
  rw [hpure]
  apply Entails.pure_right ⟨hle, by decide, hptr⟩
  exact Entails.of_eq (by sep_ac_rfl)

private theorem e2ar_snoc_arrayAt_112 (A : RustAlloc) (ptr : BitVec 64)
    (xs : List ChainEpochPB) (ep : ChainEpochPB) (q : Quads14) :
    arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ∗
      quads14At (ptr + BitVec.ofNat 64 (xs.length * 112)) q ∗
      chainEpochPBHeap A q ep ⊢
      arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr (xs ++ [ep]) := by
  have hep_at := quads14_entails_chainEpochPBAt A (ptr + BitVec.ofNat 64 (xs.length * 112)) q ep
  have harr := e2ar_arrayAt_112_append_singleton (fun ep addr => chainEpochPBAt A addr ep) ptr xs ep
  rw [← harr]
  have hgroup :
      arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ∗
        quads14At (ptr + BitVec.ofNat 64 (xs.length * 112)) q ∗
        chainEpochPBHeap A q ep =
      arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ∗
        (quads14At (ptr + BitVec.ofNat 64 (xs.length * 112)) q ∗
          chainEpochPBHeap A q ep) := by sep_ac_rfl
  rw [hgroup]
  exact sepConj_mono_right hep_at

private theorem e2ar_empty_bytes_to_arrayAt_chainEpochPB (A : RustAlloc) (p' : BitVec 64) :
    (p' ↦ₛ ([] : List (BitVec 8))) ⊢
      arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 p' [] := by
  have hof := (relocArrayAtChainEpochPB A []).2.of_bytes p' [] rfl
  simpa [relocArrayAtChainEpochPB] using hof

private theorem e2ar_len_lt4_beq_false {n : Nat} (hlt : n < 4) :
    (BitVec.ofNat 64 n == 4#64) = false ∧
    (BitVec.ofNat 64 n - 4#64 == 0#64) = false ∧
    (!decide ((BitVec.ofNat 64 n - 4#64 == 0#64) = true)) = true := by
  match n, hlt with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide

/-- Single Tag-3 `ChainEpochPB` decode + merge (`+508 -> +624`, `SpqrTightEvs 6 183420 79236`). -/
theorem e2ar_chain_epoch_tag3_merge_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (hEpochDir : E2ar2EpochDirCanonicalOk A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (V_state : Nat → SepProp) (hV_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → V_state r1 ⊢ V_state r2)
    (ep : ChainEpochPB) (hep : e2ar2_ValidChainEpochPB ep)
    {cur restAfter : Bytes} {limit : Nat}
    (hcur_eq : cur = encodeKey 3#32 .lengthDelimited ++
      e2a_lenPrefixed (ChainEpochPB.encodeRaw ep) restAfter)
    (hlim_le : limit ≤ restAfter.length)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs 6 183420 79236))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hpost : post = decodeStatePostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 508#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      V_state cur.length ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (evs_em : List AllocEvent) (sf : State) (P' : SepProp),
      SpqrTightEvs 6 183420 79236 evs_em →
      restAfter.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes restAfter →
      sf.pc = decodeStatePlacedEntry + 624#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        V_state restAfter.length ∗
        chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) restAfter.length ep ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_em st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  let rest1 := e2a_lenPrefixed (ChainEpochPB.encodeRaw ep) restAfter
  have hlim1 : limit ≤ rest1.length := by
    dsimp only [rest1]; unfold e2a_lenPrefixed; simp only [List.length_append]; omega
  refine e2ar_chain_key_decode_cl hc x st0 st
    (((s0.sp - 688#64) ↦₆₄ w0) ∗ V_state cur.length ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304)
    3#32 .lengthDelimited (BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    hcur_eq hlim1 hcur_le hcur_suf hlen_bound hFit
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    hs0A hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hrest1_le hrest1_suf hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1
    hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  have hle_cur : rest1.length ≤ cur.length := by
    have hlen_eq := congrArg List.length hcur_eq
    dsimp only [rest1] at hlen_eq ⊢
    simp only [e2a_lenPrefixed, List.length_append] at hlen_eq ⊢
    omega
  have hx0_2 : s1.readReg64 .x0 = 2#64 := hx0_1
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc1 ⊢
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 592#64)
  wp_steps 8
  apply SepWP.done (by simp only [wp_norm, arm64_norm, hx1_1])
    (by simp only [wp_norm, arm64_norm, hrun1])
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 600#64)
  wp_steps 2
  refine SepWP.fold (hV_mono hle_cur) (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm, hx0_2])
    (by simp only [wp_norm, arm64_norm, hrun1])
  exact e2ar2_epoch_merge_tight_536f4 (v20 := BitVec.ofNat 64 limit)
    hc hEpochDir x st0 st w0 V_state hV_mono ep hep rest1 restAfter rfl
    hrest1_le hrest1_suf hlen_bound hFit s0 _ _ R post hpost hs0A
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, hx0_2])
    (by simp only [wp_norm, arm64_norm, hrun1]) (by simp only [wp_norm, arm64_norm, hsp1])
    (by simp only [wp_norm, arm64_norm, htr1])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; sep_ac_rfl)
    hdone

/-- 112-byte Q-register copy at `+640 -> +508` (`cap = 4#64`, `xs.length < 4`, `evs = []`),
restoring `.x27 = 8#64`. -/
theorem e2ar_chain_push_copy_640_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (x : DecodeStateGhost) (st0 st : M.σ)
    (ptr : BitVec 64) (xs : List ChainEpochPB) (ep : ChainEpochPB)
    (restAfter : Bytes) (limit : Nat) (F_rest : SepProp)
    (hlt : xs.length < 4) (hptr : ptr ≠ 0#64)
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 640#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 xs.length)
    (hx28 : s.readReg64 .x28 = 1#64) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
      ((s0.sp - 992#64) ↦₆₄ 4#64) ∗ ((s0.sp - 984#64) ↦₆₄ ptr) ∗
      ((s0.sp - 976#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
      A.repAlloc.live ptr (4 * 112) 8 ∗
      arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 ptr xs ∗
      memRegion (ptr + BitVec.ofNat 64 (xs.length * 112)) ((4 - xs.length) * 112) ∗
      chainEpochPBAt A.repAlloc (s0.sp - 688#64) ep ∗
      memRegion (s0.sp - 576#64) 240 ∗
      F_rest ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (w0' : BitVec 64) (sf : State) (P' : SepProp),
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        ((s0.sp - 992#64) ↦₆₄ 4#64) ∗ ((s0.sp - 984#64) ↦₆₄ ptr) ∗
        ((s0.sp - 976#64) ↦₆₄ BitVec.ofNat 64 (xs ++ [ep]).length) ∗
        A.repAlloc.live ptr (4 * 112) 8 ∗
        arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 ptr (xs ++ [ep]) ∗
        memRegion (ptr + BitVec.ofNat 64 ((xs ++ [ep]).length * 112))
          ((4 - (xs ++ [ep]).length) * 112) ∗
        F_rest ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hlen_app : (xs ++ [ep]).length = xs.length + 1 := by simp
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced] at hpc ⊢
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 508#64)
  refine SepWP.fold (chainEpochPBAt_entails_quads14 A.repAlloc (s0.sp - 688#64) ep)
    (by sep_focus) ?_
  refine SepWP.fold (e2ar_memRegion_rem_split_112 ptr xs.length 4 hlt (by decide))
    (by sep_focus) ?_
  wp_pull_exists
  rename_i q_src q_dst
  rcases q_src with ⟨⟨s0_0, s0_1, s0_2, s0_3, s0_4, s0_5, s0_6⟩,
                     ⟨s1_0, s1_1, s1_2, s1_3, s1_4, s1_5, s1_6⟩⟩
  rcases q_dst with ⟨⟨d0_0, d0_1, d0_2, d0_3, d0_4, d0_5, d0_6⟩,
                     ⟨d1_0, d1_1, d1_2, d1_3, d1_4, d1_5, d1_6⟩⟩
  dsimp only [quads14At, quads7At]
  wp_steps_sync_pool ((blkPl_325).base + 508#64)
  try simp only [State.setMem_setMem]
  have hsnoc := e2ar_snoc_arrayAt_112 A.repAlloc ptr xs ep
    ((s0_0, s0_1, s0_2, s0_3, s0_4, s0_5, s0_6), (s1_0, s1_1, s1_2, s1_3, s1_4, s1_5, s1_6))
  dsimp only [quads14At, quads7At] at hsnoc
  refine SepWP.fold hsnoc (by sep_focus) ?_
  have hrestore := e2ar_quads14At_sp_688_restore s0.sp
    ((s0_0, s0_1, s0_2, s0_3, s0_4, s0_5, s0_6), (s1_0, s1_1, s1_2, s1_3, s1_4, s1_5, s1_6))
  dsimp only [quads14At, quads7At, Quads14.head] at hrestore
  refine SepWP.fold hrestore (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  exact hdone s0_0 _ _
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19]) (by simp only [wp_norm, arm64_norm, hx20])
    (by simp only [wp_norm, arm64_norm, hx21]) (by simp only [wp_norm, arm64_norm, hx22])
    (by simp only [wp_norm, arm64_norm, hx23]) (by simp only [wp_norm, arm64_norm, hx24])
    (by simp only [wp_norm, arm64_norm, hx25]) (by simp only [wp_norm, arm64_norm, hx26])
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hx28])
    (by simp only [wp_norm, arm64_norm, hx29])
    (by rw [hlen_app]; dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; sep_ac_rfl)

/-- First `Vec<ChainEpochPB>::push` from `cap = 0#64, ptr = 8#64, xs = []` at `+624 -> +508`
(`SpqrTightEvs 1 9789 448`). -/
theorem e2ar_chain_push_first_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ)
    (ep : ChainEpochPB) (restAfter : Bytes) (limit : Nat) (F_rest : SepProp)
    (hFit : FitsEnv M lim st (SpqrTightEvs 1 9789 448))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 624#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx28 : s.readReg64 .x28 = 1#64) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
      ((s0.sp - 992#64) ↦₆₄ 0#64) ∗ ((s0.sp - 984#64) ↦₆₄ 8#64) ∗
      ((s0.sp - 976#64) ↦₆₄ 0#64) ∗
      F_rest ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) restAfter.length ep ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (w0' p' : BitVec 64) (evs_grow : List AllocEvent) (sf : State) (P' : SepProp),
      p' ≠ 0#64 → SpqrTightEvs 1 9789 448 evs_grow →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        ((s0.sp - 992#64) ↦₆₄ 4#64) ∗ ((s0.sp - 984#64) ↦₆₄ p') ∗
        ((s0.sp - 976#64) ↦₆₄ 1#64) ∗
        A.repAlloc.live p' (4 * 112) 8 ∗
        arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 p' [ep] ∗
        memRegion (p' + BitVec.ofNat 64 (1 * 112)) ((4 - 1) * 112) ∗
        F_rest ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_grow st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hgrow_call := hc.growOneChainEpoch
  have hfits_grow : FitsEnv M lim st (GrowOneStrideEnv 0#64 112 8) :=
    hFit.mono fun _ h => e2a_growOneChainEpoch_zero_tight h
  have hbeq : ((0#64 : BitVec 64) - 0#64 == 0#64) = true := rfl
  have hbne : (!decide (((0#64 : BitVec 64) - 0#64 == 0#64) = true)) = false := rfl
  have hx22_30 : s0.sp - 1040#64 + 48#64 = s0.sp - 992#64 := by bv_omega
  have ha984 : s0.sp - 992#64 + 8#64 = s0.sp - 984#64 := by bv_omega
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced]
    at hpc hgrow_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1200#64)
  refine SepWP.fold (chainEpochPBCapOkAt_entails_chainEpochPBAt A.repAlloc (s0.sp - 688#64)
    restAfter.length ep) (by sep_focus) ?_
  wp_steps 4
  apply SepWP.done (by simp only [arm64_norm, hbeq, hbne]) (by simp only [arm64_norm, hrun])
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 356)
  wp_steps 2
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  refine SepWPpIPlaced.call_growOneChainEpoch_cl hgrow_call
    (s0.sp - 992#64) 0#64 8#64 [] st
    (ret_pc := (blkPl_325).base + 1208#64)
    (hpc := by simp only [arm64_norm])
    (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx22, hx22_30])
    (hlen := rfl) (hptr := by decide) (hbound := by decide)
    (hfits := hfits_grow)
    (hP := by rw [ha984]; simp only [↓reduceIte, emp_sepConj]; pool_reg_norm; sep_focus) ?_
  intro s1 p' evs_grow hptr' _ hevs_grow hpc1 hrun1 hsp1 htr1 hcs1
  have hevs_tight : SpqrTightEvs 1 9789 448 evs_grow :=
    e2a_growOneChainEpoch_zero_tight hevs_grow
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, _⟩
  simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
  simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [ha984]
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 640#64)
  refine SepWP.fold (e2ar_empty_bytes_to_arrayAt_chainEpochPB A.repAlloc p') (by sep_focus) ?_
  wp_steps 1
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
  exact e2ar_chain_push_copy_640_cl x st0 (M.stepEvents evs_grow st) p' [] ep restAfter limit F_rest
    (by decide) hptr' hs0A
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
    (by simp only [arm64_norm, htr1])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, List.length_nil, BitVec.ofNat_eq_ofNat, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by
      change _ = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        ((s0.sp - 992#64) ↦₆₄ 4#64) ∗ ((s0.sp - 984#64) ↦₆₄ p') ∗
        ((s0.sp - 976#64) ↦₆₄ 0#64) ∗
        A.repAlloc.live p' (4 * 112) 8 ∗
        arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 p' [] ∗
        memRegion (p' + 0#64) ((4 - 0) * 112) ∗
        chainEpochPBAt A.repAlloc (s0.sp - 688#64) ep ∗
        memRegion (s0.sp - 576#64) 240 ∗ F_rest ∗ _
      dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; sep_ac_rfl)
    (fun w0' sf P' => hdone w0' p' evs_grow sf P' hptr' hevs_tight)

/-- Subsequent `Vec<ChainEpochPB>::push` at `cap = 4#64, xs.length < 4` (`+624 -> +508`,
`evs = []`). -/
theorem e2ar_chain_push_lt4_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (x : DecodeStateGhost) (st0 st : M.σ)
    (ptr : BitVec 64) (xs : List ChainEpochPB) (ep : ChainEpochPB)
    (restAfter : Bytes) (limit : Nat) (F_rest : SepProp)
    (hlt : xs.length < 4) (hptr : ptr ≠ 0#64)
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 624#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx28 : s.readReg64 .x28 = 1#64) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
      ((s0.sp - 992#64) ↦₆₄ 4#64) ∗ ((s0.sp - 984#64) ↦₆₄ ptr) ∗
      ((s0.sp - 976#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
      A.repAlloc.live ptr (4 * 112) 8 ∗
      arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 ptr xs ∗
      memRegion (ptr + BitVec.ofNat 64 (xs.length * 112)) ((4 - xs.length) * 112) ∗
      F_rest ∗
      chainEpochPBCapOkAt A.repAlloc (s0.sp - 688#64) restAfter.length ep ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (w0' : BitVec 64) (sf : State) (P' : SepProp),
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        ((s0.sp - 992#64) ↦₆₄ 4#64) ∗ ((s0.sp - 984#64) ↦₆₄ ptr) ∗
        ((s0.sp - 976#64) ↦₆₄ BitVec.ofNat 64 (xs ++ [ep]).length) ∗
        A.repAlloc.live ptr (4 * 112) 8 ∗
        arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 ptr (xs ++ [ep]) ∗
        memRegion (ptr + BitVec.ofNat 64 ((xs ++ [ep]).length * 112))
          ((4 - (xs ++ [ep]).length) * 112) ∗
        F_rest ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have ⟨hbeq4, hbeq, hbne⟩ := e2ar_len_lt4_beq_false hlt
  subst hP
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 640#64)
  refine SepWP.fold (chainEpochPBCapOkAt_entails_chainEpochPBAt A.repAlloc (s0.sp - 688#64)
    restAfter.length ep) (by sep_focus) ?_
  wp_steps 4
  apply SepWP.done (by simp only [arm64_norm, hbeq4, hbeq, hbne]) (by simp only [arm64_norm, hrun])
  exact e2ar_chain_push_copy_640_cl x st0 st ptr xs ep restAfter limit F_rest hlt hptr hs0A
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hbeq4, hbeq, hbne])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
    (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
    (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
    (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hx28])
    (by simp only [arm64_norm, hx29])
    (by dsimp only [decodeStateLoopCommonPlaced]; pool_reg_norm; sep_ac_rfl)
    hdone

private theorem e2ar_fitsEnv_tight_split_le {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {n₁ n₂ n c₁ c₂ c r₁ r₂ r : Nat} {evs₁ : List AllocEvent}
    (h₁ : SpqrTightEvs n₁ c₁ r₁ evs₁)
    (hn : n₁ + n₂ ≤ n) (hc : c₁ + c₂ ≤ c) (hr : max r₁ r₂ ≤ r)
    (hFit : FitsEnv M lim st (SpqrTightEvs n c r)) :
    FitsEnv M lim (M.stepEvents evs₁ st) (SpqrTightEvs n₂ c₂ r₂) :=
  e2a_fitsEnv_tight_split h₁ (hFit.mono fun _ h => h.mono hn hc hr)

/-- Combined 1st Tag-3 step (`0 -> 1` link: `merge` + `push_first`, `SpqrTightEvs 7 193209 79236`). -/
private theorem e2ar_chain_tag3_step_first_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (hEpochDir : E2ar2EpochDirCanonicalOk A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (F_state : Nat → SepProp) (hF_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → F_state r1 ⊢ F_state r2)
    (ep : ChainEpochPB) (hep : e2ar2_ValidChainEpochPB ep)
    {cur restAfter : Bytes} {limit : Nat}
    (hcur_eq : cur = encodeKey 3#32 .lengthDelimited ++
      e2a_lenPrefixed (ChainEpochPB.encodeRaw ep) restAfter)
    (hlim_le : limit ≤ restAfter.length)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs 7 193209 79236))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hpost : post = decodeStatePostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 508#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      ((s0.sp - 992#64) ↦₆₄ 0#64) ∗ ((s0.sp - 984#64) ↦₆₄ 8#64) ∗
      ((s0.sp - 976#64) ↦₆₄ 0#64) ∗
      F_state cur.length ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (w0' p' : BitVec 64) (evs_step : List AllocEvent) (sf : State) (P' : SepProp),
      p' ≠ 0#64 → SpqrTightEvs 7 193209 79236 evs_step →
      restAfter.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes restAfter →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        ((s0.sp - 992#64) ↦₆₄ 4#64) ∗ ((s0.sp - 984#64) ↦₆₄ p') ∗
        ((s0.sp - 976#64) ↦₆₄ 1#64) ∗
        A.repAlloc.live p' (4 * 112) 8 ∗
        arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 p' [ep] ∗
        memRegion (p' + BitVec.ofNat 64 (1 * 112)) ((4 - 1) * 112) ∗
        F_state restAfter.length ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_step st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  let V_state : Nat → SepProp := fun r =>
    ((s0.sp - 992#64) ↦₆₄ 0#64) ∗ ((s0.sp - 984#64) ↦₆₄ 8#64) ∗
      ((s0.sp - 976#64) ↦₆₄ 0#64) ∗ F_state r
  have hV_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → V_state r1 ⊢ V_state r2 := fun hle =>
    sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (hF_mono hle)))
  have hFit_em : FitsEnv M lim st (SpqrTightEvs 6 183420 79236) :=
    hFit.mono fun _ h => h.mono (by decide) (by decide) (by decide)
  refine e2ar_chain_epoch_tag3_merge_cl hc hEpochDir x st0 st w0 V_state hV_mono ep hep
    hcur_eq hlim_le hcur_le hcur_suf hlen_bound hFit_em hpost hs0A
    hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    (by rw [hP]; dsimp only [V_state]; sep_ac_rfl) ?_
  intro evs_em s1 P1 hevs_em hafter_le hafter_suf hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1
    hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 hP1
  have hFit_grow : FitsEnv M lim (M.stepEvents evs_em st) (SpqrTightEvs 1 9789 448) :=
    e2ar_fitsEnv_tight_split_le hevs_em (by decide) (by decide) (by decide) hFit
  refine e2ar_chain_push_first_cl hc x st0 (M.stepEvents evs_em st) ep restAfter limit
    (F_state restAfter.length) hFit_grow hs0A
    hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1
    (by rw [hP1]; dsimp only [V_state]; sep_ac_rfl) ?_
  intro w0' p' evs_grow sf P' hptr' hevs_grow hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f
    hx22_f hx23_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hP'
  have hevs_step : SpqrTightEvs 7 193209 79236 (evs_em ++ evs_grow) :=
    (hevs_em.append hevs_grow).mono (by decide) (by decide) (by decide)
  exact hdone w0' p' (evs_em ++ evs_grow) sf P' hptr' hevs_step hafter_le hafter_suf
    hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f hx23_f hx24_f hx25_f hx26_f
    hx27_f hx28_f hx29_f (by rw [hP', M.stepEvents_append])

/-- Combined subsequent Tag-3 step (`xs -> xs ++ [ep]` at `cap = 4#64, xs.length < 4`,
`SpqrTightEvs 6 183420 79236`). -/
private theorem e2ar_chain_tag3_step_more_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (hEpochDir : E2ar2EpochDirCanonicalOk A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 ptr : BitVec 64)
    (xs : List ChainEpochPB) (hlt : xs.length < 4) (hptr : ptr ≠ 0#64)
    (F_state : Nat → SepProp) (hF_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → F_state r1 ⊢ F_state r2)
    (ep : ChainEpochPB) (hep : e2ar2_ValidChainEpochPB ep)
    {cur restAfter : Bytes} {limit : Nat}
    (hcur_eq : cur = encodeKey 3#32 .lengthDelimited ++
      e2a_lenPrefixed (ChainEpochPB.encodeRaw ep) restAfter)
    (hlim_le : limit ≤ restAfter.length)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs 6 183420 79236))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hpost : post = decodeStatePostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 508#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      ((s0.sp - 992#64) ↦₆₄ 4#64) ∗ ((s0.sp - 984#64) ↦₆₄ ptr) ∗
      ((s0.sp - 976#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
      A.repAlloc.live ptr (4 * 112) 8 ∗
      arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 ptr xs ∗
      memRegion (ptr + BitVec.ofNat 64 (xs.length * 112)) ((4 - xs.length) * 112) ∗
      F_state cur.length ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (w0' : BitVec 64) (evs_em : List AllocEvent) (sf : State) (P' : SepProp),
      SpqrTightEvs 6 183420 79236 evs_em →
      restAfter.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes restAfter →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        ((s0.sp - 992#64) ↦₆₄ 4#64) ∗ ((s0.sp - 984#64) ↦₆₄ ptr) ∗
        ((s0.sp - 976#64) ↦₆₄ BitVec.ofNat 64 (xs ++ [ep]).length) ∗
        A.repAlloc.live ptr (4 * 112) 8 ∗
        arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 ptr (xs ++ [ep]) ∗
        memRegion (ptr + BitVec.ofNat 64 ((xs ++ [ep]).length * 112))
          ((4 - (xs ++ [ep]).length) * 112) ∗
        F_state restAfter.length ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_em st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  let V_state : Nat → SepProp := fun r =>
    ((s0.sp - 992#64) ↦₆₄ 4#64) ∗ ((s0.sp - 984#64) ↦₆₄ ptr) ∗
      ((s0.sp - 976#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
      A.repAlloc.live ptr (4 * 112) 8 ∗
      arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 ptr xs ∗
      memRegion (ptr + BitVec.ofNat 64 (xs.length * 112)) ((4 - xs.length) * 112) ∗
      F_state r
  have hV_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → V_state r1 ⊢ V_state r2 := fun hle =>
    sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (hF_mono hle))))))
  refine e2ar_chain_epoch_tag3_merge_cl hc hEpochDir x st0 st w0 V_state hV_mono ep hep
    hcur_eq hlim_le hcur_le hcur_suf hlen_bound hFit hpost hs0A
    hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    (by rw [hP]; dsimp only [V_state]; sep_ac_rfl) ?_
  intro evs_em s1 P1 hevs_em hafter_le hafter_suf hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1
    hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 hP1
  exact e2ar_chain_push_lt4_cl x st0 (M.stepEvents evs_em st) ptr xs ep restAfter limit
    (F_state restAfter.length) hlt hptr hs0A
    hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1
    (by rw [hP1]; dsimp only [V_state]; sep_ac_rfl)
    (fun w0' sf P' => hdone w0' evs_em sf P' hevs_em hafter_le hafter_suf)

/-- Canonical `0..3` repeated `ChainEpochPB` links (`encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 links`)
at `+508 -> +508` under `SpqrTightEvs 19 560049 79236`. -/
theorem e2ar_chain_tag3_links_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (hEpochDir : E2ar2EpochDirCanonicalOk A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (F_state : Nat → SepProp) (hF_mono : ∀ {r1 r2 : Nat}, r2 ≤ r1 → F_state r1 ⊢ F_state r2)
    (links : List ChainEpochPB)
    (hlen_le : links.length ≤ 3)
    (hall_ep : ∀ ep ∈ links, e2ar2_ValidChainEpochPB ep)
    {cur restAfter : Bytes} {limit : Nat}
    (hcur_eq : cur = encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 links ++ restAfter)
    (hlim_le : limit ≤ restAfter.length)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs 19 560049 79236))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hpost : post = decodeStatePostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 508#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      ((s0.sp - 992#64) ↦₆₄ 0#64) ∗ ((s0.sp - 984#64) ↦₆₄ 8#64) ∗
      ((s0.sp - 976#64) ↦₆₄ 0#64) ∗
      F_state cur.length ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (w0' : BitVec 64) (evs3 : List AllocEvent) (sf : State) (P' : SepProp),
      SpqrTightEvs 19 560049 79236 evs3 →
      restAfter.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes restAfter →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes restAfter ∗
        chainLinksVecAt A.repAlloc (s0.sp - 992#64) links ∗
        F_state restAfter.length ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs3 st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  match links with
  | [] =>
    simp only [encodeRepeatedMessage, List.nil_append] at hcur_eq
    subst hcur_eq
    subst hP
    apply SepWPpIPlaced.of_sepWP (mid := decodeStatePlacedEntry + 508#64)
    refine SepWP.fold (e2ar_chainLinksVecAt_nil A.repAlloc s0.sp) (by sep_focus) ?_
    apply SepWP.done hpc hrun
    exact hdone w0 [] s _ (SpqrTightEvs.nil 19 560049 79236) hcur_le hcur_suf
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
      (by rw [M.stepEvents_nil]; sep_ac_rfl)
  | [ep1] =>
    have hep1 : e2ar2_ValidChainEpochPB ep1 := hall_ep ep1 (by simp)
    have hcur1 : cur = encodeKey 3#32 .lengthDelimited ++
        e2a_lenPrefixed (ChainEpochPB.encodeRaw ep1) restAfter := by
      rw [hcur_eq, e2ar_encodeRepeatedMessage_cons_append]
      rfl
    have hFit1 : FitsEnv M lim st (SpqrTightEvs 7 193209 79236) :=
      hFit.mono fun _ h => h.mono (by decide) (by decide) (by decide)
    refine e2ar_chain_tag3_step_first_cl hc hEpochDir x st0 st w0 F_state hF_mono ep1 hep1
      hcur1 hlim_le hcur_le hcur_suf hlen_bound hFit1 hpost hs0A
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP ?_
    intro w0_1 p' evs1 s1 P1 hptr' hevs1 hafter_le hafter_suf
      hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1
      hx27_1 hx28_1 hx29_1 hP1
    subst hP1
    apply SepWPpIPlaced.of_sepWP (mid := decodeStatePlacedEntry + 508#64)
    refine SepWP.fold (e2ar_chainLinksVecAt_fold4 A.repAlloc s0.sp p' [ep1] (by simp) hptr')
      (by sep_focus) ?_
    apply SepWP.done hpc1 hrun1
    exact hdone w0_1 evs1 s1 _
      (hevs1.mono (by decide) (by decide) (by decide)) hafter_le hafter_suf
      hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1
      hx27_1 hx28_1 hx29_1 (by sep_ac_rfl)
  | [ep1, ep2] =>
    have hep1 : e2ar2_ValidChainEpochPB ep1 := hall_ep ep1 (by simp)
    have hep2 : e2ar2_ValidChainEpochPB ep2 := hall_ep ep2 (by simp)
    let rem1 := encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 [ep2] ++ restAfter
    have hcur1 : cur = encodeKey 3#32 .lengthDelimited ++
        e2a_lenPrefixed (ChainEpochPB.encodeRaw ep1) rem1 := by
      rw [hcur_eq]; exact e2ar_encodeRepeatedMessage_cons_append ChainEpochPB.encodeRaw 3#32 ep1 [ep2] restAfter
    have hlim1 : limit ≤ rem1.length := by dsimp only [rem1]; rw [List.length_append]; omega
    have hFit1 : FitsEnv M lim st (SpqrTightEvs 7 193209 79236) :=
      hFit.mono fun _ h => h.mono (by decide) (by decide) (by decide)
    refine e2ar_chain_tag3_step_first_cl hc hEpochDir x st0 st w0 F_state hF_mono ep1 hep1
      hcur1 hlim1 hcur_le hcur_suf hlen_bound hFit1 hpost hs0A
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP ?_
    intro w0_1 p' evs1 s1 P1 hptr' hevs1 hrem1_le hrem1_suf
      hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1
      hx27_1 hx28_1 hx29_1 hP1
    have hrem1_eq : rem1 = encodeKey 3#32 .lengthDelimited ++
        e2a_lenPrefixed (ChainEpochPB.encodeRaw ep2) restAfter := by
      dsimp only [rem1]
      rw [e2ar_encodeRepeatedMessage_cons_append]
      rfl
    have hFit2 : FitsEnv M lim (M.stepEvents evs1 st) (SpqrTightEvs 6 183420 79236) :=
      e2ar_fitsEnv_tight_split_le hevs1 (by decide) (by decide) (by decide) hFit
    refine e2ar_chain_tag3_step_more_cl hc hEpochDir x st0 (M.stepEvents evs1 st) w0_1 p'
      [ep1] (by simp) hptr' F_state hF_mono ep2 hep2
      hrem1_eq hlim_le hrem1_le hrem1_suf hlen_bound hFit2 hpost hs0A
      hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1
      hx27_1 hx28_1 hx29_1 hP1 ?_
    intro w0_2 evs2 s2 P2 hevs2 hafter_le hafter_suf
      hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2
      hx27_2 hx28_2 hx29_2 hP2
    subst hP2
    apply SepWPpIPlaced.of_sepWP (mid := decodeStatePlacedEntry + 508#64)
    refine SepWP.fold (e2ar_chainLinksVecAt_fold4 A.repAlloc s0.sp p' [ep1, ep2] (by simp) hptr')
      (by sep_focus) ?_
    apply SepWP.done hpc2 hrun2
    exact hdone w0_2 (evs1 ++ evs2) s2 _
      ((hevs1.append hevs2).mono (by decide) (by decide) (by decide)) hafter_le hafter_suf
      hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2
      hx27_2 hx28_2 hx29_2 (by rw [M.stepEvents_append]; sep_ac_rfl)
  | [ep1, ep2, ep3] =>
    have hep1 : e2ar2_ValidChainEpochPB ep1 := hall_ep ep1 (by simp)
    have hep2 : e2ar2_ValidChainEpochPB ep2 := hall_ep ep2 (by simp)
    have hep3 : e2ar2_ValidChainEpochPB ep3 := hall_ep ep3 (by simp)
    let rem1 := encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 [ep2, ep3] ++ restAfter
    let rem2 := encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 [ep3] ++ restAfter
    have hcur1 : cur = encodeKey 3#32 .lengthDelimited ++
        e2a_lenPrefixed (ChainEpochPB.encodeRaw ep1) rem1 := by
      rw [hcur_eq]
      exact e2ar_encodeRepeatedMessage_cons_append ChainEpochPB.encodeRaw 3#32 ep1 [ep2, ep3] restAfter
    have hlim1 : limit ≤ rem1.length := by dsimp only [rem1]; rw [List.length_append]; omega
    have hlim2 : limit ≤ rem2.length := by dsimp only [rem2]; rw [List.length_append]; omega
    have hFit1 : FitsEnv M lim st (SpqrTightEvs 7 193209 79236) :=
      hFit.mono fun _ h => h.mono (by decide) (by decide) (by decide)
    refine e2ar_chain_tag3_step_first_cl hc hEpochDir x st0 st w0 F_state hF_mono ep1 hep1
      hcur1 hlim1 hcur_le hcur_suf hlen_bound hFit1 hpost hs0A
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP ?_
    intro w0_1 p' evs1 s1 P1 hptr' hevs1 hrem1_le hrem1_suf
      hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1
      hx27_1 hx28_1 hx29_1 hP1
    have hrem1_eq : rem1 = encodeKey 3#32 .lengthDelimited ++
        e2a_lenPrefixed (ChainEpochPB.encodeRaw ep2) rem2 := by
      dsimp only [rem1, rem2]
      exact e2ar_encodeRepeatedMessage_cons_append ChainEpochPB.encodeRaw 3#32 ep2 [ep3] restAfter
    have hFit_rem : FitsEnv M lim (M.stepEvents evs1 st) (SpqrTightEvs 12 366840 79236) :=
      e2ar_fitsEnv_tight_split_le hevs1 (by decide) (by decide) (by decide) hFit
    have hFit2 : FitsEnv M lim (M.stepEvents evs1 st) (SpqrTightEvs 6 183420 79236) :=
      hFit_rem.mono fun _ h => h.mono (by decide) (by decide) (by decide)
    refine e2ar_chain_tag3_step_more_cl hc hEpochDir x st0 (M.stepEvents evs1 st) w0_1 p'
      [ep1] (by simp) hptr' F_state hF_mono ep2 hep2
      hrem1_eq hlim2 hrem1_le hrem1_suf hlen_bound hFit2 hpost hs0A
      hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1
      hx27_1 hx28_1 hx29_1 hP1 ?_
    intro w0_2 evs2 s2 P2 hevs2 hrem2_le hrem2_suf
      hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2
      hx27_2 hx28_2 hx29_2 hP2
    have hrem2_eq : rem2 = encodeKey 3#32 .lengthDelimited ++
        e2a_lenPrefixed (ChainEpochPB.encodeRaw ep3) restAfter := by
      dsimp only [rem2]
      rw [e2ar_encodeRepeatedMessage_cons_append]
      rfl
    have hFit3 : FitsEnv M lim (M.stepEvents evs2 (M.stepEvents evs1 st))
        (SpqrTightEvs 6 183420 79236) :=
      e2ar_fitsEnv_tight_split_le hevs2 (by decide) (by decide) (by decide) hFit_rem
    refine e2ar_chain_tag3_step_more_cl hc hEpochDir x st0
      (M.stepEvents evs2 (M.stepEvents evs1 st)) w0_2 p'
      [ep1, ep2] (by simp) hptr' F_state hF_mono ep3 hep3
      hrem2_eq hlim_le hrem2_le hrem2_suf hlen_bound hFit3 hpost hs0A
      hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2
      hx27_2 hx28_2 hx29_2 hP2 ?_
    intro w0_3 evs3 s3 P3 hevs3 hafter_le hafter_suf
      hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3
      hx27_3 hx28_3 hx29_3 hP3
    subst hP3
    apply SepWPpIPlaced.of_sepWP (mid := decodeStatePlacedEntry + 508#64)
    refine SepWP.fold
      (e2ar_chainLinksVecAt_fold4 A.repAlloc s0.sp p' [ep1, ep2, ep3] (by simp) hptr')
      (by sep_focus) ?_
    apply SepWP.done hpc3 hrun3
    exact hdone w0_3 ((evs1 ++ evs2) ++ evs3) s3 _
      (((hevs1.append hevs2).append hevs3).mono (by decide) (by decide) (by decide))
      hafter_le hafter_suf
      hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3
      hx27_3 hx28_3 hx29_3 (by rw [M.stepEvents_append, M.stepEvents_append]; sep_ac_rfl)
  | _ :: _ :: _ :: _ :: _ =>
    simp only [List.length_cons] at hlen_le
    omega

private theorem e2ar_optChainPB_none_split72 (sp : BitVec 64) :
    memRegion (sp - 992#64 + 8#64) 72 ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
      ∃∗ w8 : BitVec 32, ∃∗ w9 : BitVec 32,
        ((sp - 984#64) ↦₆₄ w1) ∗ ((sp - 976#64) ↦₆₄ w2) ∗ ((sp - 968#64) ↦₆₄ w3) ∗
        ((sp - 960#64) ↦₆₄ w4) ∗ ((sp - 952#64) ↦₆₄ w5) ∗ ((sp - 944#64) ↦₆₄ w6) ∗
        ((sp - 936#64) ↦₆₄ w7) ∗ ((sp - 928#64) ↦₃₂ w8) ∗
        memRegion (sp - 924#64) 8 ∗ ((sp - 916#64) ↦₃₂ w9) := by
  have ha984 : sp - 992#64 + 8#64 = sp - 984#64 := by bv_omega
  rw [ha984,
    ProofLib.memRegion_split' (b := sp - 984#64) (n := 56) (k := 16)
      (b' := sp - 928#64) rfl (by bv_omega) (by decide),
    CryptoVerification.SpqrV1.Top.DecodeState.memRegion_56_eq_quads7At (sp - 984#64),
    ProofLib.memRegion_split' (b := sp - 928#64) (n := 4) (k := 12)
      (b' := sp - 924#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 924#64) (n := 8) (k := 4)
      (b' := sp - 916#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_four (sp - 928#64),
    ProofLib.memRegion_four (sp - 916#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w9
  apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; rintro ⟨w1, w2, w3, w4, w5, w6, w7⟩
  dsimp only [quads7At]
  have hc1 : sp - 984#64 + 8#64 = sp - 976#64 := by bv_omega
  have hc2 : sp - 984#64 + 16#64 = sp - 968#64 := by bv_omega
  have hc3 : sp - 984#64 + 24#64 = sp - 960#64 := by bv_omega
  have hc4 : sp - 984#64 + 32#64 = sp - 952#64 := by bv_omega
  have hc5 : sp - 984#64 + 40#64 = sp - 944#64 := by bv_omega
  have hc6 : sp - 984#64 + 48#64 = sp - 936#64 := by bv_omega
  rw [hc1, hc2, hc3, hc4, hc5, hc6]
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4
      (Entails.sepExists_right w5 (Entails.sepExists_right w6
        (Entails.sepExists_right w7 (Entails.sepExists_right w8
          (Entails.sepExists_right w9 ?_))))))))
  exact Entails.of_eq (by sep_ac_rfl)

private theorem e2ar_chain_slots_default_init (A : RustAlloc) (sp : BitVec 64) :
    ((sp - 968#64) ↦₆₄ 0#64) ∗ ((sp - 960#64) ↦₆₄ 1#64) ∗ ((sp - 952#64) ↦₆₄ 0#64) ∗
      ((sp - 928#64) ↦₃₂ 0#32) ∗ memRegion (sp - 924#64) 8 ⊢
      vecU8At A (sp - 968#64) 0#64 1#64 [] ∗ optChainParamsPBAt (sp - 928#64) none := by
  have hv := vecU8At_nil_zero_one A (sp - 968#64)
  have ha1 : sp - 968#64 + 8#64 = sp - 960#64 := by bv_omega
  have ha2 : sp - 968#64 + 16#64 = sp - 952#64 := by bv_omega
  rw [ha1, ha2] at hv
  have hp : ((sp - 928#64) ↦₃₂ 0#32) ∗ memRegion (sp - 924#64) 8 ⊢
      optChainParamsPBAt (sp - 928#64) none := by
    unfold optChainParamsPBAt
    dsimp only
    have ha3 : sp - 928#64 + 4#64 = sp - 924#64 := by bv_omega
    rw [ha3]
    exact Entails.refl _
  have hgroup :
      ((sp - 968#64) ↦₆₄ 0#64) ∗ ((sp - 960#64) ↦₆₄ 1#64) ∗ ((sp - 952#64) ↦₆₄ 0#64) ∗
        ((sp - 928#64) ↦₃₂ 0#32) ∗ memRegion (sp - 924#64) 8 =
      (((sp - 968#64) ↦₆₄ 0#64) ∗ ((sp - 960#64) ↦₆₄ 1#64) ∗ ((sp - 952#64) ↦₆₄ 0#64)) ∗
        (((sp - 928#64) ↦₃₂ 0#32) ∗ memRegion (sp - 924#64) 8) := by sep_ac_rfl
  rw [hgroup]
  exact sepConj_mono hv hp

/-- Outer Tag-2 entry (`+160 -> +508`, `evs = []`) on `rest1 = e2a_lenPrefixed (ChainPB.encodeRaw ch) rest`,
initializing the zero-capacity `ChainPB` stack slots at `s0.sp - 992#64` and setting
`.x20 = BitVec.ofNat 64 rest.length`. -/
theorem e2ar_outer_tag2_entry_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_i : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_i A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB)
    (inner : Option PqRatchetState.Inner)
    {rest1 rest : Bytes} {n c r : Nat}
    (hrest1_eq : rest1 = e2a_lenPrefixed (ChainPB.encodeRaw ch) rest)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs n c r))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx1 : s.readReg64 .x1 = 2#64)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_i A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨optVn, none, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hok : ∀ (sf : State) (P' : SepProp),
      (ChainPB.encodeRaw ch ++ rest).length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes (ChainPB.encodeRaw ch ++ rest) →
      sf.pc = decodeStatePlacedEntry + 508#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 rest.length →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes (ChainPB.encodeRaw ch ++ rest) ∗
        optVersionNegotiationPBCapOkAt A.repAlloc (s0.sp - 1040#64)
          (ChainPB.encodeRaw ch ++ rest).length optVn ∗
        ((s0.sp - 992#64) ↦₆₄ 0#64) ∗ ((s0.sp - 984#64) ↦₆₄ 8#64) ∗
        ((s0.sp - 976#64) ↦₆₄ 0#64) ∗
        vecU8At A.repAlloc (s0.sp - 968#64) 0#64 1#64 [] ∗
        ((s0.sp - 944#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 936#64) ↦₆₄ 0#64) ∗
        optChainParamsPBAt (s0.sp - 928#64) none ∗
        ((s0.sp - 916#64) ↦₃₂ 0#32) ∗
        optProtoPqRatchetInnerCapOkAt H_i A.repAlloc (s0.sp - 912#64)
          (ChainPB.encodeRaw ch ++ rest).length inner ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_i A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hdv_call := hc.decodeVarint2
  have hraw_lt : (ChainPB.encodeRaw ch).length < 2 ^ 64 := by
    rw [hrest1_eq] at hrest1_le
    unfold e2a_lenPrefixed at hrest1_le
    simp only [List.length_append] at hrest1_le
    omega
  obtain ⟨hdv_canon, hlen64_nat⟩ :=
    e2a_decodeVarint_lenPrefixed (raw := ChainPB.encodeRaw ch) (rest := rest) hraw_lt
  rw [← hrest1_eq] at hdv_canon
  have ha992 : s0.sp - 1040#64 + 48#64 = s0.sp - 992#64 := by bv_omega
  have ha912 : s0.sp - 1040#64 + 128#64 = s0.sp - 912#64 := by bv_omega
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  have hsp1048 : s0.sp - 1056#64 + 8#64 = s0.sp - 1048#64 := by bv_omega
  subst hP
  unfold protoPqRatchetStateCapOkAt optChainPBCapOkAt
  rw [ha992, ha912, sliceCursorAfter_eq_split hrest1_le hrest1_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced,
    WireType.toNat] at hpc hdv_call hx0 ⊢
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 160#64)
  refine SepWP.fold (e2ar_optChainPB_none_split72 s0.sp) (by sep_focus) ?_
  apply SepWP.done hpc hrun
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply e2ar_sepExists_elim; intro w1
  apply e2ar_sepExists_elim; intro w2
  apply e2ar_sepExists_elim; intro w3
  apply e2ar_sepExists_elim; intro w4
  apply e2ar_sepExists_elim; intro w5
  apply e2ar_sepExists_elim; intro w6
  apply e2ar_sepExists_elim; intro w7
  apply e2ar_sepExists_elim; intro w8
  apply e2ar_sepExists_elim; intro w9
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 244#64)
  wp_steps 4
  apply SepWP.done (by simp only [wp_norm, arm64_norm, hx1])
    (by simp only [wp_norm, arm64_norm, hrun])
  apply e2ar_pool_sync_step (A := A) (lim := lim) (st := st) (s := s)
  intro hpool_sync
  rw [hpool_sync]
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
  wp_steps_sync_pool ((blkPl_325).base + 284#64)
  try simp only [State.setMem_setMem]
  refine SepWP.fold (e2ar_chain_slots_default_init A.repAlloc s0.sp) (by sep_focus) ?_
  wp_steps_sync_pool (lsmpl.base 291)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm, hx0])
    (by simp only [wp_norm, arm64_norm, hrun])
  refine e2ar_call_decodeVarint2_some_cl hdv_call
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length))
    rest1 (ChainPB.encodeRaw ch ++ rest) (BitVec.ofNat 64 (ChainPB.encodeRaw ch).length)
    st hdv_canon hFit
    (ret_pc := (blkPl_325).base + 300#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hP := by pool_reg_norm; sep_focus) ?_
  intro s1 hlt2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_len
  let rest2 := ChainPB.encodeRaw ch ++ rest
  change rest2.length < rest1.length at hlt2
  change IsDropSuffix rest1 rest2 at hsuf2
  have hle2 : rest2.length ≤ rest1.length := Nat.le_of_lt hlt2
  have hrest2_le : rest2.length ≤ x.st.bytes.length := Nat.le_trans hle2 hrest1_le
  have hrest2_suf : IsDropSuffix x.st.bytes rest2 := suffix_trans hrest1_le hrest1_suf hle2 hsuf2
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, _⟩
  simp only [arm64_norm, wp_norm] at hx0_0 hx1_len hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
  simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  have hlt_len : ¬ rest2.length < (BitVec.ofNat 64 (ChainPB.encodeRaw ch).length).toNat := by
    rw [hlen64_nat]; dsimp only [rest2]; rw [List.length_append]; omega
  have hlim_eq :
      rest2.length - (BitVec.ofNat 64 (ChainPB.encodeRaw ch).length).toNat = rest.length := by
    rw [hlen64_nat]; dsimp only [rest2]; rw [List.length_append, Nat.add_sub_cancel_left]
  have ⟨hult, hule⟩ := len_ult_of_ge hlt_len (by omega)
  have hsub_lim := bv_len_sub_limit hlt_len
  rw [hlim_eq] at hsub_lim
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 508#64)
  refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
    hrest1_le hrest1_suf hle2) (by sep_focus) ?_
  dsimp only [sliceCursorAfter]
  wp_steps 4
  refine SepWP.fold (optVersionNegotiationPBCapOkAt_mono (A := A.repAlloc)
    (a := s0.sp - 1040#64) (rem1 := rest1.length) (rem2 := rest2.length)
    (opt := optVn) hle2) (by sep_focus) ?_
  refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_mono (H_inner := H_i) (A := A.repAlloc)
    (a := s0.sp - 912#64) (rem1 := rest1.length) (rem2 := rest2.length)
    (opt := inner) hle2) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm, hx0_0, hult, hule])
    (by simp only [arm64_norm, hrun1])
  exact hok _ _ hrest2_le hrest2_suf
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hult, hule])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
    (by simp only [arm64_norm, htr1])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hsub_lim, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by
      dsimp only [decodeStateLoopCommonPlaced, sliceCursorAfter]
      rw [hsp1048]
      pool_reg_norm
      sep_ac_rfl)

private theorem e2ar_fold_some_ch_placed (H_i : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (remLen : Nat) (optVn : Option VersionNegotiationPB)
    (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (hcap : ch.links.length + remLen ≤ 2 ^ 54) :
    optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
      chainLinksVecAt A (sp - 992#64) ch.links ∗
      vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
      ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
      ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
      optChainParamsPBAt (sp - 928#64) ch.params ∗
      ((sp - 916#64) ↦₃₂ ch.direction) ∗
      optProtoPqRatchetInnerCapOkAt H_i A (sp - 912#64) remLen inner ⊢
    protoPqRatchetStateCapOkAt H_i A (sp - 1040#64) remLen ⟨optVn, some ch, inner⟩ := by
  rw [protoPqRatchetStateCapOkAt_some_ch_eq_placed]
  have hpure :
      optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
        (⌜ch.links.length + remLen ≤ 2 ^ 54⌝ ∗
          chainLinksVecAt A (sp - 992#64) ch.links ∗
          vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
          ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
          ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
          optChainParamsPBAt (sp - 928#64) ch.params ∗
          ((sp - 916#64) ↦₃₂ ch.direction)) ∗
        optProtoPqRatchetInnerCapOkAt H_i A (sp - 912#64) remLen inner =
      ⌜ch.links.length + remLen ≤ 2 ^ 54⌝ ∗
        (optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
          chainLinksVecAt A (sp - 992#64) ch.links ∗
          vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
          ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
          ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
          optChainParamsPBAt (sp - 928#64) ch.params ∗
          ((sp - 916#64) ↦₃₂ ch.direction) ∗
          optProtoPqRatchetInnerCapOkAt H_i A (sp - 912#64) remLen inner) := by sep_ac_rfl
  rw [hpure]
  exact Entails.pure_right hcap (Entails.refl _)

/-- Full canonical outer Field-2 (`PqRatchetState::chain`, `+116 -> +1576`) driver under
`SpqrTightEvs 21 561525 79236`, exported for `E2aTightDecodeStateChPlacedBudget`. -/
theorem e2ar_ch_outer_field2_body_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (hEpochDir : E2ar2EpochDirCanonicalOk A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB)
    (hlinks_le : ch.links.length ≤ 3)
    (hroot_le : ch.nextRoot.length ≤ 32)
    (hall_ep : ∀ ep ∈ ch.links, e2ar2_ValidChainEpochPB ep)
    (inner : Option PqRatchetState.Inner)
    {cur rest : Bytes}
    (hcur_eq : cur = encodeMessage ChainPB.encodeRaw 2#32 ch ++ rest)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs 21 561525 79236))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 116#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = 8#64) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length
        ⟨optVn, none, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (w0' : BitVec 64) (evs_ch : List AllocEvent) (sf : State) (P' : SepProp),
      SpqrTightEvs 21 561525 79236 evs_ch →
      rest.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes rest →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 rest.length →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest.length
          ⟨optVn, some ch, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_ch st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  let rest1 := e2a_lenPrefixed (ChainPB.encodeRaw ch) rest
  have hcur_split : cur = encodeKey 2#32 .lengthDelimited ++ rest1 := by
    rw [hcur_eq]; exact e2ar_encodeMessage_append ChainPB.encodeRaw 2#32 ch rest
  refine e2ar_outer_key_decode_tag2_cl hc x st0 st
    (((s0.sp - 688#64) ↦₆₄ w0) ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length
        ⟨optVn, none, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304)
    hcur_split hcur_le hcur_suf hlen_bound hFit hs0A
    hpc hrun hsp htr hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hrest1_le hrest1_suf hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx21_1 hx22_1 hx23_1
    hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  have hle_cur1 : rest1.length ≤ cur.length := by
    have hlen_eq := congrArg List.length hcur_split
    dsimp only [rest1] at hlen_eq ⊢
    simp only [e2a_lenPrefixed, List.length_append] at hlen_eq ⊢
    omega
  apply SepWPpIPlaced.of_sepWP (mid := decodeStatePlacedEntry + 160#64)
  refine SepWP.fold
    (protoPqRatchetStateCapOkAt_mono hle_cur1 :
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length
        ⟨optVn, none, inner⟩ ⊢
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨optVn, none, inner⟩)
    (by sep_focus) ?_
  apply SepWP.done hpc1 hrun1
  refine e2ar_outer_tag2_entry_cl hc x st0 st w0 optVn ch inner rfl hrest1_le hrest1_suf
    hlen_bound hFit hs0A hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx21_1 hx22_1 hx23_1
    hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    (by sep_ac_rfl) ?_
  intro s2 P2 hraw_le hraw_suf hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2
    hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hP2
  let r6 := encodeOptMessage ChainParamsPB.encodeRaw 6#32 ch.params ++ rest
  let r5 := encodeUint64Field 5#32 ch.sendEpoch ++ r6
  let r4 := encodeBytesField 4#32 ch.nextRoot ++ r5
  let r3 := encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ch.links ++ r4
  let r2 := encodeUint64Field 2#32 ch.currentEpoch ++ r3
  let r1 := encodeInt32Field 1#32 ch.direction ++ r2
  have hraw_eq : ChainPB.encodeRaw ch ++ rest = r1 := by
    dsimp only [r1, r2, r3, r4, r5, r6]
    unfold ChainPB.encodeRaw
    simp only [List.append_assoc]
  rw [hraw_eq] at hraw_le hraw_suf hP2
  have hlim6 : rest.length ≤ r6.length := by dsimp only [r6]; rw [List.length_append]; omega
  have hlim5 : rest.length ≤ r5.length := by dsimp only [r5]; rw [List.length_append]; omega
  have hlim4 : rest.length ≤ r4.length := by dsimp only [r4]; rw [List.length_append]; omega
  have hlim3 : rest.length ≤ r3.length := by dsimp only [r3]; rw [List.length_append]; omega
  have hlim2 : rest.length ≤ r2.length := by dsimp only [r2]; rw [List.length_append]; omega
  let OuterVI : Nat → SepProp := fun rem =>
    optVersionNegotiationPBCapOkAt A.repAlloc (s0.sp - 1040#64) rem optVn ∗
      optProtoPqRatchetInnerCapOkAt H_inner A.repAlloc (s0.sp - 912#64) rem inner
  have hOuterVI_mono : ∀ {a b : Nat}, b ≤ a → OuterVI a ⊢ OuterVI b := fun hle =>
    sepConj_mono (optVersionNegotiationPBCapOkAt_mono hle)
      (optProtoPqRatchetInnerCapOkAt_mono hle)
  let F1 : Nat → SepProp := fun rem =>
    OuterVI rem ∗
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
      ((s0.sp - 992#64) ↦₆₄ 0#64) ∗ ((s0.sp - 984#64) ↦₆₄ 8#64) ∗
      ((s0.sp - 976#64) ↦₆₄ 0#64) ∗
      vecU8At A.repAlloc (s0.sp - 968#64) 0#64 1#64 [] ∗
      ((s0.sp - 944#64) ↦₆₄ 0#64) ∗ ((s0.sp - 936#64) ↦₆₄ 0#64) ∗
      optChainParamsPBAt (s0.sp - 928#64) none ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304
  have hF1_mono : ∀ {a b : Nat}, b ≤ a → F1 a ⊢ F1 b := fun hle =>
    sepConj_mono_left (hOuterVI_mono hle)
  refine e2ar_chain_tag1_opt_cl hc x st0 st F1 hF1_mono ch.direction rfl hlim2 hraw_le hraw_suf
    hlen_bound hFit hs0A hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2
    hx26_2 hx27_2 hx28_2 hx29_2
    (by rw [hP2]; dsimp only [F1, OuterVI]; sep_ac_rfl) ?_
  intro s3 P3 hr2_le hr2_suf hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3
    hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hP3
  let F2 : Nat → SepProp := fun rem =>
    OuterVI rem ∗
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
      ((s0.sp - 992#64) ↦₆₄ 0#64) ∗ ((s0.sp - 984#64) ↦₆₄ 8#64) ∗
      ((s0.sp - 976#64) ↦₆₄ 0#64) ∗
      vecU8At A.repAlloc (s0.sp - 968#64) 0#64 1#64 [] ∗
      ((s0.sp - 936#64) ↦₆₄ 0#64) ∗
      optChainParamsPBAt (s0.sp - 928#64) none ∗
      ((s0.sp - 916#64) ↦₃₂ ch.direction) ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304
  have hF2_mono : ∀ {a b : Nat}, b ≤ a → F2 a ⊢ F2 b := fun hle =>
    sepConj_mono_left (hOuterVI_mono hle)
  refine e2ar_chain_tag2_opt_cl hc x st0 st F2 hF2_mono ch.currentEpoch rfl hlim3 hr2_le hr2_suf
    hlen_bound hFit hs0A hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3
    hx26_3 hx27_3 hx28_3 hx29_3
    (by rw [hP3]; dsimp only [F1, F2, OuterVI]; sep_ac_rfl) ?_
  intro s4 P4 hr3_le hr3_suf hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4
    hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hP4
  let F3 : Nat → SepProp := fun rem =>
    OuterVI rem ∗
      vecU8At A.repAlloc (s0.sp - 968#64) 0#64 1#64 [] ∗
      ((s0.sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
      ((s0.sp - 936#64) ↦₆₄ 0#64) ∗
      optChainParamsPBAt (s0.sp - 928#64) none ∗
      ((s0.sp - 916#64) ↦₃₂ ch.direction)
  have hF3_mono : ∀ {a b : Nat}, b ≤ a → F3 a ⊢ F3 b := fun hle =>
    sepConj_mono_left (hOuterVI_mono hle)
  have hFit3 : FitsEnv M lim st (SpqrTightEvs 19 560049 79236) :=
    hFit.mono fun _ h => h.mono (by decide) (by decide) (by decide)
  refine e2ar_chain_tag3_links_cl hc hEpochDir x st0 st w0 F3 hF3_mono ch.links hlinks_le hall_ep
    rfl hlim4 hr3_le hr3_suf hlen_bound hFit3 hpost hs0A
    hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4
    hx29_4 (by rw [hP4]; dsimp only [F2, F3, OuterVI]; sep_ac_rfl) ?_
  intro w0_3 evs3 s5 P5 hevs3 hr4_le hr4_suf hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hx22_5
    hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 hx29_5 hP5
  let F4 : Nat → SepProp := fun rem =>
    OuterVI rem ∗
      ((s0.sp - 688#64) ↦₆₄ w0_3) ∗
      chainLinksVecAt A.repAlloc (s0.sp - 992#64) ch.links ∗
      ((s0.sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
      ((s0.sp - 936#64) ↦₆₄ 0#64) ∗
      optChainParamsPBAt (s0.sp - 928#64) none ∗
      ((s0.sp - 916#64) ↦₃₂ ch.direction) ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304
  have hF4_mono : ∀ {a b : Nat}, b ≤ a → F4 a ⊢ F4 b := fun hle =>
    sepConj_mono_left (hOuterVI_mono hle)
  have hFit4 : FitsEnv M lim (M.stepEvents evs3 st) (SpqrTightEvs 2 1476 32) :=
    e2ar_fitsEnv_tight_split_le hevs3 (by decide) (by decide) (by decide) hFit
  refine e2ar_chain_tag4_opt_cl hc x st0 (M.stepEvents evs3 st) F4 hF4_mono ch.nextRoot hroot_le
    rfl hlim5 hr4_le hr4_suf hlen_bound hFit4 hs0A
    hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5
    hx29_5 (by rw [hP5]; dsimp only [F3, F4, OuterVI]; sep_ac_rfl) ?_
  intro evs4 s6 P6 hevs4 hr5_le hr5_suf hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hx21_6 hx22_6
    hx23_6 hx24_6 hx25_6 hx26_6 hx27_6 hx28_6 hx29_6 hP6
  have hFit5 : FitsEnv M lim (M.stepEvents evs4 (M.stepEvents evs3 st)) (SpqrTightEvs 0 0 0) :=
    e2ar_fitsEnv_tight_split_le hevs4 (by decide) (by decide) (by decide) hFit4
  let F5 : Nat → SepProp := fun rem =>
    (OuterVI rem ∗ vecU8CapOkAt A.repAlloc (s0.sp - 968#64) rem ch.nextRoot) ∗
      ((s0.sp - 688#64) ↦₆₄ w0_3) ∗
      chainLinksVecAt A.repAlloc (s0.sp - 992#64) ch.links ∗
      ((s0.sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
      optChainParamsPBAt (s0.sp - 928#64) none ∗
      ((s0.sp - 916#64) ↦₃₂ ch.direction) ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304
  have hF5_mono : ∀ {a b : Nat}, b ≤ a → F5 a ⊢ F5 b := fun hle =>
    sepConj_mono_left (sepConj_mono (hOuterVI_mono hle) (vecU8CapOkAt_mono hle))
  refine e2ar_chain_tag5_opt_cl hc x st0 (M.stepEvents evs4 (M.stepEvents evs3 st)) F5 hF5_mono
    ch.sendEpoch rfl hlim6 hr5_le hr5_suf hlen_bound hFit5 hs0A
    hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hx21_6 hx22_6 hx23_6 hx24_6 hx25_6 hx26_6 hx27_6 hx28_6
    hx29_6 (by rw [hP6]; dsimp only [F4, F5, OuterVI]; sep_ac_rfl) ?_
  intro s7 P7 hr6_le hr6_suf hpc7 hrun7 hsp7 htr7 hx19_7 hx20_7 hx21_7 hx22_7 hx23_7 hx24_7
    hx25_7 hx26_7 hx27_7 hx28_7 hx29_7 hP7
  let F6 : Nat → SepProp := fun rem =>
    (OuterVI rem ∗ vecU8CapOkAt A.repAlloc (s0.sp - 968#64) rem ch.nextRoot) ∗
      ((s0.sp - 688#64) ↦₆₄ w0_3) ∗
      chainLinksVecAt A.repAlloc (s0.sp - 992#64) ch.links ∗
      ((s0.sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
      ((s0.sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
      ((s0.sp - 916#64) ↦₃₂ ch.direction) ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304
  have hF6_mono : ∀ {a b : Nat}, b ≤ a → F6 a ⊢ F6 b := fun hle =>
    sepConj_mono_left (sepConj_mono (hOuterVI_mono hle) (vecU8CapOkAt_mono hle))
  refine e2ar_chain_tag6_opt_cl hc x st0 (M.stepEvents evs4 (M.stepEvents evs3 st)) F6 hF6_mono
    ch.params rfl (Nat.le_refl _) hr6_le hr6_suf hlen_bound hFit5 hs0A
    hpc7 hrun7 hsp7 htr7 hx19_7 hx20_7 hx21_7 hx22_7 hx23_7 hx24_7 hx25_7 hx26_7 hx27_7 hx28_7
    hx29_7 (by rw [hP7]; dsimp only [F5, F6, OuterVI]; sep_ac_rfl) ?_
  intro s8 P8 hrest_le hrest_suf hpc8 hrun8 hsp8 htr8 hx19_8 hx20_8 hx21_8 hx22_8 hx23_8 hx24_8
    hx25_8 hx26_8 hx27_8 hx28_8 hx29_8 hP8
  have hlinks_cap : ch.links.length + rest.length ≤ 2 ^ 54 := by omega
  subst hP8
  dsimp only [F6, OuterVI]
  apply SepWPpIPlaced.of_sepWP (mid := decodeStatePlacedEntry + 508#64)
  refine SepWP.fold (e2ar_fold_some_ch_placed H_inner A.repAlloc s0.sp rest.length optVn ch inner
    hlinks_cap) (by sep_focus) ?_
  apply SepWP.done hpc8 hrun8
  have hevs_ch : SpqrTightEvs 21 561525 79236 (evs3 ++ evs4) :=
    (hevs3.append hevs4).mono (by decide) (by decide) (by decide)
  exact e2ar_chain_exit_508_cl x st0 (M.stepEvents (evs3 ++ evs4) st) w0_3 optVn ch inner rest
    hrest_le hrest_suf hs0A hpc8 hrun8 hsp8 htr8 hx19_8 hx20_8 hx21_8 hx22_8 hx23_8 hx24_8
    hx25_8 hx26_8 hx27_8 hx28_8 hx29_8
    (by rw [M.stepEvents_append]; sep_ac_rfl)
    (fun sf P' => hdone w0_3 (evs3 ++ evs4) sf P' hevs_ch hrest_le hrest_suf)

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStateChPlacedBudgetAux
