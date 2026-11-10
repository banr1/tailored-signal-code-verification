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
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightChainParamsClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationClPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopClPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import ProofLib.SepLogic.WPp

/-!
# Canonical Guarded-Tight `VersionNegotiationPB` Outer Field-1 & Shared Key/Merge Helpers (`Block 325`)

Proves zero-error-branch `decode_varint` (`Block 291`) and zero-capacity `bytes::merge`
(`Block 290`) call wrappers, parametric outer field-key decode (`+116 -> +160`), and canonical
outer Field 1 (`version_negotiation = some vn`, `+116 -> +1576`) under `SpqrTightEvs 2 1476 32`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStateVnPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkLib_eq_325 blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint mergeBytes)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost IsDropSuffix
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt suffix_trans)
open CryptoVerification.SpqrV1.Prost.BytesMerge
  (bytesMerge3Stack protoWireTypeToCodec proto_mergeBytes_toOption)
open CryptoVerification.SpqrV1.Prost.MessageMerge (v1StateMergeStack)
open CryptoVerification.SpqrV1.ProtoRepr (chainParamsPBAt optChainParamsPBAt)
open CryptoVerification.LibsignalSpqrV1
  (Bytes ChainPB ChainParamsPB PqRatchetState VersionNegotiationPB)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeBytesField encodeInt32Field encodeKey encodeMessage encodeOptMessage encodeVarint)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred bv_len_sub_limit bytesMergeCapOk_zero
   cmp_len_limit_of_eq cmp_len_limit_of_gt decodeStatePlacedEntry decodeStatePlacedProg
   key_and7_of_wt_some key_lsr32_eq_zero_of_lt key_lsr3_32_eq len_ult_of_ge
   optChainPBCapOkAt optChainPBCapOkAt_mono optChainParamsPBAt_none_to_init
   optChainParamsPBAt_some_default_init optChainParamsPBAt_some_eq
   optProtoPqRatchetInnerCapOkAt optProtoPqRatchetInnerCapOkAt_mono
   optVersionNegotiationPBCapOkAt optVersionNegotiationPB_none_split40
   pointsTo64_zero_split32 protoPqRatchetStateCapOkAt protoPqRatchetStateCapOkAt_mono
   protoPqRatchetStateCapOkAt_some_vn_eq proto_mergeBytes_suffix sp_sub_1392_aligned
   stackAt_of_callee stackAt_to_callee
   tag_cbz32_false tag_cbz64_false tag_lt_pow29_of_key_lt tag_setWidth32_ofNat
   tag_zeroExtend64_ofNat32 vecU8At_nil_zero_one vecU8At_zero_entails_vecU8CapOkAt
   vecU8CapOkAt vecU8CapOkAt_mono versionNegotiationPBCapOkAt versionNegotiationPB_default_eq
   wt_ult6)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.E2aTightBytesZeroAux
  (e2a_bytesMergeEventsCore_zero_tight_32 e2a_decodeKey_encodeKey e2a_decodeVarint2Env_eq_nil
   e2a_decodeVarint_encodeVarint e2a_decodeVarint_lenPrefixed e2a_encodeBytesField_append_of_ne
   e2a_encodeBytesField_of_nil e2a_encodeInt32Field_append_of_ne e2a_encodeInt32Field_of_zero
   e2a_fitsEnv_tight_split e2a_lenPrefixed e2a_mergeBytes_encode)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightChainParamsClPlacedBudget
  (E2aChainParamsCanonicalPostEnv E2aChainParamsCanonicalPreEnv
   e2a_chainParamsCanonicalPostEnv_eq_nil e2a_chainParamsMerge_cl_placed_ok_canonical
   e2a_fitsEnv_chainParams_canonical e2a_mergeMessage_chainParams_encode)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlacedOfEnv decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonClPlacedBudget
  (SepWPpIPlaced.call_chainParamsMerge_cl_ofEnv SepWPpIPlaced.call_decodeVarint2_cl)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced bytesMerge3DetBudgetSpec bytesMerge3RawBudgetSpecOfEnv
   decodeStateLoopCommonPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlaced DecodeStateCalleeContractsClPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationClPlacedBudgetAux
  (decodeState_vn_tag2_539cc_cl_placed_ofEnv decodeState_vn_tag3_53a34_cl_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopClPlacedBudgetAux
  (bytesMerge3Det_of_contractsClPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv bytesMergeEventsCore)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Reusable Canonical Call Wrappers (`decode_varint` & Zero-Cap `bytes::merge`) -/

/-- Call `decode_varint` (`Block 291`) when `decodeVarint bs = some (v, rest)` is statically known:
eliminates the `none` branch and simplifies `DecodeVarint2Env` to `[]` (`st` unchanged). -/
theorem e2a_call_decodeVarint2_some_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (bufRef slot ptr : BitVec 64) {bs rest : Bytes} {v : BitVec 64} (st : M.σ)
    (hd : decodeVarint bs = some (v, rest))
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = bufRef)
    (hlen : bs.length < 2 ^ 63)
    (hfit_nil : FitsEnv M lim st (fun evs => evs = []))
    (hP : P = ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ sf : State,
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
    (fun evs hdv => by
      rw [e2a_decodeVarint2Env_eq_nil hd hdv]
      exact hfit_nil [] rfl)
    hP ?_ ?_
  · intro sf v' rest' evs hdv hevs_dv hlt hsuf hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_v
    rw [hd] at hdv
    cases hdv
    have hevs_nil := e2a_decodeVarint2Env_eq_nil hd hevs_dv
    subst hevs_nil
    simp only [M.stepEvents_nil]
    exact hok sf hlt hsuf hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_v
  · intro _ _ hdv
    rw [hd] at hdv
    cases hdv

/-- Call `prost::encoding::bytes::merge` (`Block 290`) on a freshly zero-initialized `Vec<u8>`
(`vecU8At A.repAlloc valPtr 0#64 1#64 []`) when `mergeBytes .lengthDelimited bs = some (v, rest)` is
statically known. Eliminates the error branch and pins `evs = bytesMergeEventsCore .lengthDelimited 0#64 bs`. -/
theorem e2a_call_bytesMerge3_zero_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (bytesMerge3DetBudgetSpec A lim)))
    (valPtr bufRef slot ptr : BitVec 64) {bs v rest : Bytes} (st : M.σ)
    (hm : mergeBytes .lengthDelimited bs = some (v, rest))
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = valPtr)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hlen : bs.length < 2 ^ 63)
    (hfit : FitsEnv M lim st (fun evs => evs = bytesMergeEventsCore .lengthDelimited 0#64 bs))
    (hP : P = (vecU8At A.repAlloc valPtr 0#64 1#64 [] ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ sf : State,
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗
          A.pool lim (M.stepEvents (bytesMergeEventsCore .lengthDelimited 0#64 bs) st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          vecU8CapOkAt A.repAlloc valPtr rest.length v ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp := by
  intro hinv R' hm_mem hL
  rw [hP] at hm_mem
  let sp_cur := s0.sp - 1392#64
  let x_bm : BytesMergeGhost := ⟨.lengthDelimited, valPtr, 0#64, 1#64, [], bufRef, slot, ptr, bs⟩
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - bytesMerge3Stack) ∗ F
  have hpre : s.mem ⊨
      (withLsCodeRoLoaded lsmpl (bytesMerge3DetBudgetSpec A lim)).pre (x_bm, st) s ∗ (F_ext ∗ R') := by
    dsimp only [withLsCodeRoLoaded, bytesMerge3DetBudgetSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    dsimp only [bytesMerge3RawBudgetSpecOfEnv, BytesMergeEnv, x_bm, WireType.toNat]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen, bytesMergeCapOk_zero bs.length, hfit⟩, ?_⟩
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur bytesMerge3Stack (by decide)))))))) hm_mem
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; sep_ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome (x_bm, st) (F_ext ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ (bytesMerge3DetBudgetSpec A lim).post (x_bm, st) s sm ∗ (F_ext ∗ R') at hpost
    dsimp only [bytesMerge3DetBudgetSpec, bytesMerge3RawBudgetSpecOfEnv, BytesMergeEnv, x_bm] at hpost
    rw [hm, hsp] at hpost
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨cap', ptr', evs, hpost⟩
    have hpost_pure : sm.mem ⊨ ⌜evs = bytesMergeEventsCore .lengthDelimited 0#64 bs⌝ ∗
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
    subst hevs
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
        (((bufRef ↦₆₄ slot) ∗
          A.pool lim (M.stepEvents (bytesMergeEventsCore .lengthDelimited 0#64 bs) st) sm ∗
          stackAt sp_cur v1StateMergeStack ∗
          vecU8CapOkAt A.repAlloc valPtr rest.length v ∗
          sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R' :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost1'
    have hmb_to :
        (CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes .lengthDelimited bs).toOption =
          some (v, rest) := by
      rw [proto_mergeBytes_toOption]; exact hm
    have ⟨hle, hsuf⟩ := proto_mergeBytes_suffix hmb_to
    obtain ⟨sf, hsteps', hout'⟩ :=
      hok sm hle hsuf hpcm hrunm hspm
        (htr.step htrm hcsm) hcsm hx0_0 (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [bytesMerge3DetBudgetSpec, bytesMerge3RawBudgetSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [bytesMerge3DetBudgetSpec, bytesMerge3RawBudgetSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [bytesMerge3DetBudgetSpec, bytesMerge3RawBudgetSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

/-! ## 2. Canonical Outer Field-Key Decode (`+116 -> +160`) -/

private theorem sync_pool_at [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (x : DecodeStateGhost) (s0 s_old : State)
    {prog : Program} {ret : BitVec 64} {s_cur : State} {P : SepProp}
    {Q Q_err : State → SepProp → Prop}
    (hpool : A.pool lim st s_old = A.pool lim st s_cur)
    (h : ∀ s', decodeStateLoopCommonPlaced A lim st x s0 s_old =
        decodeStateLoopCommonPlaced A lim st x s0 s' →
      s' = s_cur → SepWPpIPlaced prog ret s_cur P Q Q_err) :
    SepWPpIPlaced prog ret s_cur P Q Q_err :=
  h s_cur (by dsimp only [decodeStateLoopCommonPlaced]; rw [hpool]) rfl

private theorem truncate32_signExtend64 (v : BitVec 32) :
    (v.signExtend 64).truncate 32 = v := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getElem_signExtend, hi]

/-- Canonical outer-loop field-key decode (`+116 -> +160`) on `cur = encodeKey tag wt ++ rest1`
(`1 ≤ tag.toNat < 2 ^ 29`), parametric in `F_state : SepProp` and emitting `0` events (`st` unchanged). -/
theorem e2a_outer_key_decode_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (F_state : SepProp)
    {cur rest1 : Bytes} (tag : BitVec 32)
    (wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType)
    (hcur_eq : cur = encodeKey tag wt ++ rest1)
    (htag1 : 1 ≤ tag.toNat) (htag29 : tag.toNat < 2 ^ 29)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hfit_nil : FitsEnv M lim st (fun evs => evs = []))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 116#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      F_state ∗ decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (sf : State) (P' : SepProp),
      rest1.length < cur.length → rest1.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes rest1 →
      sf.pc = decodeStatePlacedEntry + 160#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x0 = BitVec.ofNat 64 (protoWireTypeToCodec wt).toNat →
      sf.readReg64 .x1 = BitVec.ofNat 64 tag.toNat →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
        F_state ∗ decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hdv_call := hc.decodeVarint2
  have hkey_prop := e2a_decodeKey_encodeKey tag wt rest1 htag1 htag29
  dsimp only at hkey_prop
  generalize (((tag <<< 3) ||| wt.toU32).zeroExtend 64 : BitVec 64) = key at hkey_prop
  rcases hkey_prop with ⟨hdv_eq, _, hnot_ge, hwt_eq, hdiv8, _⟩
  rw [← hcur_eq] at hdv_eq
  subst hP
  rw [sliceCursorAfter_eq_split hcur_le hcur_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced]
    at hpc hdv_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
  wp_steps_sync_pool (lsmpl.base 291)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine e2a_call_decodeVarint2_some_cl hdv_call
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) st hdv_eq
    (ret_pc := (blkPl_325).base + 124#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hlen := by omega) (hfit_nil := hfit_nil)
    (hP := by sep_focus) ?_
  intro s1 hlt1 hsuf1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_key
  have hle1 : rest1.length ≤ cur.length := Nat.le_of_lt hlt1
  have hrest1_le : rest1.length ≤ x.st.bytes.length := Nat.le_trans hle1 hcur_le
  have hrest1_suf : IsDropSuffix x.st.bytes rest1 := suffix_trans hcur_le hcur_suf hle1 hsuf1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx0_0 hx1_key hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
  simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  have hkey_lt32 : key.toNat < 4294967296 := Nat.lt_of_not_ge hnot_ge
  have hkey_lt64 : key.toNat < 18446744073709551616 := Nat.lt_trans hkey_lt32 (by decide)
  have hkey_div_lt64 : key.toNat / 8 < 18446744073709551616 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hkey_lt64
  have hkey_div_ge1 : 1 ≤ key.toNat / 8 := by rw [hdiv8]; exact htag1
  have hk_zero : key >>> 32 = 0#64 := key_lsr32_eq_zero_of_lt hnot_ge
  have hand7 : key &&& 7#64 = BitVec.ofNat 64 (protoWireTypeToCodec wt).toNat :=
    key_and7_of_wt_some hwt_eq
  have ⟨hwt_ult, hwt_ule⟩ := wt_ult6 (protoWireTypeToCodec wt)
  have hlsr3 : BitVec.truncate 32 key >>> 3 = BitVec.ofNat 32 (key.toNat / 8) :=
    key_lsr3_32_eq hnot_ge
  have hlsr3_64 : BitVec.zeroExtend 64 (BitVec.truncate 32 key) >>> 3 =
      BitVec.ofNat 64 (key.toNat / 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    change ((key.toNat % 4294967296) % 18446744073709551616) / 8 =
      (key.toNat / 8) % 18446744073709551616
    rw [Nat.mod_eq_of_lt hkey_lt32, Nat.mod_eq_of_lt hkey_lt64, Nat.mod_eq_of_lt hkey_div_lt64]
  have htag29' : key.toNat / 8 < 2 ^ 29 := tag_lt_pow29_of_key_lt hnot_ge
  have hze : BitVec.zeroExtend 64 (BitVec.ofNat 32 (key.toNat / 8)) =
      BitVec.ofNat 64 (key.toNat / 8) :=
    tag_zeroExtend64_ofNat32 htag29'
  have htw32 : BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) =
      BitVec.ofNat 32 (key.toNat / 8) :=
    tag_setWidth32_ofNat (key.toNat / 8)
  have hcbz64 := tag_cbz64_false hkey_div_ge1 htag29'
  have hcbz32 := tag_cbz32_false hkey_div_ge1 htag29'
  have hze_tag : BitVec.zeroExtend 64 (BitVec.ofNat 32 tag.toNat) = BitVec.ofNat 64 tag.toNat :=
    tag_zeroExtend64_ofNat32 htag29
  have htw32_tag : BitVec.truncate 32 (BitVec.ofNat 64 tag.toNat) = BitVec.ofNat 32 tag.toNat :=
    tag_setWidth32_ofNat tag.toNat
  have hcbz64_tag := tag_cbz64_false htag1 htag29
  have hcbz32_tag := tag_cbz32_false htag1 htag29
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 160#64)
  wp_steps 9
  refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
    hcur_le hcur_suf hle1) (by sep_focus) ?_
  apply SepWP.done
    (by simp only [wp_norm, arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule,
          hlsr3, hlsr3_64, hze, htw32, hcbz64, hcbz32, hze_tag, htw32_tag, hcbz64_tag, hcbz32_tag])
    (by simp only [wp_norm, arm64_norm, hrun1])
  exact hdone _ _ hlt1 hrest1_le hrest1_suf
    (by dsimp only [decodeStatePlacedEntry]
        simp only [wp_norm, arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule,
          hlsr3, hlsr3_64, hze, htw32, hcbz64, hcbz32, hze_tag, htw32_tag, hcbz64_tag, hcbz32_tag])
    (by simp only [wp_norm, arm64_norm, hrun1]) (by simp only [wp_norm, arm64_norm, hsp1])
    (by simp only [wp_norm, arm64_norm, htr1])
    (by simp only [wp_norm, arm64_norm, Reg.x0, hand7, *])
    (by rw [← hdiv8]; simp only [wp_norm, arm64_norm, Reg.x1, hx1_key, hlsr3, hlsr3_64, hze, htw32,
          hze_tag, htw32_tag])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by dsimp only [decodeStateLoopCommonPlaced]; simp only [wp_norm, arm64_norm]; sep_ac_rfl)

/-! ## 3. Canonical `VersionNegotiationPB` Key Decode (`+1252 -> +1304`) & Pinned Zero-Cap Init -/

private def versionNegotiationZeroCapAt (A : RustAlloc) (a : BitVec 64)
    (v : VersionNegotiationPB) : SepProp :=
  vecU8At A a 0#64 1#64 v.authKey ∗
    optChainParamsPBAt (a + 0x18#64) v.chainParams ∗
    ((a + 0x24#64) ↦₃₂ v.direction) ∗
    ((a + 0x28#64) ↦₃₂ v.minVersion) ∗
    memRegion (a + 0x2c#64) 4

private theorem versionNegotiationZeroCapAt_default_init (A : RustAlloc) (a : BitVec 64) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗
      ((a + 24#64) ↦₃₂ 0#32) ∗ memRegion (a + 28#64) 8 ∗
      ((a + 36#64) ↦₆₄ 0#64) ∗ memRegion (a + 44#64) 4 ⊢
    versionNegotiationZeroCapAt A a default := by
  rw [versionNegotiationPB_default_eq]
  unfold versionNegotiationZeroCapAt optChainParamsPBAt
  dsimp only
  have h1 := vecU8At_nil_zero_one A a
  have h36 : ((a + 36#64) ↦₆₄ 0#64) = ((a + 36#64) ↦₃₂ 0#32) ∗ ((a + 40#64) ↦₃₂ 0#32) := by
    rw [pointsTo64_zero_split32 (a + 36#64)]
    have : (a + 36#64) + 4#64 = a + 40#64 := by bv_omega
    rw [this]
  have ha28 : (a + 24#64) + 4#64 = a + 28#64 := by bv_omega
  rw [h36, ha28]
  refine Entails.trans (sepConj_mono_left h1) ?_
  exact Entails.of_eq (by sep_ac_rfl)

private theorem versionNegotiationZeroCapAt_default_entails_capOk (A : RustAlloc) (a : BitVec 64)
    (remLen : Nat) :
    versionNegotiationZeroCapAt A a default ⊢
      versionNegotiationPBCapOkAt A a remLen default := by
  rw [versionNegotiationPB_default_eq]
  unfold versionNegotiationZeroCapAt versionNegotiationPBCapOkAt
  dsimp only
  exact sepConj_mono_left (vecU8At_zero_entails_vecU8CapOkAt A a remLen)

private theorem e2a_encodeKey_pos (tag : BitVec 32)
    (wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType) :
    1 ≤ (encodeKey tag wt).length := by
  unfold encodeKey
  exact (CryptoVerification.SpqrV1Sync.Codec.proto_encodeVarint_length _).1

/-- Canonical `VersionNegotiationPB` field-key decode (`+1252 -> +1264 -> +1304`) on
`cur = encodeKey tag wt ++ rest1` when `limit ≤ rest1.length` (`1 ≤ tag.toNat < 2 ^ 29`),
parametric in `F_vn : SepProp` and emitting `0` events (`st` unchanged). -/
private theorem e2a_vn_key_decode_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (F_vn : SepProp)
    {cur rest1 : Bytes} (limit : Nat) (tag : BitVec 32)
    (wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType)
    (hcur_eq : cur = encodeKey tag wt ++ rest1)
    (hlim_le : limit ≤ rest1.length)
    (htag1 : 1 ≤ tag.toNat) (htag29 : tag.toNat < 2 ^ 29)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hfit_nil : FitsEnv M lim st (fun evs => evs = []))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1252#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      F_vn ∗ decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (sf : State) (P' : SepProp),
      rest1.length < cur.length → rest1.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes rest1 →
      sf.pc = decodeStatePlacedEntry + 1304#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x0 = BitVec.ofNat 64 (protoWireTypeToCodec wt).toNat →
      sf.readReg64 .x1 = BitVec.ofNat 64 tag.toNat →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
        F_vn ∗ decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hk_pos := e2a_encodeKey_pos tag wt
  have hcur_len : cur.length = (encodeKey tag wt).length + rest1.length := by
    rw [hcur_eq, List.length_append]
  have hgt : ¬ cur.length ≤ limit := by omega
  have ⟨hult_lim, hule_lim⟩ := cmp_len_limit_of_gt hgt (by omega)
  have hdv_call := hc.decodeVarint2
  have hkey_prop := e2a_decodeKey_encodeKey tag wt rest1 htag1 htag29
  dsimp only at hkey_prop
  generalize (((tag <<< 3) ||| wt.toU32).zeroExtend 64 : BitVec 64) = key at hkey_prop
  rcases hkey_prop with ⟨hdv_eq, _, hnot_ge, hwt_eq, hdiv8, _⟩
  rw [← hcur_eq] at hdv_eq
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  have hult_eq : (BitVec.ofNat 64 limit).ult
      (BitVec.ofNat 64 (List.length (encodeKey tag wt ++ rest1))) = true := by
    rw [← hcur_eq]; exact hult_lim
  have hule_eq : (BitVec.ofNat 64 (List.length (encodeKey tag wt ++ rest1))).ule
      (BitVec.ofNat 64 limit) = false := by
    rw [← hcur_eq]; exact hule_lim
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, sliceCursorAfter] at hpc hdv_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1264#64)
  wp_steps 3
  apply SepWP.done
    (by simp only [wp_norm, arm64_norm, hx20, hult_lim, hule_lim, hult_eq, hule_eq])
    (by simp only [wp_norm, arm64_norm, hrun])
  refine sync_pool_at A lim st x s0 s (by simp only [wp_norm, arm64_norm]) fun s_mid hcomm hs_mid => ?_
  subst hs_mid
  rw [hcomm]
  dsimp only [decodeStateLoopCommonPlaced]
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
  refine SepWP.fold (Entails.of_eq (sliceCursorAfter_eq_split hcur_le hcur_suf))
    (by dsimp only [sliceCursorAfter]; try sep_focus) ?_
  wp_steps_sync_pool (lsmpl.base 291)
  try simp only [State.setMem_setMem]
  apply SepWP.done
    (by simp only [wp_norm, arm64_norm, hx20, hult_lim, hule_lim, hult_eq, hule_eq])
    (by simp only [wp_norm, arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine e2a_call_decodeVarint2_some_cl hdv_call
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) st hdv_eq
    (ret_pc := (blkPl_325).base + 1272#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hlen := by omega) (hfit_nil := hfit_nil)
    (hP := by sep_focus) ?_
  intro s1 hlt1 hsuf1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_key
  have hle1 : rest1.length ≤ cur.length := Nat.le_of_lt hlt1
  have hrest1_le : rest1.length ≤ x.st.bytes.length := Nat.le_trans hle1 hcur_le
  have hrest1_suf : IsDropSuffix x.st.bytes rest1 := suffix_trans hcur_le hcur_suf hle1 hsuf1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hvregs_1⟩
  simp only [arm64_norm, wp_norm] at hx0_0 hx1_key hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
  simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  have hkey_lt32 : key.toNat < 4294967296 := Nat.lt_of_not_ge hnot_ge
  have hkey_lt64 : key.toNat < 18446744073709551616 := Nat.lt_trans hkey_lt32 (by decide)
  have hkey_div_lt64 : key.toNat / 8 < 18446744073709551616 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hkey_lt64
  have hkey_div_ge1 : 1 ≤ key.toNat / 8 := by rw [hdiv8]; exact htag1
  have hk_zero : key >>> 32 = 0#64 := key_lsr32_eq_zero_of_lt hnot_ge
  have hand7 : key &&& 7#64 = BitVec.ofNat 64 (protoWireTypeToCodec wt).toNat :=
    key_and7_of_wt_some hwt_eq
  have ⟨hwt_ult, hwt_ule⟩ := wt_ult6 (protoWireTypeToCodec wt)
  have hlsr3 : BitVec.truncate 32 key >>> 3 = BitVec.ofNat 32 (key.toNat / 8) :=
    key_lsr3_32_eq hnot_ge
  have hlsr3_64 : BitVec.zeroExtend 64 (BitVec.truncate 32 key) >>> 3 =
      BitVec.ofNat 64 (key.toNat / 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    change ((key.toNat % 4294967296) % 18446744073709551616) / 8 =
      (key.toNat / 8) % 18446744073709551616
    rw [Nat.mod_eq_of_lt hkey_lt32, Nat.mod_eq_of_lt hkey_lt64, Nat.mod_eq_of_lt hkey_div_lt64]
  have htag29' : key.toNat / 8 < 2 ^ 29 := tag_lt_pow29_of_key_lt hnot_ge
  have hze : BitVec.zeroExtend 64 (BitVec.ofNat 32 (key.toNat / 8)) =
      BitVec.ofNat 64 (key.toNat / 8) :=
    tag_zeroExtend64_ofNat32 htag29'
  have htw32 : BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) =
      BitVec.ofNat 32 (key.toNat / 8) :=
    tag_setWidth32_ofNat (key.toNat / 8)
  have hcbz64 := tag_cbz64_false hkey_div_ge1 htag29'
  have hcbz32 := tag_cbz32_false hkey_div_ge1 htag29'
  have hze_tag : BitVec.zeroExtend 64 (BitVec.ofNat 32 tag.toNat) = BitVec.ofNat 64 tag.toNat :=
    tag_zeroExtend64_ofNat32 htag29
  have htw32_tag : BitVec.truncate 32 (BitVec.ofNat 64 tag.toNat) = BitVec.ofNat 32 tag.toNat :=
    tag_setWidth32_ofNat tag.toNat
  have hcbz64_tag := tag_cbz64_false htag1 htag29
  have hcbz32_tag := tag_cbz32_false htag1 htag29
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1304#64)
  wp_steps 8
  refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
    hcur_le hcur_suf hle1) (by sep_focus) ?_
  apply SepWP.done
    (by simp only [wp_norm, arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3,
          hlsr3_64, hze, htw32, hcbz64, hcbz32, hze_tag, htw32_tag, hcbz64_tag, hcbz32_tag])
    (by simp only [wp_norm, arm64_norm, hrun1])
  exact hdone _ _ hlt1 hrest1_le hrest1_suf
    (by dsimp only [decodeStatePlacedEntry]
        simp only [wp_norm, arm64_norm, hx0_0, hx1_key, hk_zero, hand7, hwt_ult, hwt_ule, hlsr3,
          hlsr3_64, hze, htw32, hcbz64, hcbz32, hze_tag, htw32_tag, hcbz64_tag, hcbz32_tag])
    (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
    (by simp only [arm64_norm, htr1])
    (by simp only [arm64_norm, Reg.x0, hand7, *])
    (by rw [← hdiv8]; simp only [arm64_norm, Reg.x1, hx1_key, hlsr3, hlsr3_64, hze, htw32,
          hze_tag, htw32_tag])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by dsimp only [decodeStateLoopCommonPlaced]; simp only [wp_norm, arm64_norm]; sep_ac_rfl)

/-! ## 4. Canonical `VersionNegotiationPB` Tag Steps (`+1252 -> +1252` / `+1576`) -/

/-- Tag 1 (`auth_key`, `vn.authKey.length ≤ 32`) from `+1252` with zero-cap `versionNegotiationZeroCapAt`
to `+1252` with `protoPqRatchetStateCapOkAt` (`SpqrTightEvs 2 1476 32`). -/
private theorem e2a_vn_tag1_step_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (authKey : Bytes) (hkey_le : authKey.length ≤ 32)
    (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    {cur0 cur1 : Bytes} (limit : Nat)
    (hcur0_eq : cur0 = encodeBytesField 1#32 authKey ++ cur1)
    (hlim_le : limit ≤ cur1.length)
    (hcur0_le : cur0.length ≤ x.st.bytes.length)
    (hcur0_suf : IsDropSuffix x.st.bytes cur0)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs 2 1476 32))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1252#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur0 ∗
      versionNegotiationZeroCapAt A.repAlloc (s0.sp - 1040#64) default ∗
      optChainPBCapOkAt A.repAlloc (s0.sp - 992#64) cur0.length optCh ∗
      optProtoPqRatchetInnerCapOkAt H_inner A.repAlloc (s0.sp - 912#64) cur0.length inner ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (evs_t1 : List AllocEvent) (sf : State) (P' : SepProp),
      SpqrTightEvs 2 1476 32 evs_t1 →
      cur1.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes cur1 →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur1 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur1.length
          ⟨some { (default : VersionNegotiationPB) with authKey := authKey }, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_t1 st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  by_cases hk0 : authKey = []
  · subst hk0
    have hcur_id : cur0 = cur1 := by
      rw [hcur0_eq, e2a_encodeBytesField_of_nil, List.nil_append]
    subst hcur_id
    have hdef_eq :
        ({ (default : VersionNegotiationPB) with authKey := [] } : VersionNegotiationPB) =
          default := by
      rw [versionNegotiationPB_default_eq]
    have hfold : P ⊢
        ((s0.sp - 688#64) ↦₆₄ w0) ∗
          sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur0 ∗
          protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur0.length
            ⟨some { (default : VersionNegotiationPB) with authKey := [] }, optCh, inner⟩ ∗
          memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
          decodeStateLoopCommonPlaced A lim (M.stepEvents [] st) x s0 s := by
      rw [hP, hdef_eq]
      unfold protoPqRatchetStateCapOkAt optVersionNegotiationPBCapOkAt
      dsimp only
      have ha48 : s0.sp - 1040#64 + 48#64 = s0.sp - 992#64 := by bv_omega
      have ha128 : s0.sp - 1040#64 + 128#64 = s0.sp - 912#64 := by bv_omega
      rw [ha48, ha128, M.stepEvents_nil]
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (versionNegotiationZeroCapAt_default_entails_capOk A.repAlloc (s0.sp - 1040#64)
            cur0.length)))) ?_
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPpIPlaced.mono_pre hfold ?_
    exact hdone [] s _ (SpqrTightEvs.nil 2 1476 32) hcur0_le hcur0_suf
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 rfl
  · have hcur0_key := e2a_encodeBytesField_append_of_ne 1#32 hk0 cur1
    rw [← hcur0_eq] at hcur0_key
    let rest_bm := encodeVarint (BitVec.ofNat 64 authKey.length) ++ authKey ++ cur1
    have hlim_bm : limit ≤ rest_bm.length := by
      dsimp only [rest_bm]
      rw [List.length_append, List.length_append]
      omega
    refine e2a_vn_key_decode_cl (PreEnv := PreEnv) (PostEnv := PostEnv)
      hc.toDecodeStateCalleeContractsClPlaced x st0 st
      (((s0.sp - 688#64) ↦₆₄ w0) ∗
        versionNegotiationZeroCapAt A.repAlloc (s0.sp - 1040#64) default ∗
        optChainPBCapOkAt A.repAlloc (s0.sp - 992#64) cur0.length optCh ∗
        optProtoPqRatchetInnerCapOkAt H_inner A.repAlloc (s0.sp - 912#64) cur0.length inner ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304)
      limit 1#32 .lengthDelimited hcur0_key hlim_bm (by decide) (by decide)
      hcur0_le hcur0_suf hlen_bound
      (fun evs he => by subst he; exact hFit [] (SpqrTightEvs.nil 2 1476 32))
      hs0A hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
      (by rw [hP]; sep_ac_rfl) ?_
    intro s1 P1 hlt_bm hbm_le hbm_suf hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1
      hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hP1
    have hle_bm0 : rest_bm.length ≤ cur0.length := Nat.le_of_lt hlt_bm
    subst hP1
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, protoWireTypeToCodec,
      WireType.toNat] at hpc1 hx0_1 hx1_1 ⊢
    change s1.readReg64 .x1 = 1#64 at hx1_1
    change s1.readReg64 .x0 = 2#64 at hx0_1
    have hbm_call := bytesMerge3Det_of_contractsClPlacedX hc
    have hmb_eq : mergeBytes .lengthDelimited rest_bm = some (authKey, cur1) :=
      e2a_mergeBytes_encode (by omega)
    have htight_bm : SpqrTightEvs 2 1476 32 (bytesMergeEventsCore .lengthDelimited 0#64 rest_bm) :=
      e2a_bytesMergeEventsCore_zero_tight_32 hmb_eq hkey_le
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1412#64)
    wp_steps 4
    refine SepWP.fold (Entails.of_eq (sliceCursorAfter_eq_split hbm_le hbm_suf)) (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm, hx1_1])
      (by simp only [wp_norm, arm64_norm, hrun1])
    refine sync_pool_at A lim st x s0 s1 (by simp only [wp_norm, arm64_norm]) fun s_mid hcomm hs_mid => ?_
    subst hs_mid
    rw [hcomm, versionNegotiationPB_default_eq]
    unfold versionNegotiationZeroCapAt
    dsimp only [decodeStateLoopCommonPlaced]
    apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 290)
    wp_steps_sync_pool (lsmpl.base 290)
    try simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [wp_norm, arm64_norm, hx1_1])
      (by simp only [wp_norm, arm64_norm, hrun1])
    have hsp160 : s0.sp - 1392#64 + 352#64 = s0.sp - 1040#64 := by bv_omega
    have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
    refine e2a_call_bytesMerge3_zero_cl hbm_call (s0.sp - 1040#64)
      (s0.sp - 336#64) (s0.sp - 1056#64)
      (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest_bm.length)) st hmb_eq
      (ret_pc := (blkPl_325).base + 1424#64)
      (hpc := by simp only [wp_norm, arm64_norm])
      (hrun := by simp only [wp_norm, arm64_norm, hrun1])
      (hsp := by simp only [wp_norm, arm64_norm, hsp1]) (hs0A := hs0A)
      (hlr := by simp only [wp_norm, arm64_norm])
      (htr := by simp only [wp_norm, arm64_norm, htr1])
      (hx0 := by simp only [wp_norm, arm64_norm, hx0_1]; try rfl)
      (hx1 := by simp only [wp_norm, arm64_norm, hsp1, hsp160])
      (hx2 := by simp only [wp_norm, arm64_norm, hx29_1, hx29_f0])
      (hlen := by omega)
      (hfit := fun evs he => by subst he; exact hFit _ htight_bm)
      (hP := by sep_focus) ?_
    intro s2 hle_cur1 hsuf_cur1 hpc2 hrun2 hsp2 htr2 hcs2 hx0_0
    have hcur1_le : cur1.length ≤ x.st.bytes.length := Nat.le_trans hle_cur1 hbm_le
    have hcur1_suf : IsDropSuffix x.st.bytes cur1 := suffix_trans hbm_le hbm_suf hle_cur1 hsuf_cur1
    have hle_cur1_0 : cur1.length ≤ cur0.length := Nat.le_trans hle_cur1 hle_bm0
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2,
      hx28_2, hx29_2, hvregs_2⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2
    simp only [arm64_norm, wp_norm] at hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1252#64)
    wp_steps_sync_pool ((blkPl_325).base + 1252#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hbm_le hbm_suf hle_cur1) (by sep_focus) ?_
    refine SepWP.fold (optChainPBCapOkAt_mono (A := A.repAlloc) (a := s0.sp - 992#64)
      (rem1 := cur0.length) (rem2 := cur1.length) (opt := optCh) hle_cur1_0)
      (by sep_focus) ?_
    refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
      (a := s0.sp - 912#64) (rem1 := cur0.length) (rem2 := cur1.length) (opt := inner) hle_cur1_0)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2])
    exact hdone (bytesMergeEventsCore .lengthDelimited 0#64 rest_bm) _ _
      htight_bm hcur1_le hcur1_suf
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun2]) (by simp only [wp_norm, arm64_norm, hsp2])
      (by simp only [wp_norm, arm64_norm, htr2])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by
        rw [versionNegotiationPB_default_eq, protoPqRatchetStateCapOkAt_some_vn_eq]
        dsimp only [decodeStateLoopCommonPlaced]
        sep_ac_rfl)

/-- Tag 2 (`direction : i32`) from `+1252` to `+1252` (`evs = []`, `st` unchanged). -/
private theorem e2a_vn_tag2_step_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (vn1 : VersionNegotiationPB) (hdir0 : vn1.direction = 0#32)
    (dir : BitVec 32) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    {cur1 cur2 : Bytes} (limit : Nat)
    (hcur1_eq : cur1 = encodeInt32Field 2#32 dir ++ cur2)
    (hlim_le : limit ≤ cur2.length)
    (hcur1_le : cur1.length ≤ x.st.bytes.length)
    (hcur1_suf : IsDropSuffix x.st.bytes cur1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hfit_nil : FitsEnv M lim st (fun evs => evs = []))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1252#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur1.length
        ⟨some vn1, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (sf : State) (P' : SepProp),
      cur2.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes cur2 →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur2.length
          ⟨some { vn1 with direction := dir }, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  by_cases hd0 : dir = 0#32
  · subst hd0
    have hcur_id : cur1 = cur2 := by
      rw [hcur1_eq, e2a_encodeInt32Field_of_zero, List.nil_append]
    subst hcur_id
    have hvn_id : ({ vn1 with direction := 0#32 } : VersionNegotiationPB) = vn1 := by
      cases vn1; dsimp only at hdir0 ⊢; subst hdir0; rfl
    rw [← hvn_id] at hP
    exact hdone s P hcur1_le hcur1_suf hpc hrun hsp htr
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP
  · have hcur1_key := e2a_encodeInt32Field_append_of_ne 2#32 dir hd0 cur2
    rw [← hcur1_eq] at hcur1_key
    let rest_dv := encodeVarint (dir.signExtend 64) ++ cur2
    have hlim_dv : limit ≤ rest_dv.length := by
      dsimp only [rest_dv]; rw [List.length_append]; omega
    refine e2a_vn_key_decode_cl (PreEnv := PreEnv) (PostEnv := PostEnv)
      hc x st0 st
      (((s0.sp - 688#64) ↦₆₄ w0) ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur1.length
          ⟨some vn1, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304)
      limit 2#32 .varint hcur1_key hlim_dv (by decide) (by decide)
      hcur1_le hcur1_suf hlen_bound hfit_nil hs0A
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
      (by rw [hP]; sep_ac_rfl) ?_
    intro s1 P1 hlt_dv hdv_le hdv_suf hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1
      hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hP1
    have hle_dv1 : rest_dv.length ≤ cur1.length := Nat.le_of_lt hlt_dv
    subst hP1
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, protoWireTypeToCodec,
      WireType.toNat] at hpc1 hx0_1 hx1_1 ⊢
    change s1.readReg64 .x1 = 2#64 at hx1_1
    change s1.readReg64 .x0 = 0#64 at hx0_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1328#64)
    wp_steps 6
    refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
      (a := s0.sp - 1040#64) (rem1 := cur1.length) (rem2 := rest_dv.length)
      (st := ⟨some vn1, optCh, inner⟩) hle_dv1) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hx1_1]) (by simp only [arm64_norm, hrun1])
    have hdv_eq : decodeVarint rest_dv = some (dir.signExtend 64, cur2) :=
      e2a_decodeVarint_encodeVarint (dir.signExtend 64) cur2
    refine decodeState_vn_tag2_539cc_cl_placed_ofEnv
      (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := v27)
      hc x st0 st w0 vn1 optCh inner rest_dv limit .varint
      hdv_le hdv_suf hlen_bound
      (fun hne => absurd rfl hne)
      (fun _ hnone => by rw [hdv_eq] at hnone; cases hnone)
      s0 _ _ R post hpost
      (fun _ evs hdv_e => by
        rw [e2a_decodeVarint2Env_eq_nil hdv_eq hdv_e]
        exact hfit_nil [] rfl)
      (fun _ _ hnone => by rw [hdv_eq] at hnone; cases hnone)
      (fun _ _ _ hnone => by rw [hdv_eq] at hnone; cases hnone)
      (fun _ _ _ _ _ hnone => by rw [hdv_eq] at hnone; cases hnone)
      (fun hne => absurd rfl hne)
      (fun hne => absurd rfl hne)
      (fun hne => absurd rfl hne)
      (fun hne => absurd rfl hne)
      hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx1_1])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, Reg.x0, hx0_1, WireType.toNat])
      (by simp only [arm64_norm, hx19_1]) (by simp only [arm64_norm, hx20_1])
      (by simp only [arm64_norm, hx21_1]) (by simp only [arm64_norm, hx22_1])
      (by simp only [arm64_norm, hx23_1]) (by simp only [arm64_norm, hx24_1])
      (by simp only [arm64_norm, hx25_1]) (by simp only [arm64_norm, hx26_1])
      (by simp only [arm64_norm, hx27_1]) (by simp only [arm64_norm, hx28_1])
      (by simp only [arm64_norm, hx29_1])
      (by dsimp only [decodeStateLoopCommonPlaced]; simp only [wp_norm, arm64_norm]; sep_ac_rfl)
      ?_
    intro v' rest2 evs_dv sf P' _ hdv2 hevs_dv hle2 hsuf2
      hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
      hx29_2 hP'
    rw [hdv_eq] at hdv2
    cases hdv2
    have hevs_nil := e2a_decodeVarint2Env_eq_nil hdv_eq hevs_dv
    subst hevs_nil
    have htr_dir : (dir.signExtend 64).truncate 32 = dir := truncate32_signExtend64 dir
    rw [htr_dir, M.stepEvents_nil] at hP'
    exact hdone sf P' (Nat.le_trans hle2 hdv_le) (suffix_trans hdv_le hdv_suf hle2 hsuf2)
      hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
      hx29_2 hP'

/-- Tag 3 (`min_version : i32`) from `+1252` to `+1252` (`evs = []`, `st` unchanged). -/
private theorem e2a_vn_tag3_step_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (vn2 : VersionNegotiationPB) (hver0 : vn2.minVersion = 0#32)
    (minVer : BitVec 32) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    {cur2 cur3 : Bytes} (limit : Nat)
    (hcur2_eq : cur2 = encodeInt32Field 3#32 minVer ++ cur3)
    (hlim_le : limit ≤ cur3.length)
    (hcur2_le : cur2.length ≤ x.st.bytes.length)
    (hcur2_suf : IsDropSuffix x.st.bytes cur2)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hfit_nil : FitsEnv M lim st (fun evs => evs = []))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1252#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur2 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur2.length
        ⟨some vn2, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (sf : State) (P' : SepProp),
      cur3.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes cur3 →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur3 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur3.length
          ⟨some { vn2 with minVersion := minVer }, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  by_cases hv0 : minVer = 0#32
  · subst hv0
    have hcur_id : cur2 = cur3 := by
      rw [hcur2_eq, e2a_encodeInt32Field_of_zero, List.nil_append]
    subst hcur_id
    have hvn_id : ({ vn2 with minVersion := 0#32 } : VersionNegotiationPB) = vn2 := by
      cases vn2; dsimp only at hver0 ⊢; subst hver0; rfl
    rw [← hvn_id] at hP
    exact hdone s P hcur2_le hcur2_suf hpc hrun hsp htr
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP
  · have hcur2_key := e2a_encodeInt32Field_append_of_ne 3#32 minVer hv0 cur3
    rw [← hcur2_eq] at hcur2_key
    let rest_dv := encodeVarint (minVer.signExtend 64) ++ cur3
    have hlim_dv : limit ≤ rest_dv.length := by
      dsimp only [rest_dv]; rw [List.length_append]; omega
    refine e2a_vn_key_decode_cl (PreEnv := PreEnv) (PostEnv := PostEnv)
      hc x st0 st
      (((s0.sp - 688#64) ↦₆₄ w0) ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur2.length
          ⟨some vn2, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304)
      limit 3#32 .varint hcur2_key hlim_dv (by decide) (by decide)
      hcur2_le hcur2_suf hlen_bound hfit_nil hs0A
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
      (by rw [hP]; sep_ac_rfl) ?_
    intro s1 P1 hlt_dv hdv_le hdv_suf hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1
      hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hP1
    have hle_dv2 : rest_dv.length ≤ cur2.length := Nat.le_of_lt hlt_dv
    subst hP1
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, protoWireTypeToCodec,
      WireType.toNat] at hpc1 hx0_1 hx1_1 ⊢
    change s1.readReg64 .x1 = 3#64 at hx1_1
    change s1.readReg64 .x0 = 0#64 at hx0_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1432#64)
    wp_steps 4
    refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
      (a := s0.sp - 1040#64) (rem1 := cur2.length) (rem2 := rest_dv.length)
      (st := ⟨some vn2, optCh, inner⟩) hle_dv2) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hx1_1]) (by simp only [arm64_norm, hrun1])
    have hdv_eq : decodeVarint rest_dv = some (minVer.signExtend 64, cur3) :=
      e2a_decodeVarint_encodeVarint (minVer.signExtend 64) cur3
    refine decodeState_vn_tag3_53a34_cl_placed_ofEnv
      (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := v27)
      hc x st0 st w0 vn2 optCh inner rest_dv limit .varint
      hdv_le hdv_suf hlen_bound
      (fun hne => absurd rfl hne)
      (fun _ hnone => by rw [hdv_eq] at hnone; cases hnone)
      s0 _ _ R post hpost
      (fun _ evs hdv_e => by
        rw [e2a_decodeVarint2Env_eq_nil hdv_eq hdv_e]
        exact hfit_nil [] rfl)
      (fun _ _ hnone => by rw [hdv_eq] at hnone; cases hnone)
      (fun _ _ _ hnone => by rw [hdv_eq] at hnone; cases hnone)
      (fun _ _ _ _ _ hnone => by rw [hdv_eq] at hnone; cases hnone)
      (fun hne => absurd rfl hne)
      (fun hne => absurd rfl hne)
      (fun hne => absurd rfl hne)
      (fun hne => absurd rfl hne)
      hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx1_1])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, Reg.x0, hx0_1, WireType.toNat])
      (by simp only [arm64_norm, hx19_1]) (by simp only [arm64_norm, hx20_1])
      (by simp only [arm64_norm, hx21_1]) (by simp only [arm64_norm, hx22_1])
      (by simp only [arm64_norm, hx23_1]) (by simp only [arm64_norm, hx24_1])
      (by simp only [arm64_norm, hx25_1]) (by simp only [arm64_norm, hx26_1])
      (by simp only [arm64_norm, hx27_1]) (by simp only [arm64_norm, hx28_1])
      (by simp only [arm64_norm, hx29_1])
      (by dsimp only [decodeStateLoopCommonPlaced]; simp only [wp_norm, arm64_norm]; sep_ac_rfl)
      ?_
    intro v' rest2 evs_dv sf P' _ hdv2 hevs_dv hle2 hsuf2
      hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
      hx29_2 hP'
    rw [hdv_eq] at hdv2
    cases hdv2
    have hevs_nil := e2a_decodeVarint2Env_eq_nil hdv_eq hevs_dv
    subst hevs_nil
    have htr_ver : (minVer.signExtend 64).truncate 32 = minVer := truncate32_signExtend64 minVer
    rw [htr_ver, M.stepEvents_nil] at hP'
    exact hdone sf P' (Nat.le_trans hle2 hdv_le) (suffix_trans hdv_le hdv_suf hle2 hsuf2)
      hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
      hx29_2 hP'

/-- Canonical Tag 4 call site `+1228 -> lsmpl.base 294 -> +1252` (`evs = []`, `st` unchanged). -/
private theorem e2a_vn_tag4_call_53968_canonical_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (authKey : Bytes) (dir minVer : BitVec 32)
    (cp : ChainParamsPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    {rest_cp rest : Bytes} (limit : Nat)
    (hrest_cp_eq : rest_cp = e2a_lenPrefixed (ChainParamsPB.encodeRaw cp) rest)
    (hcp_le : rest_cp.length ≤ x.st.bytes.length)
    (hcp_suf : IsDropSuffix x.st.bytes rest_cp)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hfit_nil : FitsEnv M lim st (fun evs => evs = []))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = 2#64)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest_cp ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest_cp.length
        ⟨some ⟨authKey, dir, minVer, some default⟩, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (sf : State) (P' : SepProp),
      rest.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes rest →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest.length
          ⟨some ⟨authKey, dir, minVer, some cp⟩, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hcp_call := e2a_chainParamsMerge_cl_placed_ok_canonical hc
  subst hP
  rw [sliceCursorAfter_eq_split hcp_le hcp_suf,
    protoPqRatchetStateCapOkAt_some_vn_eq, optChainParamsPBAt_some_eq]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced]
    at hpc hcp_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 294)
  wp_steps_sync_pool (lsmpl.base 294)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  have hx22_1c : s0.sp - 1040#64 + 28#64 = s0.sp - 1012#64 := by bv_omega
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  have hmm_cp :
      (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage ChainParamsPB.mergeField
        .lengthDelimited default rest_cp 99).toOption = some (cp, rest) := by
    rw [hrest_cp_eq, e2a_mergeMessage_chainParams_encode cp rest]
    rfl
  have hdom_cp :
      E2aTightChainParamsClPlacedBudget.e2a_ChainParamsCanonicalDom
        ⟨.lengthDelimited, s0.sp - 1012#64, default, s0.sp - 336#64, s0.sp - 1056#64,
          x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest_cp.length), rest_cp⟩ :=
    ⟨rfl, rfl, cp, rest, hrest_cp_eq⟩
  refine SepWPpIPlaced.call_chainParamsMerge_cl_ofEnv hcp_call .lengthDelimited
    (s0.sp - 1012#64) default (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest_cp.length)) rest_cp st
    (ret_pc := (blkPl_325).base + 1240#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx0]; try rfl)
    (hx1 := by simp only [wp_norm, arm64_norm, hx22, hx22_1c])
    (hx2 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hfits := e2a_fitsEnv_chainParams_canonical st hdom_cp)
    (hP := by sep_focus) ?_ ?_
  · intro s2 cp' rest2 evs_cp hcp_ok hevs_cp hle2 hsuf2 hpc2 hrun2 hsp2 htr2 hcs2 hx0_0
    change (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage ChainParamsPB.mergeField
      .lengthDelimited default rest_cp 99).toOption = some (cp', rest2) at hcp_ok
    rw [hmm_cp] at hcp_ok
    cases hcp_ok
    have hevs_nil := e2a_chainParamsCanonicalPostEnv_eq_nil hdom_cp hevs_cp
    subst hevs_nil
    simp only [M.stepEvents_nil]
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2,
      hx28_2, hx29_2, hvregs_2⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2
    simp only [arm64_norm, wp_norm] at hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1252#64)
    wp_steps_sync_pool ((blkPl_325).base + 1252#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hcp_le hcp_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (vecU8CapOkAt_mono (A := A.repAlloc) (v := s0.sp - 1040#64)
      (rem1 := rest_cp.length) (rem2 := rest.length) (bs := authKey) hle2)
      (by sep_focus) ?_
    refine SepWP.fold (optChainPBCapOkAt_mono (A := A.repAlloc) (a := s0.sp - 992#64)
      (rem1 := rest_cp.length) (rem2 := rest.length) (opt := optCh) hle2)
      (by sep_focus) ?_
    refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
      (a := s0.sp - 912#64) (rem1 := rest_cp.length) (rem2 := rest.length) (opt := inner) hle2)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2])
    exact hdone _ _ (Nat.le_trans hle2 hcp_le) (suffix_trans hcp_le hcp_suf hle2 hsuf2)
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun2]) (by simp only [wp_norm, arm64_norm, hsp2])
      (by simp only [wp_norm, arm64_norm, htr2])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by
        rw [protoPqRatchetStateCapOkAt_some_vn_eq, optChainParamsPBAt_some_eq]
        dsimp only [decodeStateLoopCommonPlaced]
        sep_ac_rfl)
  · intro _ _ _ _ hcp_none
    change (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage ChainParamsPB.mergeField
      .lengthDelimited default rest_cp 99).toOption = none at hcp_none
    rw [hmm_cp] at hcp_none
    cases hcp_none

/-- Canonical Tag 4 init `+1372 -> +1380 -> +1228` (`none` -> `some default`) followed by
`e2a_vn_tag4_call_53968_canonical_cl`. -/
private theorem e2a_vn_tag4_539f8_canonical_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (authKey : Bytes) (dir minVer : BitVec 32)
    (cp : ChainParamsPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    {rest_cp rest : Bytes} (limit : Nat)
    (hrest_cp_eq : rest_cp = e2a_lenPrefixed (ChainParamsPB.encodeRaw cp) rest)
    (hcp_le : rest_cp.length ≤ x.st.bytes.length)
    (hcp_suf : IsDropSuffix x.st.bytes rest_cp)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hfit_nil : FitsEnv M lim st (fun evs => evs = []))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1372#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = 2#64)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest_cp ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest_cp.length
        ⟨some ⟨authKey, dir, minVer, none⟩, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (sf : State) (P' : SepProp),
      rest.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes rest →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest.length
          ⟨some ⟨authKey, dir, minVer, some cp⟩, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  rw [protoPqRatchetStateCapOkAt_some_vn_eq]
  have hnone_eq : optChainParamsPBAt (s0.sp - 1016#64) none =
      ((s0.sp - 1016#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 1016#64 + 4#64) 8 := rfl
  rw [hnone_eq]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced] at hpc ⊢
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1380#64)
  wp_steps_sync_pool ((blkPl_325).base + 1380#64)
  try simp only [State.setMem_setMem]
  refine SepWP.fold (optChainParamsPBAt_none_to_init (s0.sp - 1016#64)) (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPpIPlaced.exists_elim; intro w0_init
  apply SepWPpIPlaced.exists_elim; intro w1_init
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1228#64)
  wp_steps_sync_pool ((blkPl_325).base + 1228#64)
  try simp only [State.setMem_setMem]
  have hinit : ((s0.sp - 1016#64) ↦₆₄ 1#64) ∗ ((s0.sp - 1008#64) ↦₃₂ 0#32) ⊢
      optChainParamsPBAt (s0.sp - 1016#64) (some default) := by
    have h1 := optChainParamsPBAt_some_default_init (s0.sp - 1016#64)
    have ha8 : s0.sp - 1016#64 + 8#64 = s0.sp - 1008#64 := by bv_omega
    rw [ha8] at h1
    exact h1
  refine SepWP.fold hinit (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  exact e2a_vn_tag4_call_53968_canonical_cl (PreEnv := PreEnv) (PostEnv := PostEnv)
    hc x st0 st w0 authKey dir minVer cp optCh inner limit
    hrest_cp_eq hcp_le hcp_suf hlen_bound hfit_nil hs0A
    (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm, htr]) (by simp only [wp_norm, arm64_norm, hx0])
    (by simp only [wp_norm, arm64_norm, hx19]) (by simp only [wp_norm, arm64_norm, hx20])
    (by simp only [wp_norm, arm64_norm, hx21]) (by simp only [wp_norm, arm64_norm, hx22])
    (by simp only [wp_norm, arm64_norm, hx23]) (by simp only [wp_norm, arm64_norm, hx24])
    (by simp only [wp_norm, arm64_norm, hx25]) (by simp only [wp_norm, arm64_norm, hx26])
    (by simp only [wp_norm, arm64_norm, hx27]) (by simp only [wp_norm, arm64_norm, hx28])
    (by simp only [wp_norm, arm64_norm, hx29])
    (by
      rw [protoPqRatchetStateCapOkAt_some_vn_eq]
      dsimp only [decodeStateLoopCommonPlaced]
      try sep_ac_rfl)
    hdone

/-- Tag 4 (`chain_params : Option ChainParams`) from `+1252` to `+1252` via
`e2a_chainParamsMerge_cl_placed_ok_canonical` (`evs = []`, `st` unchanged). -/
private theorem e2a_vn_tag4_step_cl [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (authKey : Bytes) (dir minVer : BitVec 32)
    (optCp : Option ChainParamsPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    {cur3 rest : Bytes} (limit : Nat)
    (hcur3_eq : cur3 = encodeOptMessage ChainParamsPB.encodeRaw 4#32 optCp ++ rest)
    (hlim_le : limit ≤ rest.length)
    (hcur3_le : cur3.length ≤ x.st.bytes.length)
    (hcur3_suf : IsDropSuffix x.st.bytes cur3)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hfit_nil : FitsEnv M lim st (fun evs => evs = []))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1252#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur3 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur3.length
        ⟨some ⟨authKey, dir, minVer, none⟩, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (sf : State) (P' : SepProp),
      rest.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes rest →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest.length
          ⟨some ⟨authKey, dir, minVer, optCp⟩, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  cases optCp with
  | none =>
    have hcur_id : cur3 = rest := by
      simpa [encodeOptMessage] using hcur3_eq
    subst hcur_id
    exact hdone s P hcur3_le hcur3_suf hpc hrun hsp htr
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP
  | some cp =>
    let rest_cp := e2a_lenPrefixed (ChainParamsPB.encodeRaw cp) rest
    have hcur3_key : cur3 = encodeKey 4#32 .lengthDelimited ++ rest_cp := by
      rw [hcur3_eq]
      dsimp only [encodeOptMessage, encodeMessage, rest_cp, e2a_lenPrefixed]
      simp only [List.append_assoc]
    have hlim_cp : limit ≤ rest_cp.length := by
      dsimp only [rest_cp, e2a_lenPrefixed]
      rw [List.length_append, List.length_append]
      omega
    refine e2a_vn_key_decode_cl (PreEnv := PreEnv) (PostEnv := PostEnv)
      hc x st0 st
      (((s0.sp - 688#64) ↦₆₄ w0) ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur3.length
          ⟨some ⟨authKey, dir, minVer, none⟩, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304)
      limit 4#32 .lengthDelimited hcur3_key hlim_cp (by decide) (by decide)
      hcur3_le hcur3_suf hlen_bound hfit_nil hs0A
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
      (by rw [hP]; sep_ac_rfl) ?_
    intro s1 P1 hlt_cp hcp_le hcp_suf hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1
      hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hP1
    have hle_cp3 : rest_cp.length ≤ cur3.length := Nat.le_of_lt hlt_cp
    subst hP1
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, protoWireTypeToCodec,
      WireType.toNat] at hpc1 hx0_1 hx1_1 ⊢
    change s1.readReg64 .x1 = 4#64 at hx1_1
    change s1.readReg64 .x0 = 2#64 at hx0_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1372#64)
    wp_steps 6
    refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
      (a := s0.sp - 1040#64) (rem1 := cur3.length) (rem2 := rest_cp.length)
      (st := ⟨some ⟨authKey, dir, minVer, none⟩, optCh, inner⟩) hle_cp3) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hx1_1]) (by simp only [arm64_norm, hrun1])
    exact e2a_vn_tag4_539f8_canonical_cl (PreEnv := PreEnv) (PostEnv := PostEnv)
      hc x st0 st w0 authKey dir minVer cp optCh inner limit
      rfl hcp_le hcp_suf hlen_bound hfit_nil hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx1_1])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, hx0_1])
      (by simp only [arm64_norm, hx19_1]) (by simp only [arm64_norm, hx20_1])
      (by simp only [arm64_norm, hx21_1]) (by simp only [arm64_norm, hx22_1])
      (by simp only [arm64_norm, hx23_1]) (by simp only [arm64_norm, hx24_1])
      (by simp only [arm64_norm, hx25_1]) (by simp only [arm64_norm, hx26_1])
      (by simp only [arm64_norm, hx27_1]) (by simp only [arm64_norm, hx28_1])
      (by simp only [arm64_norm, hx29_1])
      (by dsimp only [decodeStateLoopCommonPlaced]; simp only [wp_norm, arm64_norm]; sep_ac_rfl)
      hdone

/-! ## 5. Canonical Outer Field 1 (`PqRatchetState::version_negotiation`, `+116 -> +1576`) -/

/-- Canonical outer Field 1 (`PqRatchetState.versionNegotiation = some vn`, `vn.authKey.length ≤ 32`)
stepping from `+116` (`curSt = ⟨none, optCh, inner⟩`, `cur = encodeMessage VersionNegotiationPB.encodeRaw 1#32 vn ++ rest`)
to `+1576` (`curSt' = ⟨some vn, optCh, inner⟩`, `rest`), emitting `evs_vn` under `SpqrTightEvs 2 1476 32`. -/
theorem e2a_vn_outer_field1_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (hkey_le : vn.authKey.length ≤ 32)
    (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    {cur rest : Bytes}
    (hcur_eq : cur = encodeMessage VersionNegotiationPB.encodeRaw 1#32 vn ++ rest)
    (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hFit : FitsEnv M lim st (SpqrTightEvs 2 1476 32))
    {s0 s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 116#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64) (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64) (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64) (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27) (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length
        ⟨none, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (evs_vn : List AllocEvent) (sf : State) (P' : SepProp),
      SpqrTightEvs 2 1476 32 evs_vn →
      rest.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes rest →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 rest.length →
      sf.readReg64 .x21 = 0x8000000000000006#64 → sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 → sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 → sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 → sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest.length
          ⟨some vn, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_vn st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  let raw := VersionNegotiationPB.encodeRaw vn
  let rest1 := e2a_lenPrefixed raw rest
  have hcur_key : cur = encodeKey 1#32 .lengthDelimited ++ rest1 := by
    rw [hcur_eq]
    dsimp only [encodeMessage, raw, rest1, e2a_lenPrefixed]
    simp only [List.append_assoc]
  have hfit_nil0 : FitsEnv M lim st (fun evs => evs = []) :=
    fun evs he => by subst he; exact hFit [] (SpqrTightEvs.nil 2 1476 32)
  refine e2a_outer_key_decode_cl (PreEnv := PreEnv) (PostEnv := PostEnv)
    hc.toDecodeStateCalleeContractsClPlaced x st0 st
    (((s0.sp - 688#64) ↦₆₄ w0) ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length
        ⟨none, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304)
    1#32 .lengthDelimited hcur_key (by decide) (by decide)
    hcur_le hcur_suf hlen_bound hfit_nil0 hs0A
    hpc hrun hsp htr hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 P1 hlt1 hrest1_le hrest1_suf hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1
    hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hP1
  have hle1_cur : rest1.length ≤ cur.length := Nat.le_of_lt hlt1
  have hsp1A : s1.spAligned = true := by
    rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
  subst hP1
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, protoWireTypeToCodec,
    WireType.toNat] at hpc1 hx0_1 hx1_1 ⊢
  change s1.readReg64 .x1 = 1#64 at hx1_1
  change s1.readReg64 .x0 = 2#64 at hx0_1
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 184#64)
  wp_steps 6
  refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
    (a := s0.sp - 1040#64) (rem1 := cur.length) (rem2 := rest1.length)
    (st := ⟨none, optCh, inner⟩) hle1_cur) (by sep_focus) ?_
  unfold protoPqRatchetStateCapOkAt optVersionNegotiationPBCapOkAt
  dsimp only
  have ha48 : s0.sp - 1040#64 + 48#64 = s0.sp - 992#64 := by bv_omega
  have ha128 : s0.sp - 1040#64 + 128#64 = s0.sp - 912#64 := by bv_omega
  rw [ha48, ha128]
  refine SepWP.fold (optVersionNegotiationPB_none_split40 (s0.sp - 1040#64)) (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm, hx1_1])
    (by simp only [wp_norm, arm64_norm, hrun1])
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPpIPlaced.exists_elim; intro w1
  apply SepWPpIPlaced.exists_elim; intro w2
  apply SepWPpIPlaced.exists_elim; intro w3
  apply SepWPpIPlaced.exists_elim; intro w4
  have hdv_call := hc.toDecodeStateCalleeContractsClPlaced.decodeVarint2
  have hraw_lt64 : raw.length < 2 ^ 64 := by
    have : rest1.length = (encodeVarint (BitVec.ofNat 64 raw.length)).length + raw.length +
        rest.length := by
      dsimp only [rest1, e2a_lenPrefixed]
      rw [List.length_append, List.length_append]
    omega
  have ⟨hdv_len, hlen64_nat⟩ := e2a_decodeVarint_lenPrefixed (rest := rest) hraw_lt64
  refine sync_pool_at A lim st x s0 s1 (by simp only [wp_norm, arm64_norm]) fun s_mid hcomm hs_mid => ?_
  subst hs_mid
  rw [hcomm]
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
  dsimp only [decodeStateLoopCommonPlaced]
  wp_steps_sync_pool ((blkPl_325).base + 216#64)
  try simp only [State.setMem_setMem]
  refine SepWP.fold (versionNegotiationZeroCapAt_default_init A.repAlloc (s0.sp - 1040#64))
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (sliceCursorAfter_eq_split hrest1_le hrest1_suf))
    (by sep_focus) ?_
  wp_steps_sync_pool (lsmpl.base 291)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm, hx0_1])
    (by simp only [wp_norm, arm64_norm, hrun1])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  have hsp1048 : s0.sp - 1056#64 + 8#64 = s0.sp - 1048#64 := by bv_omega
  refine e2a_call_decodeVarint2_some_cl hdv_call
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) st hdv_len
    (ret_pc := (blkPl_325).base + 232#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun1])
    (hsp := by simp only [wp_norm, arm64_norm, hsp1]) (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr1])
    (hx0 := by simp only [wp_norm, arm64_norm, hx29_1, hx29_f0])
    (hlen := by change rest1.length < 2 ^ 63; omega) (hfit_nil := hfit_nil0)
    (hP := by sep_focus) ?_
  intro s2 hlt2 hsuf2 hpc2 hrun2 hsp2 htr2 hcs2 hx0_0 hx1_len
  let cur0 := raw ++ rest
  have hle2 : cur0.length ≤ rest1.length := Nat.le_of_lt hlt2
  have hcur0_le : cur0.length ≤ x.st.bytes.length := Nat.le_trans hle2 hrest1_le
  have hcur0_suf : IsDropSuffix x.st.bytes cur0 := suffix_trans hrest1_le hrest1_suf hle2 hsuf2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2,
    hx28_2, hx29_2, hvregs_2⟩
  dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
    Reg.x28, Reg.x29] at hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  simp only [arm64_norm, wp_norm] at hx0_0 hx1_len hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2
  simp only [arm64_norm, wp_norm] at hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
  have hnot_lt_len : ¬ cur0.length < (BitVec.ofNat 64 raw.length).toNat := by
    rw [hlen64_nat]
    dsimp only [cur0]
    rw [List.length_append]
    omega
  have ⟨hult_len, hule_len⟩ := len_ult_of_ge hnot_lt_len (by omega)
  have hsub_lim := bv_len_sub_limit hnot_lt_len
  have hlim_eq : cur0.length - (BitVec.ofNat 64 raw.length).toNat = rest.length := by
    rw [hlen64_nat]
    dsimp only [cur0]
    rw [List.length_append]
    omega
  rw [hlim_eq] at hsub_lim
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1252#64)
  refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
    hrest1_le hrest1_suf hle2) (by sep_focus) ?_
  dsimp only [sliceCursorAfter]
  wp_steps_sync_pool ((blkPl_325).base + 1252#64)
  try simp only [State.setMem_setMem]
  refine SepWP.fold (optChainPBCapOkAt_mono (A := A.repAlloc) (a := s0.sp - 992#64)
    (rem1 := rest1.length) (rem2 := cur0.length) (opt := optCh) hle2) (by sep_focus) ?_
  refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
    (a := s0.sp - 912#64) (rem1 := rest1.length) (rem2 := cur0.length) (opt := inner) hle2)
    (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm, hx0_0, hult_len, hule_len])
    (by simp only [wp_norm, arm64_norm, hrun2])
  let cur3 := encodeOptMessage ChainParamsPB.encodeRaw 4#32 vn.chainParams ++ rest
  let cur2 := encodeInt32Field 3#32 vn.minVersion ++ cur3
  let cur1 := encodeInt32Field 2#32 vn.direction ++ cur2
  have hcur0_split : cur0 = encodeBytesField 1#32 vn.authKey ++ cur1 := by
    dsimp only [cur0, raw, VersionNegotiationPB.encodeRaw, cur1, cur2, cur3]
    simp only [List.append_assoc]
  have hlim_cur3 : rest.length ≤ cur3.length := by
    dsimp only [cur3]; rw [List.length_append]; omega
  have hlim_cur2 : rest.length ≤ cur2.length := by
    dsimp only [cur2]; rw [List.length_append]; omega
  have hlim_cur1 : rest.length ≤ cur1.length := by
    dsimp only [cur1]; rw [List.length_append]; omega
  refine e2a_vn_tag1_step_cl (v27 := v27) (PreEnv := PreEnv) (PostEnv := PostEnv)
    hc x st0 st w0 vn.authKey hkey_le optCh inner (cur0 := cur0) (cur1 := cur1) rest.length
    hcur0_split hlim_cur1 hcur0_le hcur0_suf hlen_bound hFit hs0A
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hult_len, hule_len])
    (by simp only [arm64_norm, hrun2]) (by simp only [arm64_norm, hsp2])
    (by simp only [arm64_norm, htr2])
    (by dsimp only [Reg.x19]; simp only [arm64_norm, *])
    (by dsimp only [Reg.x20]; simp only [arm64_norm, hsub_lim, *])
    (by dsimp only [Reg.x21]; simp only [arm64_norm, *])
    (by dsimp only [Reg.x22]; simp only [arm64_norm, *])
    (by dsimp only [Reg.x23]; simp only [arm64_norm, *])
    (by dsimp only [Reg.x24]; simp only [arm64_norm, *])
    (by dsimp only [Reg.x25]; simp only [arm64_norm, *])
    (by dsimp only [Reg.x26]; simp only [arm64_norm, *])
    (by dsimp only [Reg.x27]; simp only [arm64_norm, *])
    (by dsimp only [Reg.x28]; simp only [arm64_norm, *])
    (by dsimp only [Reg.x29]; simp only [arm64_norm, *])
    (by
      dsimp only [cur0, raw, decodeStateLoopCommonPlaced, sliceCursorAfter]
      rw [hsp1048]
      simp only [wp_norm, arm64_norm]
      sep_ac_rfl) ?_
  intro evs_t1 s3 P3 htight_t1 hcur1_le hcur1_suf
    hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3
    hx29_3 hP3
  have hfit_nil1 : FitsEnv M lim (M.stepEvents evs_t1 st) (fun evs => evs = []) := by
    have hrem : FitsEnv M lim (M.stepEvents evs_t1 st) (SpqrTightEvs 0 0 0) :=
      e2a_fitsEnv_tight_split (n₂ := 0) (c₂ := 0) (r₂ := 0) htight_t1 hFit
    intro evs he; subst he; exact hrem [] (SpqrTightEvs.nil 0 0 0)
  refine e2a_vn_tag2_step_cl (PreEnv := PreEnv) (PostEnv := PostEnv)
    hc.toDecodeStateCalleeContractsClPlaced x st0 (M.stepEvents evs_t1 st) w0
    { (default : VersionNegotiationPB) with authKey := vn.authKey }
    (by rw [versionNegotiationPB_default_eq])
    vn.direction optCh inner rest.length rfl hlim_cur2 hcur1_le hcur1_suf hlen_bound
    hfit_nil1 hpost hs0A
    hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3
    hx29_3 hP3 ?_
  intro s4 P4 hcur2_le hcur2_suf
    hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4
    hx29_4 hP4
  refine e2a_vn_tag3_step_cl (PreEnv := PreEnv) (PostEnv := PostEnv)
    hc.toDecodeStateCalleeContractsClPlaced x st0 (M.stepEvents evs_t1 st) w0
    { (default : VersionNegotiationPB) with authKey := vn.authKey, direction := vn.direction }
    (by rw [versionNegotiationPB_default_eq])
    vn.minVersion optCh inner rest.length rfl hlim_cur3 hcur2_le hcur2_suf hlen_bound
    hfit_nil1 hpost hs0A
    hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4
    hx29_4 hP4 ?_
  intro s5 P5 hcur3_le hcur3_suf
    hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5
    hx29_5 hP5
  have hvn3_eq :
      ({ (default : VersionNegotiationPB) with
        authKey := vn.authKey, direction := vn.direction, minVersion := vn.minVersion } :
          VersionNegotiationPB) = ⟨vn.authKey, vn.direction, vn.minVersion, none⟩ := by
    rw [versionNegotiationPB_default_eq]
  rw [hvn3_eq] at hP5
  refine e2a_vn_tag4_step_cl (PreEnv := PreEnv) (PostEnv := PostEnv)
    hc.toDecodeStateCalleeContractsClPlaced x st0 (M.stepEvents evs_t1 st) w0
    vn.authKey vn.direction vn.minVersion vn.chainParams optCh inner rest.length
    rfl (Nat.le_refl _) hcur3_le hcur3_suf hlen_bound hfit_nil1 hs0A
    hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5
    hx29_5 hP5 ?_
  intro s6 P6 hrest_le hrest_suf
    hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hx21_6 hx22_6 hx23_6 hx24_6 hx25_6 hx26_6 hx27_6 hx28_6
    hx29_6 hP6
  have hvn_fin : (⟨vn.authKey, vn.direction, vn.minVersion, vn.chainParams⟩ :
      VersionNegotiationPB) = vn := by
    cases vn; rfl
  rw [hvn_fin] at hP6
  have ⟨hult_ex, hule_ex, hbeq_ex⟩ := cmp_len_limit_of_eq (rfl : rest.length = rest.length)
  have hsp6A : s6.spAligned = true := by
    rw [State.spAligned, hsp6]; exact sp_sub_1392_aligned s0 hs0A
  subst hP6
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, sliceCursorAfter] at hpc6 ⊢
  apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1576#64)
  wp_steps 4
  apply SepWP.done (by simp only [arm64_norm, hult_ex, hule_ex, hbeq_ex])
    (by simp only [arm64_norm, hrun6])
  exact hdone evs_t1 _ _ htight_t1 hrest_le hrest_suf
    (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult_ex, hule_ex, hbeq_ex])
    (by simp only [arm64_norm, hrun6]) (by simp only [arm64_norm, hsp6])
    (by simp only [arm64_norm, htr6])
    (by simp only [arm64_norm, hx19_6]) (by simp only [arm64_norm, hx20_6])
    (by simp only [arm64_norm, hx21_6]) (by simp only [arm64_norm, hx22_6])
    (by simp only [arm64_norm, hx23_6]) (by simp only [arm64_norm, hx24_6])
    (by simp only [arm64_norm, hx25_6]) (by simp only [arm64_norm, hx26_6])
    (by simp only [arm64_norm, hx27_6]) (by simp only [arm64_norm, hx28_6])
    (by simp only [arm64_norm, hx29_6])
    (by
      dsimp only [sliceCursorAfter, decodeStateLoopCommonPlaced]
      simp only [wp_norm, arm64_norm]
      try sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStateVnPlacedBudget
