/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationClPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Code-Loaded `VersionNegotiationPB` Tag Body Helpers (Block `325`)

Re-exports Tag 1..3 helpers from `VersionNegotiationClPlacedBudgetAux` and proves budget-threaded
code-loaded Tag 4 (`chain_params`, `+1228`, `+1372`) and `skip_field` (`+1392`) body lemmas.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationClPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkLib_eq_325 blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalProtoCodec (WireType skipField)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join)
open CryptoVerification.SpqrV1.ProtoRepr (optChainParamsPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge (codecWireTypeToProto)
open CryptoVerification.LibsignalSpqrV1
  (ChainPB ChainParamsPB PqRatchetState VersionNegotiationPB spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg
   errFrame_parts_fold optChainPBCapOkAt_entails_optChainPBAt optChainPBCapOkAt_mono
   optChainParamsPBAt_none_to_init optChainParamsPBAt_some_default_init optChainParamsPBAt_some_eq
   optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt
   optProtoPqRatchetInnerCapOkAt_mono protoPqRatchetStateAt_some_vn_eq protoPqRatchetStateCapOkAt
   protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt protoPqRatchetStateCapOkAt_mono
   protoPqRatchetStateCapOkAt_some_vn_eq sp_sub_1392_aligned vecU8CapOkAt_entails_rustBytesVecAt
   vecU8CapOkAt_mono)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorPushEnv)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (SkipField3Env)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (ChainParamsMergeEnv ChainParamsMergePostEnv DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget (decodeStateErrFramePlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced
   decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitClPlacedBudget
  (decodeState_err_push_53dcc_cl_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced decodeStateLoopCommonPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonClPlacedBudget
  (SepWPpIPlaced.call_chainParamsMerge_cl SepWPpIPlaced.call_skipField3_cl)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrClPlacedBudget
  (decodeState_err_push_53da4_cl_placed_ofEnv)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationClPlacedBudgetAux
  (decodeState_vn_tag1_53a20_cl_placed_ofEnv decodeState_vn_tag1_53a20_cl_placed
   decodeState_vn_tag2_539cc_cl_placed_ofEnv decodeState_vn_tag2_539cc_cl_placed)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationClPlacedBudgetAux
  (decodeState_vn_tag3_53a34_cl_placed_ofEnv decodeState_vn_tag3_53a34_cl_placed)

/-- Envelope-parameterized call helper at `+1228..+1248` for Tag 4 (`chain_params`) of `VersionNegotiation`. -/
theorem decodeState_vn_tag4_call_53968_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (cp : ChainParamsPB)
    (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt) cp rest1 99).toOption =
        none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hfits_cp : FitsEnv M lim st
      (ChainParamsMergeEnv ⟨iwt, s0.sp - 1012#64, cp, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩))
    (hfits_err1 : ∀ n evs_cp,
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt) cp rest1 99).toOption =
        none →
      n ≤ 1 →
      ChainParamsMergePostEnv ⟨iwt, s0.sp - 1012#64, cp, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_cp →
      FitsEnv M lim (M.stepEvents evs_cp st) (DecodeErrorPushEnv n))
    (hfits_err2 : ∀ n evs_cp evs_p1,
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt) cp rest1 99).toOption =
        none →
      n ≤ 1 →
      ChainParamsMergePostEnv ⟨iwt, s0.sp - 1012#64, cp, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_cp →
      DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_cp st)) (DecodeErrorPushEnv (n + 1)))
    (henv_err : ∀ n evs_cp evs_p1 evs_p2 evs_f,
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt) cp rest1 99).toOption =
        none →
      n ≤ 1 →
      ChainParamsMergePostEnv ⟨iwt, s0.sp - 1012#64, cp, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_cp →
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_cp st))))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨some { vn with chainParams := some cp }, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (cp' : ChainParamsPB) (rest2 : List (BitVec 8)) (evs_cp : List AllocEvent)
        (sf : State) (P' : SepProp),
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt) cp rest1 99).toOption =
        some (cp', rest2) →
      ChainParamsMergePostEnv ⟨iwt, s0.sp - 1012#64, cp, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_cp →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨some { vn with chainParams := some cp' }, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_cp st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hcp_call := hc.chainParamsMerge
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf,
    protoPqRatchetStateCapOkAt_some_vn_eq, optChainParamsPBAt_some_eq]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced] at hpc hcp_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 294)
  wp_steps_sync_pool (lsmpl.base 294)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  have hx22_1c : s0.sp - 1040#64 + 28#64 = s0.sp - 1012#64 := by bv_omega
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpIPlaced.call_chainParamsMerge_cl hcp_call iwt (s0.sp - 1012#64) cp
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1 st
    (ret_pc := (blkPl_325).base + 1240#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx0])
    (hx1 := by simp only [wp_norm, arm64_norm, hx22, hx22_1c])
    (hx2 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hfits := hfits_cp)
    (hP := by sep_focus) ?_ ?_
  · intro s1 cp' rest2 evs_cp hcp hevs_cp hle2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1252#64)
    wp_steps_sync_pool ((blkPl_325).base + 1252#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (vecU8CapOkAt_mono (A := A.repAlloc) (v := s0.sp - 1040#64)
      (rem1 := rest1.length) (rem2 := rest2.length) (bs := vn.authKey) hle2)
      (by sep_focus) ?_
    refine SepWP.fold (optChainPBCapOkAt_mono (A := A.repAlloc) (a := s0.sp - 992#64)
      (rem1 := rest1.length) (rem2 := rest2.length) (opt := optCh) hle2)
      (by sep_focus) ?_
    refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
      (a := s0.sp - 912#64) (rem1 := rest1.length) (rem2 := rest2.length) (opt := inner) hle2)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
    exact hloop cp' rest2 evs_cp _ _ hcp hevs_cp hle2 hsuf2
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun1]) (by simp only [wp_norm, arm64_norm, hsp1])
      (by simp only [wp_norm, arm64_norm, htr1])
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
  · intro s1 n cp' evs_cp hcp hevs_cp hpc1 hrun1 hsp1 htr1 hcs1 hx0_ne hn_le
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2312#64)
    wp_steps 1
    wp_if hcbnz
    · refine SepWP.fold (errFrame_parts_fold A.repAlloc x s0 hrest1_le hrest1_suf) (by sep_focus) ?_
      refine SepWP.fold (vecU8CapOkAt_entails_rustBytesVecAt A.repAlloc (s0.sp - 1040#64)
        rest1.length vn.authKey) (by sep_focus) ?_
      refine SepWP.fold (optChainPBCapOkAt_entails_optChainPBAt A.repAlloc (s0.sp - 992#64)
        rest1.length optCh) (by sep_focus) ?_
      refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt H_inner
        A.repAlloc (s0.sp - 912#64) rest1.length inner) (by sep_focus) ?_
      apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
      exact decodeState_err_push_53da4_cl_placed_ofEnv hc x st0
        (M.stepEvents evs_cp st) ⟨some { vn with chainParams := some cp' }, optCh, inner⟩
        w0 n s0 _ _ R post hpost (herr_of_none hcp) (by omega)
        (hfits_err1 n evs_cp hcp hn_le hevs_cp)
        (fun evs_p1 hp1 => hfits_err2 n evs_cp evs_p1 hcp hn_le hevs_cp hp1)
        (fun evs_p1 evs_p2 evs_f hp1 hp2 hfree =>
          henv_err n evs_cp evs_p1 evs_p2 evs_f hcp hn_le hevs_cp hp1 hp2 hfree)
        (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun1])
        (by simp only [wp_norm, arm64_norm, hsp1]) hs0A
        (by simp only [wp_norm, arm64_norm, htr1])
        (by simp only [wp_norm, arm64_norm, *])
        (by
          unfold decodeStateErrFramePlaced
          rw [protoPqRatchetStateAt_some_vn_eq, optChainParamsPBAt_some_eq]
          dsimp only [Reg.x0, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
            Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
          simp only [wp_norm, arm64_norm]
          sep_ac_rfl)
    · exact absurd hcbnz hx0_ne

theorem decodeState_vn_tag4_call_53968_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (cp : ChainParamsPB)
    (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt) cp rest1 99).toOption =
        none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hfits_cp : FitsEnv M lim st
      (ChainParamsMergeEnv ⟨iwt, s0.sp - 1012#64, cp, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩))
    (hfits_err1 : ∀ n evs_cp,
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt) cp rest1 99).toOption =
        none →
      n ≤ 1 →
      ChainParamsMergePostEnv ⟨iwt, s0.sp - 1012#64, cp, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_cp →
      FitsEnv M lim (M.stepEvents evs_cp st) (DecodeErrorPushEnv n))
    (hfits_err2 : ∀ n evs_cp evs_p1,
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt) cp rest1 99).toOption =
        none →
      n ≤ 1 →
      ChainParamsMergePostEnv ⟨iwt, s0.sp - 1012#64, cp, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_cp →
      DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_cp st)) (DecodeErrorPushEnv (n + 1)))
    (henv_err : ∀ n evs_cp evs_p1 evs_p2 evs_f,
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt) cp rest1 99).toOption =
        none →
      n ≤ 1 →
      ChainParamsMergePostEnv ⟨iwt, s0.sp - 1012#64, cp, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_cp →
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_cp st))))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨some { vn with chainParams := some cp }, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (cp' : ChainParamsPB) (rest2 : List (BitVec 8)) (evs_cp : List AllocEvent)
        (sf : State) (P' : SepProp),
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt) cp rest1 99).toOption =
        some (cp', rest2) →
      ChainParamsMergePostEnv ⟨iwt, s0.sp - 1012#64, cp, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_cp →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨some { vn with chainParams := some cp' }, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_cp st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_vn_tag4_call_53968_cl_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st w0 vn cp optCh inner rest1 limit iwt hrest1_le hrest1_suf hlen_bound
    herr_of_none s0 s P R post hpost hfits_cp hfits_err1 hfits_err2 henv_err hs0A
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hloop

/-- Envelope-parameterized Tag 4 (`chain_params: Option<ChainParams>`) in `VersionNegotiation` at `+1372..+1388`, `+1228..+1248`. -/
theorem decodeState_vn_tag4_539f8_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt)
        (vn.chainParams.getD default) rest1 99).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hfits_cp : FitsEnv M lim st
      (ChainParamsMergeEnv ⟨iwt, s0.sp - 1012#64, vn.chainParams.getD default,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩))
    (hfits_err1 : ∀ n evs_cp,
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt)
        (vn.chainParams.getD default) rest1 99).toOption = none →
      n ≤ 1 →
      ChainParamsMergePostEnv ⟨iwt, s0.sp - 1012#64, vn.chainParams.getD default,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_cp →
      FitsEnv M lim (M.stepEvents evs_cp st) (DecodeErrorPushEnv n))
    (hfits_err2 : ∀ n evs_cp evs_p1,
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt)
        (vn.chainParams.getD default) rest1 99).toOption = none →
      n ≤ 1 →
      ChainParamsMergePostEnv ⟨iwt, s0.sp - 1012#64, vn.chainParams.getD default,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_cp →
      DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_cp st)) (DecodeErrorPushEnv (n + 1)))
    (henv_err : ∀ n evs_cp evs_p1 evs_p2 evs_f,
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt)
        (vn.chainParams.getD default) rest1 99).toOption = none →
      n ≤ 1 →
      ChainParamsMergePostEnv ⟨iwt, s0.sp - 1012#64, vn.chainParams.getD default,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_cp →
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_cp st))))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1372#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨some vn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (cp' : ChainParamsPB) (rest2 : List (BitVec 8)) (evs_cp : List AllocEvent)
        (sf : State) (P' : SepProp),
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt)
        (vn.chainParams.getD default) rest1 99).toOption = some (cp', rest2) →
      ChainParamsMergePostEnv ⟨iwt, s0.sp - 1012#64, vn.chainParams.getD default,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_cp →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨some { vn with chainParams := some cp' }, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_cp st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  rcases vn with ⟨authKey, dir, minVer, _ | cp⟩
  · rw [protoPqRatchetStateCapOkAt_some_vn_eq]
    dsimp only [Option.getD] at herr_of_none hfits_cp hfits_err1 hfits_err2 henv_err hloop ⊢
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
    exact decodeState_vn_tag4_call_53968_cl_placed_ofEnv (v27 := v27) hc x st0 st w0
      ⟨authKey, dir, minVer, none⟩ default optCh inner rest1 limit iwt
      hrest1_le hrest1_suf hlen_bound herr_of_none s0 _ _ R post hpost
      hfits_cp hfits_err1 hfits_err2 henv_err hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by simp only [wp_norm, arm64_norm, hsp])
      (by simp only [wp_norm, arm64_norm, htr])
      (by simp only [wp_norm, arm64_norm, hx0])
      (by simp only [wp_norm, arm64_norm, hx19])
      (by simp only [wp_norm, arm64_norm, hx20])
      (by simp only [wp_norm, arm64_norm, hx21])
      (by simp only [wp_norm, arm64_norm, hx22])
      (by simp only [wp_norm, arm64_norm, hx23])
      (by simp only [wp_norm, arm64_norm, hx24])
      (by simp only [wp_norm, arm64_norm, hx25])
      (by simp only [wp_norm, arm64_norm, hx26])
      (by simp only [wp_norm, arm64_norm, hx27])
      (by simp only [wp_norm, arm64_norm, hx28])
      (by simp only [wp_norm, arm64_norm, hx29])
      (by
        rw [protoPqRatchetStateCapOkAt_some_vn_eq]
        dsimp only [decodeStateLoopCommonPlaced]
        sep_ac_rfl)
      hloop
  · rw [protoPqRatchetStateCapOkAt_some_vn_eq, optChainParamsPBAt_some_eq]
    dsimp only [Option.getD] at herr_of_none hfits_cp hfits_err1 hfits_err2 henv_err hloop ⊢
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced] at hpc ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1228#64)
    wp_steps_sync_pool ((blkPl_325).base + 1228#64)
    try simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    exact decodeState_vn_tag4_call_53968_cl_placed_ofEnv (v27 := v27) hc x st0 st w0
      ⟨authKey, dir, minVer, some cp⟩ cp optCh inner rest1 limit iwt
      hrest1_le hrest1_suf hlen_bound herr_of_none s0 _ _ R post hpost
      hfits_cp hfits_err1 hfits_err2 henv_err hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by simp only [wp_norm, arm64_norm, hsp])
      (by simp only [wp_norm, arm64_norm, htr])
      (by simp only [wp_norm, arm64_norm, hx0])
      (by simp only [wp_norm, arm64_norm, hx19])
      (by simp only [wp_norm, arm64_norm, hx20])
      (by simp only [wp_norm, arm64_norm, hx21])
      (by simp only [wp_norm, arm64_norm, hx22])
      (by simp only [wp_norm, arm64_norm, hx23])
      (by simp only [wp_norm, arm64_norm, hx24])
      (by simp only [wp_norm, arm64_norm, hx25])
      (by simp only [wp_norm, arm64_norm, hx26])
      (by simp only [wp_norm, arm64_norm, hx27])
      (by simp only [wp_norm, arm64_norm, hx28])
      (by simp only [wp_norm, arm64_norm, hx29])
      (by
        rw [protoPqRatchetStateCapOkAt_some_vn_eq, optChainParamsPBAt_some_eq]
        dsimp only [decodeStateLoopCommonPlaced]
        sep_ac_rfl)
      hloop

theorem decodeState_vn_tag4_539f8_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt)
        (vn.chainParams.getD default) rest1 99).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hfits_cp : FitsEnv M lim st
      (ChainParamsMergeEnv ⟨iwt, s0.sp - 1012#64, vn.chainParams.getD default,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩))
    (hfits_err1 : ∀ n evs_cp,
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt)
        (vn.chainParams.getD default) rest1 99).toOption = none →
      n ≤ 1 →
      ChainParamsMergePostEnv ⟨iwt, s0.sp - 1012#64, vn.chainParams.getD default,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_cp →
      FitsEnv M lim (M.stepEvents evs_cp st) (DecodeErrorPushEnv n))
    (hfits_err2 : ∀ n evs_cp evs_p1,
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt)
        (vn.chainParams.getD default) rest1 99).toOption = none →
      n ≤ 1 →
      ChainParamsMergePostEnv ⟨iwt, s0.sp - 1012#64, vn.chainParams.getD default,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_cp →
      DecodeErrorPushEnv n evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_cp st)) (DecodeErrorPushEnv (n + 1)))
    (henv_err : ∀ n evs_cp evs_p1 evs_p2 evs_f,
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt)
        (vn.chainParams.getD default) rest1 99).toOption = none →
      n ≤ 1 →
      ChainParamsMergePostEnv ⟨iwt, s0.sp - 1012#64, vn.chainParams.getD default,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_cp →
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_cp st))))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1372#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨some vn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (cp' : ChainParamsPB) (rest2 : List (BitVec 8)) (evs_cp : List AllocEvent)
        (sf : State) (P' : SepProp),
      (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto iwt)
        (vn.chainParams.getD default) rest1 99).toOption = some (cp', rest2) →
      ChainParamsMergePostEnv ⟨iwt, s0.sp - 1012#64, vn.chainParams.getD default,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_cp →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨some { vn with chainParams := some cp' }, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_cp st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_vn_tag4_539f8_cl_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st w0 vn optCh inner rest1 limit iwt hrest1_le hrest1_suf hlen_bound
    herr_of_none s0 s P R post hpost hfits_cp hfits_err1 hfits_err2 henv_err hs0A
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hloop

/-- Envelope-parameterized unknown tag (`skip_field`) in `VersionNegotiation` at `+1392..+1408`, `+1248`. -/
theorem decodeState_vn_skip_53a0c_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit tag : Nat) (iwt : WireType)
    (htag : 1 ≤ tag ∧ tag < 2 ^ 32)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none : skipField (2 * rest1.length + 2) 99 tag iwt rest1 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hfits_sf : FitsEnv M lim st
      (SkipField3Env ⟨iwt, tag, 99, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩))
    (hfits_err : ∀ evs_sf,
      skipField (2 * rest1.length + 2) 99 tag iwt rest1 = none →
      SkipField3Env ⟨iwt, tag, 99, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_sf →
      FitsEnv M lim (M.stepEvents evs_sf st) (DecodeErrorPushEnv 0))
    (henv_err : ∀ evs_sf evs_p evs_f,
      skipField (2 * rest1.length + 2) 99 tag iwt rest1 = none →
      SkipField3Env ⟨iwt, tag, 99, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_sf →
      DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_sf st)))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1392#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : BitVec.setWidth 8 (s.readReg64 .x0) = BitVec.ofNat 8 iwt.toNat)
    (hx1 : BitVec.setWidth 32 (s.readReg64 .x1) = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨some vn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (rest2 : List (BitVec 8)) (evs_sf : List AllocEvent)
        (sf : State) (P' : SepProp),
      skipField (2 * rest1.length + 2) 99 tag iwt rest1 = some rest2 →
      SkipField3Env ⟨iwt, tag, 99, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_sf →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨some vn, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_sf st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hsf_call := hc.skipField3
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced] at hpc hsf_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 263)
  wp_steps_sync_pool (lsmpl.base 263)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpIPlaced.call_skipField3_cl hsf_call iwt tag 99
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1 st
    (ret_pc := (blkPl_325).base + 1404#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx0])
    (hx1 := by simp only [wp_norm, arm64_norm, hx1])
    (htag := htag.2)
    (hx2 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hx3 := by simp only [wp_norm, arm64_norm])
    (hdepth := by decide) (hlen := by omega)
    (hfits := hfits_sf)
    (hP := by sep_focus) ?_ ?_
  · intro s1 rest2 evs_sf hsf hevs_sf hle2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1252#64)
    wp_steps_sync_pool ((blkPl_325).base + 1252#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
      (a := s0.sp - 1040#64) (rem1 := rest1.length) (rem2 := rest2.length)
      (st := ⟨some vn, optCh, inner⟩) hle2) (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
    exact hloop rest2 evs_sf _ _ hsf hevs_sf hle2 hsuf2
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun1]) (by simp only [wp_norm, arm64_norm, hsp1])
      (by simp only [wp_norm, arm64_norm, htr1])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by dsimp only [decodeStateLoopCommonPlaced]; sep_ac_rfl)
  · intro s1 evs_sf hsf hevs_sf hpc1 hrun1 hsp1 htr1 hcs1 hx0_ne
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2352#64)
    wp_steps 3
    wp_if hcbnz
    · refine SepWP.fold (errFrame_parts_fold A.repAlloc x s0 hrest1_le hrest1_suf) (by sep_focus) ?_
      refine SepWP.fold (protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner
        A.repAlloc (s0.sp - 1040#64) rest1.length ⟨some vn, optCh, inner⟩) (by sep_focus) ?_
      apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
      exact decodeState_err_push_53dcc_cl_placed_ofEnv hc x st0
        (M.stepEvents evs_sf st) ⟨some vn, optCh, inner⟩ w0 0 s0 _ _ R post hpost
        (herr_of_none hsf) (by decide)
        (hfits_err evs_sf hsf hevs_sf)
        (fun evs_p evs_f hp hfree => henv_err evs_sf evs_p evs_f hsf hevs_sf hp hfree)
        (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun1])
        (by simp only [wp_norm, arm64_norm, hsp1]) hs0A
        (by simp only [wp_norm, arm64_norm, htr1])
        (by simp only [wp_norm, arm64_norm, *])
        (by
          dsimp only [Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
            Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
          simp only [wp_norm, arm64_norm]
          sep_ac_rfl)
    · exact absurd hcbnz hx0_ne

theorem decodeState_vn_skip_53a0c_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit tag : Nat) (iwt : WireType)
    (htag : 1 ≤ tag ∧ tag < 2 ^ 32)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none : skipField (2 * rest1.length + 2) 99 tag iwt rest1 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hfits_sf : FitsEnv M lim st
      (SkipField3Env ⟨iwt, tag, 99, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩))
    (hfits_err : ∀ evs_sf,
      skipField (2 * rest1.length + 2) 99 tag iwt rest1 = none →
      SkipField3Env ⟨iwt, tag, 99, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_sf →
      FitsEnv M lim (M.stepEvents evs_sf st) (DecodeErrorPushEnv 0))
    (henv_err : ∀ evs_sf evs_p evs_f,
      skipField (2 * rest1.length + 2) 99 tag iwt rest1 = none →
      SkipField3Env ⟨iwt, tag, 99, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_sf →
      DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_sf st)))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1392#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : BitVec.setWidth 8 (s.readReg64 .x0) = BitVec.ofNat 8 iwt.toNat)
    (hx1 : BitVec.setWidth 32 (s.readReg64 .x1) = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨some vn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (rest2 : List (BitVec 8)) (evs_sf : List AllocEvent)
        (sf : State) (P' : SepProp),
      skipField (2 * rest1.length + 2) 99 tag iwt rest1 = some rest2 →
      SkipField3Env ⟨iwt, tag, 99, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_sf →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨some vn, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_sf st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_vn_skip_53a0c_cl_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st w0 vn optCh inner rest1 limit tag iwt htag hrest1_le hrest1_suf hlen_bound
    herr_of_none s0 s P R post hpost hfits_sf hfits_err henv_err hs0A
    hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hloop

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationClPlacedBudget
