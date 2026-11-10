/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Outer `PqRatchetState::v1` (Tag 3) Entry & `none` Path (Block `325`)

Proves 224-byte Q-register stack copies (`+340`, `+1484`), the budget-threaded relocatable outer
Tag 3 `none` merge path (`+324`), and Tag 3 entry (`+312`), re-exporting `skip_field` and `some`
helpers from `V1StateStepPlacedBudgetAux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkLib_eq_325 blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (OptInnerStatePolyBound V1StateMergeGhost codecWireTypeToProto mergeLoopBin
   v1StateJumpTablesPlacedAt)
open CryptoVerification.LibsignalSpqrV1
  (ChainPB PqRatchetState V1State VersionNegotiationPB spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost DropOptProtoInnerStateGhost Quads28 TraceVRegs V1InnerHeapPred
   decodeStatePlacedEntry decodeStatePlacedProg dropOptProtoInnerStateStack
   memRegion_224_eq_quads28At none3Cap optChainPBCapOkAt_mono optProtoInnerStateAt_entails_quads28
   optProtoInnerStateCapOkAt_entails_quads28 optProtoPqRatchetInnerAt optProtoPqRatchetInnerCapOkAt
   optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt optVersionNegotiationPBCapOkAt_mono
   pqRatchetState_mergeField_tag3 protoPqRatchetStateCapOkAt quads14At quads28At
   quads28At_entails_memRegion_224 quads28_entails_optProtoInnerStateAt
   quads28_entails_optProtoInnerStateCapOkAt quads7At sp_sub_1392_aligned stackAt_of_callee
   stackAt_to_callee)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorPushEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (V1StateMergeEnv V1StateMergePostEnv v1StateMergePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStateCalleeContractsPlaced DecodeStateCalleeContractsPlacedX
   dropOptProtoInnerStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget (decodeStateErrFramePlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced
   decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced decodeStateLoopCommonPlaced loopCommon_calleeErr_to_errFrame_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
  (decodeState_err_push_53bc0_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlacedBudgetAux
  (head_ne_none3Cap_branch memRegion_224_split_head optProtoInnerStateCapOkAt_default_init
   optProtoInnerStateCapOkAt_expose_head optProtoInnerStateCapOkAt_fold_head
   protoPqRatchetStateCapOkAt_v1_eq scratch_688_dropped_split_48 scratch_688_restore_from_quads28
   scratch_688_split_quads28_and_3a0 setWidth8_ofNat64_wt)

export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlacedBudgetAux
  (call_v1StateMerge_ofEnv call_v1StateMerge
   decodeState_outer_skip_53664_placed_ofEnv decodeState_outer_skip_53664_placed)
export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlacedBudgetAux
  (decodeState_v1_some_53678_placed_ofEnv decodeState_v1_some_53678_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup v1StateJumpTablesPlacedAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local irreducible] mergeMessage mergeLoopBin

@[simp] private theorem decodeState_codecWireTypeToProto_eq (wt : WireType) :
    CryptoVerification.SpqrV1.Top.DecodeState.codecWireTypeToProto wt = codecWireTypeToProto wt := by
  cases wt <;> rfl

/-! ## 1. 224-Byte Q-Register Copies & Outer Tag 3 `none` Path (`+324..+452`, `+1484..+1572`) -/

private theorem optProtoPqRatchetInnerCapOkAt_none_entails_quads28
    (H_inner : V1InnerHeapPred) (A : RustAlloc) (a : BitVec 64) (remLen : Nat) :
    optProtoPqRatchetInnerCapOkAt H_inner A a remLen none ⊢ ∃∗ q_dst : Quads28, quads28At a q_dst := by
  refine Entails.trans (optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt H_inner A a remLen none) ?_
  unfold optProtoPqRatchetInnerAt
  rw [← memRegion_224_eq_quads28At a,
      ProofLib.memRegion_split' (b := a) (n := 8) (k := 216) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)

/-- Budget-threaded 224-byte Q-register copy (`+340..+428`, 22 instructions) from
`x29 - 0xe8` (`s0.sp - 328#64`) to `sp + 0x2c0` (`s0.sp - 688#64`), also storing
`x24` (`s0.sp - 912#64`) at `sp + 0x3a0` (`s0.sp - 464#64`). -/
theorem decodeState_v1_copy_to_scratch_535f0_placed [LibsignalPlacement]
    {M : AllocCostModel} {target_pc v0 v20 v27 : BitVec 64}
    {ext : String → Option (State → State)}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (outPtr : BitVec 64) (q_src q_dst : Quads28) (w_3a0 : BitVec 64)
    (s0 s : State) (P R_frame : SepProp) (post : State → SepProp → Prop)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 340#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = v0)
    (hx19 : s.readReg64 .x19 = outPtr)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = (quads28At (s0.sp - 328#64) q_src ∗
      quads28At (s0.sp - 688#64) q_dst ∗
      ((s0.sp - 464#64) ↦₆₄ w_3a0) ∗
      A.pool lim st s) ∗
      R_frame)
    (hnext : ∀ (sf : State) (P' : SepProp),
      sf.pc = decodeStatePlacedEntry + 428#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 (Reg.gpr 0#5) = v0 →
      sf.readReg64 .x19 = outPtr →
      sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = (quads28At (s0.sp - 328#64) q_src ∗
        quads28At (s0.sp - 688#64) q_src ∗
        ((s0.sp - 464#64) ↦₆₄ (s0.sp - 912#64)) ∗
        A.pool lim st sf) ∗
        R_frame →
      SepWP (decodeStatePlacedProg ext) target_pc sf P' post) :
    SepWP (decodeStatePlacedProg ext) target_pc s P post := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  rcases q_src with ⟨⟨⟨s00, s01, s02, s03, s04, s05, s06⟩, ⟨s10, s11, s12, s13, s14, s15, s16⟩⟩,
                     ⟨⟨s20, s21, s22, s23, s24, s25, s26⟩, ⟨s30, s31, s32, s33, s34, s35, s36⟩⟩⟩
  rcases q_dst with ⟨⟨⟨d00, d01, d02, d03, d04, d05, d06⟩, ⟨d10, d11, d12, d13, d14, d15, d16⟩⟩,
                     ⟨⟨d20, d21, d22, d23, d24, d25, d26⟩, ⟨d30, d31, d32, d33, d34, d35, d36⟩⟩⟩
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, quads28At, quads14At, quads7At] at hpc hnext ⊢
  wp_steps_sync_pool ((blkPl_325).base + 428#64)
  try simp only [State.setMem_setMem]
  exact hnext _ _
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx0]) (by simp only [wp_norm, arm64_norm, hx19])
    (by simp only [wp_norm, arm64_norm, hx20]) (by simp only [wp_norm, arm64_norm, hx21])
    (by simp only [wp_norm, arm64_norm, hx22]) (by simp only [wp_norm, arm64_norm, hx23])
    (by simp only [wp_norm, arm64_norm, hx24]) (by simp only [wp_norm, arm64_norm, hx25])
    (by simp only [wp_norm, arm64_norm, hx26]) (by simp only [wp_norm, arm64_norm, hx27])
    (by simp only [wp_norm, arm64_norm, hx28]) (by simp only [wp_norm, arm64_norm, hx29])
    (by sep_ac_rfl)

/-- Budget-threaded 224-byte Q-register copy (`+1484..+1576`, 23 instructions) from
`x29 - 0xe8` (`s0.sp - 328#64`) to `x24` (`s0.sp - 912#64`), followed by `cbnz x0, 0x53bc0`
(not taken since `x0 = 0#64`) and `ldr x20, [sp, #0x158]`. -/
theorem decodeState_v1_copy_to_state_53a68_placed [LibsignalPlacement]
    {M : AllocCostModel} {target_pc v27 : BitVec 64}
    {ext : String → Option (State → State)}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (outPtr : BitVec 64) (q_src q_dst : Quads28) (remLen : Nat)
    (s0 s : State) (P R_frame : SepProp) (post : State → SepProp → Prop)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1484#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx19 : s.readReg64 .x19 = outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = (quads28At (s0.sp - 328#64) q_src ∗
      quads28At (s0.sp - 912#64) q_dst ∗
      ((s0.sp - 1048#64) ↦₆₄ BitVec.ofNat 64 remLen) ∗
      A.pool lim st s) ∗
      R_frame)
    (hnext : ∀ (sf : State) (P' : SepProp),
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 remLen →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = (quads28At (s0.sp - 328#64) q_src ∗
        quads28At (s0.sp - 912#64) q_src ∗
        ((s0.sp - 1048#64) ↦₆₄ BitVec.ofNat 64 remLen) ∗
        A.pool lim st sf) ∗
        R_frame →
      SepWP (decodeStatePlacedProg ext) target_pc sf P' post) :
    SepWP (decodeStatePlacedProg ext) target_pc s P post := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hbne0 : (s.readReg64 (Reg.gpr 0#5) != 0#64) = false := by rw [hx0]; rfl
  have hbeq0 : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  subst hP
  rcases q_src with ⟨⟨⟨s00, s01, s02, s03, s04, s05, s06⟩, ⟨s10, s11, s12, s13, s14, s15, s16⟩⟩,
                     ⟨⟨s20, s21, s22, s23, s24, s25, s26⟩, ⟨s30, s31, s32, s33, s34, s35, s36⟩⟩⟩
  rcases q_dst with ⟨⟨⟨d00, d01, d02, d03, d04, d05, d06⟩, ⟨d10, d11, d12, d13, d14, d15, d16⟩⟩,
                     ⟨⟨d20, d21, d22, d23, d24, d25, d26⟩, ⟨d30, d31, d32, d33, d34, d35, d36⟩⟩⟩
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, quads28At, quads14At, quads7At] at hpc hnext ⊢
  wp_steps_sync_pool ((blkPl_325).base + 1576#64)
  try simp only [State.setMem_setMem]
  exact hnext _ _
    (by simp only [wp_norm, arm64_norm, hx0])
    (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19]) (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hx21]) (by simp only [wp_norm, arm64_norm, hx22])
    (by simp only [wp_norm, arm64_norm, hx23]) (by simp only [wp_norm, arm64_norm, hx24])
    (by simp only [wp_norm, arm64_norm, hx25]) (by simp only [wp_norm, arm64_norm, hx26])
    (by simp only [wp_norm, arm64_norm, hx27]) (by simp only [wp_norm, arm64_norm, hx28])
    (by simp only [wp_norm, arm64_norm, hx29])
    (by sep_ac_rfl)

/-- Envelope-parameterized outer tag 3 when `inner = none` (`+324..+452` and `+1484..+1572`). -/
theorem decodeState_v1_none_535e0_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {V1PreEnv V1PostEnv : V1StateMergeGhost → List AllocEvent → Prop}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (hv1_call : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 298)
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpecOfEnv A lim V1PreEnv V1PostEnv)))
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (optCh : Option ChainPB)
    (rest1 : List (BitVec 8)) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage V1State.mergeField (codecWireTypeToProto iwt) default rest1 100).toOption =
        none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hfits_v1 : OptInnerStatePolyBound rest1.length (default : V1State).innerState →
      FitsEnv M lim st
        (V1PreEnv ⟨iwt, s0.sp - 328#64, default, s0.sp - 336#64, s0.sp - 1056#64,
          x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩))
    (hfits_err : ∀ evs_v1 evs_drop n,
      (mergeMessage V1State.mergeField (codecWireTypeToProto iwt) default rest1 100).toOption =
        none →
      OptInnerStatePolyBound rest1.length (default : V1State).innerState →
      V1PostEnv ⟨iwt, s0.sp - 328#64, default, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_v1 →
      FreeOnlyEvs evs_drop → n ≤ 4 →
      FitsEnv M lim (M.stepEvents evs_drop (M.stepEvents evs_v1 st)) (DecodeErrorPushEnv n))
    (henv_err : ∀ evs_v1 evs_drop evs_p evs_f n,
      (mergeMessage V1State.mergeField (codecWireTypeToProto iwt) default rest1 100).toOption =
        none →
      OptInnerStatePolyBound rest1.length (default : V1State).innerState →
      V1PostEnv ⟨iwt, s0.sp - 328#64, default, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_v1 →
      FreeOnlyEvs evs_drop → n ≤ 4 →
      DecodeErrorPushEnv n evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_drop (M.stepEvents evs_v1 st))))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 324#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
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
        ⟨optVn, optCh, none⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (w0' : BitVec 64) (v1' : V1State) (rest2 : List (BitVec 8))
        (evs_v1 : List AllocEvent) (sf : State) (P' : SepProp),
      (mergeMessage V1State.mergeField (codecWireTypeToProto iwt) default rest1 100).toOption =
        some (v1', rest2) →
      OptInnerStatePolyBound rest1.length (default : V1State).innerState →
      V1PostEnv ⟨iwt, s0.sp - 328#64, default, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_v1 →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 rest2.length →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, optCh, some (.v1 v1')⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_v1 st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hdrop_inner := hc.dropOptProtoInnerState
  simp only [dropOptProtoInnerStatePlacedSpec] at hdrop_inner
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf,
      protoPqRatchetStateCapOkAt_v1_eq]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced] at hpc hv1_call hdrop_inner ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 298)
  refine SepWP.fold (memRegion_224_split_head (s0.sp - 328#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_steps_sync_pool (lsmpl.base 298)
  try simp only [State.setMem_setMem]
  refine SepWP.fold (optProtoInnerStateCapOkAt_default_init H_inner A.repAlloc
    (s0.sp - 328#64) rest1.length (by omega)) (by sep_focus) ?_
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  have hx29_e8 : s0.sp - 96#64 - 232#64 = s0.sp - 328#64 := by bv_omega
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  have hsp1048 : s0.sp - 1056#64 + 8#64 = s0.sp - 1048#64 := by bv_omega
  refine call_v1StateMerge_ofEnv hv1_call hc.of_cap_inner hc.of_drop_inner
    iwt (s0.sp - 328#64) default
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1 st
    (ret_pc := (blkPl_325).base + 340#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx0, setWidth8_ofNat64_wt])
    (hx1 := by simp only [wp_norm, arm64_norm, hx29, hx29_e8])
    (hx2 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hfits := hfits_v1)
    (hP := by sep_focus) ?_ ?_
  · intro s1 v1' rest2 evs_v1 hv1 hpb hevs_v1 hle2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1576#64)
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (optVersionNegotiationPBCapOkAt_mono (A := A.repAlloc) (a := s0.sp - 1040#64)
      (rem1 := rest1.length) (rem2 := rest2.length) (opt := optVn) hle2) (by sep_focus) ?_
    refine SepWP.fold (optChainPBCapOkAt_mono (A := A.repAlloc) (a := s0.sp - 992#64)
      (rem1 := rest1.length) (rem2 := rest2.length) (opt := optCh) hle2) (by sep_focus) ?_
    refine SepWP.fold (optProtoInnerStateCapOkAt_entails_quads28 H_inner A.repAlloc
      (s0.sp - 328#64) rest2.length v1'.innerState) (by sep_focus) ?_
    refine SepWP.fold (scratch_688_split_quads28_and_3a0 s0.sp w0) (by sep_focus) ?_
    refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_none_entails_quads28 H_inner A.repAlloc
      (s0.sp - 912#64) rest1.length) (by sep_focus) ?_
    wp_pull_exists
    rename_i q_src w_3a0 q_scratch q_state
    refine decodeState_v1_copy_to_scratch_535f0_placed (v27 := v27) A lim (M.stepEvents evs_v1 st)
      x.outPtr q_src q_scratch w_3a0 s0 s1 _ _ _ hs0A
      hpc1 hrun1 hsp1 htr1 hx0_0
      (by simp only [wp_norm, arm64_norm, *]) rfl
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by sep_focus) ?_
    intro s2 P2 hpc2 hrun2 hsp2 htr2 hx0_2 hx19_2 _ hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hP2
    subst hP2
    have hsp2A : s2.spAligned = true := by rw [State.spAligned, hsp2]; exact sp_sub_1392_aligned s0 hs0A
    dsimp only [decodeStatePlacedEntry] at hpc2
    wp_steps_sync_pool ((blkPl_325).base + 1484#64)
    try simp only [State.setMem_setMem]
    dsimp only [sliceCursorAfter]
    rw [hsp1048]
    refine decodeState_v1_copy_to_state_53a68_placed (v27 := v27) A lim (M.stepEvents evs_v1 st)
      x.outPtr q_src q_state rest2.length s0 _ _ _ _ hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, hpc2, hx0_2])
      (by simp only [wp_norm, arm64_norm, hrun2]) (by simp only [wp_norm, arm64_norm, hsp2])
      (by simp only [wp_norm, arm64_norm, htr2]) (by simp only [wp_norm, arm64_norm, hx0_2])
      (by simp only [wp_norm, arm64_norm, hx19_2]) (by simp only [wp_norm, arm64_norm, hx21_2])
      (by simp only [wp_norm, arm64_norm, hx22_2]) (by simp only [wp_norm, arm64_norm, hx23_2])
      (by simp only [wp_norm, arm64_norm, hx24_2]) (by simp only [wp_norm, arm64_norm, hx25_2])
      (by simp only [wp_norm, arm64_norm, hx26_2]) (by simp only [wp_norm, arm64_norm, hx27_2])
      (by simp only [wp_norm, arm64_norm, hx28_2]) (by simp only [wp_norm, arm64_norm, hx29_2])
      (by sep_focus) ?_
    intro sf P3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hP3
    subst hP3
    refine SepWP.fold (quads28At_entails_memRegion_224 (s0.sp - 328#64) q_src) (by sep_focus) ?_
    refine SepWP.fold (scratch_688_restore_from_quads28 s0.sp (s0.sp - 912#64) q_src) (by sep_focus) ?_
    refine SepWP.fold (quads28_entails_optProtoInnerStateCapOkAt H_inner A.repAlloc
      (s0.sp - 912#64) rest2.length q_src v1'.innerState) (by sep_focus) ?_
    apply SepWP.done hpc3 hrun3
    exact hdone q_src.head v1' rest2 evs_v1 sf _ hv1 hpb hevs_v1 hle2 hsuf2 hpc3 hrun3 hsp3 htr3
      hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
      (by
        rw [protoPqRatchetStateCapOkAt_v1_eq]
        dsimp only [decodeStateLoopCommonPlaced, sliceCursorAfter, optProtoPqRatchetInnerCapOkAt,
          Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
          Reg.x28, Reg.x29, Reg.x30]
        rw [hsp1048]
        sep_ac_rfl)
  · intro s1 n m' evs_v1 hv1 hpb hevs_v1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_ne hn
    clear hv1_call
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1828#64)
    refine SepWP.fold (optProtoInnerStateAt_entails_quads28 H_inner A.repAlloc (s0.sp - 328#64) m')
      (by sep_focus) ?_
    refine SepWP.fold (scratch_688_split_quads28_and_3a0 s0.sp w0) (by sep_focus) ?_
    wp_pull_exists
    rename_i q_src w_3a0 q_scratch
    refine decodeState_v1_copy_to_scratch_535f0_placed (v27 := v27) A lim (M.stepEvents evs_v1 st)
      x.outPtr q_src q_scratch w_3a0 s0 s1 _ _ _ hs0A
      hpc1 hrun1 hsp1 htr1 rfl
      (by simp only [wp_norm, arm64_norm, *]) rfl
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by sep_focus) ?_
    intro s2 P2 hpc2 hrun2 hsp2 htr2 hx0_2 hx19_2 _ hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hP2
    subst hP2
    have hsp2A : s2.spAligned = true := by rw [State.spAligned, hsp2]; exact sp_sub_1392_aligned s0 hs0A
    dsimp only [decodeStatePlacedEntry] at hpc2
    have hbeq0_1 : (s1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have hbeq0_2 : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := by rw [hx0_2]; exact hbeq0_1
    refine SepWP.fold (quads28At_entails_memRegion_224 (s0.sp - 328#64) q_src) (by sep_focus) ?_
    refine SepWP.fold (quads28_entails_optProtoInnerStateAt H_inner A.repAlloc (s0.sp - 688#64) q_src m')
      (by sep_focus) ?_
    refine SepWP.fold (stackAt_to_callee (s0.sp - 1392#64) dropOptProtoInnerStateStack (by decide))
      (by sep_focus) ?_
    wp_steps_sync_pool (lsmpl.base 267)
    try simp only [State.setMem_setMem]
    wp_call hdrop_inner (({ a := s0.sp - 688#64, st := m' } : DropOptProtoInnerStateGhost), M.stepEvents evs_v1 st)
    have hstk_sf :
        stackAt sf.sp dropOptProtoInnerStateStack =
          stackAt (s0.sp - 1392#64) dropOptProtoInnerStateStack := by
      rw [hsp_sf, hsp2]
    refine SepWP.fold (Entails.of_eq hstk_sf) (by sep_focus) ?_
    refine SepWP.fold (stackAt_of_callee (s0.sp - 1392#64) dropOptProtoInnerStateStack (by decide))
      (by sep_focus) ?_
    wp_steps_sync_pool ((blkPl_325).base + 1828#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold (scratch_688_dropped_split_48 s0.sp (s0.sp - 912#64)) (by sep_focus) ?_
    wp_pull_exists
    rename_i w0'
    refine SepWP.fold (Entails.of_eq (protoPqRatchetStateCapOkAt_v1_eq H_inner A.repAlloc s0.sp
      rest1.length optVn optCh none).symm) (by sep_focus) ?_
    refine SepWP.fold (loopCommon_calleeErr_to_errFrame_placed H_inner A lim
      (M.stepEvents w (M.stepEvents evs_v1 st)) x hrest1_le hrest1_suf rest1.length
      ⟨optVn, optCh, none⟩ s0 _)
      (by dsimp only [decodeStateLoopCommonPlaced]; sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    exact SepWPpIPlaced.of_sepWPp (decodeState_err_push_53bc0_placed_ofEnv hc x st0
      (M.stepEvents w (M.stepEvents evs_v1 st)) ⟨optVn, optCh, none⟩ w0' n s0 _ _ R post hpost
      (herr_of_none hv1) (by omega)
      (hfits_err evs_v1 w n hv1 hpb hevs_v1 ‹FreeOnlyEvs w› hn)
      (fun evs_p evs_f hp hf => henv_err evs_v1 w evs_p evs_f n hv1 hpb hevs_v1 ‹FreeOnlyEvs w› hn hp hf)
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hs0A
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by
        dsimp only [decodeStateErrFramePlaced, Reg.x0, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
          Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        simp only [wp_norm, arm64_norm, *]
        sep_ac_rfl))

theorem decodeState_v1_none_535e0_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (optCh : Option ChainPB)
    (rest1 : List (BitVec 8)) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage V1State.mergeField (codecWireTypeToProto iwt) default rest1 100).toOption =
        none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hfits_v1 : OptInnerStatePolyBound rest1.length (default : V1State).innerState →
      FitsEnv M lim st
        (V1StateMergeEnv ⟨iwt, s0.sp - 328#64, default, s0.sp - 336#64, s0.sp - 1056#64,
          x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩))
    (hfits_err : ∀ evs_v1 evs_drop n,
      (mergeMessage V1State.mergeField (codecWireTypeToProto iwt) default rest1 100).toOption =
        none →
      OptInnerStatePolyBound rest1.length (default : V1State).innerState →
      V1StateMergePostEnv ⟨iwt, s0.sp - 328#64, default, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_v1 →
      FreeOnlyEvs evs_drop → n ≤ 4 →
      FitsEnv M lim (M.stepEvents evs_drop (M.stepEvents evs_v1 st)) (DecodeErrorPushEnv n))
    (henv_err : ∀ evs_v1 evs_drop evs_p evs_f n,
      (mergeMessage V1State.mergeField (codecWireTypeToProto iwt) default rest1 100).toOption =
        none →
      OptInnerStatePolyBound rest1.length (default : V1State).innerState →
      V1StateMergePostEnv ⟨iwt, s0.sp - 328#64, default, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_v1 →
      FreeOnlyEvs evs_drop → n ≤ 4 →
      DecodeErrorPushEnv n evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_drop (M.stepEvents evs_v1 st))))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 324#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
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
        ⟨optVn, optCh, none⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (w0' : BitVec 64) (v1' : V1State) (rest2 : List (BitVec 8))
        (evs_v1 : List AllocEvent) (sf : State) (P' : SepProp),
      (mergeMessage V1State.mergeField (codecWireTypeToProto iwt) default rest1 100).toOption =
        some (v1', rest2) →
      OptInnerStatePolyBound rest1.length (default : V1State).innerState →
      V1StateMergePostEnv ⟨iwt, s0.sp - 328#64, default, s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_v1 →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 rest2.length →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, optCh, some (.v1 v1')⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_v1 st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_v1_none_535e0_placed_ofEnv
    (V1PreEnv := V1StateMergeEnv) (V1PostEnv := V1StateMergePostEnv)
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc.toDecodeStateCalleeContractsPlaced hc.v1StateMerge
    x st0 st w0 optVn optCh rest1 iwt hrest1_le hrest1_suf hlen_bound
    herr_of_none s0 s P R post hpost hfits_v1 hfits_err henv_err hs0A
    hpc hrun hsp htr hx0 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hdone

/-! ## 2. Outer Tag 3 Entry (`+312`) -/

/-- Message value passed to `V1State::merge` in outer tag 3 (`PqRatchetState::v1`). -/
def pqRatchetStateV1OrDefault (curSt : PqRatchetState) : V1State :=
  match curSt.inner with
  | none => default
  | some (.v1 v1) => v1

/-- Stack pointer passed as `x1` (`msgPtr`) to `V1State::merge` in outer tag 3:
`sp - 328#64` (`x29 - 0xe8`) when `curSt.inner = none`, and `sp - 912#64` (`x24`) when
`curSt.inner = some (.v1 _)`. -/
def pqRatchetStateV1MsgPtr (sp : BitVec 64) (curSt : PqRatchetState) : BitVec 64 :=
  match curSt.inner with
  | none => sp - 328#64
  | some (.v1 _) => sp - 912#64

/-- Envelope-parameterized outer tag 3 (`PqRatchetState::v1`, `+312`). -/
theorem decodeState_v1_entry_535d4_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {V1PreEnv V1PostEnv : V1StateMergeGhost → List AllocEvent → Prop}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (hv1_call : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 298)
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpecOfEnv A lim V1PreEnv V1PostEnv)))
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (curSt : PqRatchetState)
    (rest1 : List (BitVec 8)) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (PqRatchetState.mergeField curSt 3#32 (codecWireTypeToProto iwt) rest1 100).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hfits_v1 : OptInnerStatePolyBound rest1.length (pqRatchetStateV1OrDefault curSt).innerState →
      FitsEnv M lim st
        (V1PreEnv ⟨iwt, pqRatchetStateV1MsgPtr s0.sp curSt, pqRatchetStateV1OrDefault curSt,
          s0.sp - 336#64, s0.sp - 1056#64,
          x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩))
    (hfits_err : ∀ evs_v1 evs_drop n,
      (PqRatchetState.mergeField curSt 3#32 (codecWireTypeToProto iwt) rest1 100).toOption = none →
      OptInnerStatePolyBound rest1.length (pqRatchetStateV1OrDefault curSt).innerState →
      V1PostEnv ⟨iwt, pqRatchetStateV1MsgPtr s0.sp curSt, pqRatchetStateV1OrDefault curSt,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_v1 →
      FreeOnlyEvs evs_drop → n ≤ 4 →
      FitsEnv M lim (M.stepEvents evs_drop (M.stepEvents evs_v1 st)) (DecodeErrorPushEnv n))
    (henv_err : ∀ evs_v1 evs_drop evs_p evs_f n,
      (PqRatchetState.mergeField curSt 3#32 (codecWireTypeToProto iwt) rest1 100).toOption = none →
      OptInnerStatePolyBound rest1.length (pqRatchetStateV1OrDefault curSt).innerState →
      V1PostEnv ⟨iwt, pqRatchetStateV1MsgPtr s0.sp curSt, pqRatchetStateV1OrDefault curSt,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_v1 →
      FreeOnlyEvs evs_drop → n ≤ 4 →
      DecodeErrorPushEnv n evs_p → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_drop (M.stepEvents evs_v1 st))))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 312#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
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
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (w0' : BitVec 64) (st' : PqRatchetState) (rest2 : List (BitVec 8))
        (evs_v1 : List AllocEvent) (sf : State) (P' : SepProp),
      (PqRatchetState.mergeField curSt 3#32 (codecWireTypeToProto iwt) rest1 100).toOption =
        some (st', rest2) →
      OptInnerStatePolyBound rest1.length (pqRatchetStateV1OrDefault curSt).innerState →
      V1PostEnv ⟨iwt, pqRatchetStateV1MsgPtr s0.sp curSt, pqRatchetStateV1OrDefault curSt,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_v1 →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 rest2.length →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length st' ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_v1 st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  rcases curSt with ⟨optVn, optCh, inner⟩
  have htag3 := pqRatchetState_mergeField_tag3 ⟨optVn, optCh, inner⟩ iwt rest1 100
  simp only [decodeState_codecWireTypeToProto_eq] at htag3
  rw [htag3] at herr_of_none
  cases inner with
  | none =>
    dsimp only [pqRatchetStateV1OrDefault, pqRatchetStateV1MsgPtr] at hfits_v1 hfits_err henv_err hdone
    dsimp only at herr_of_none
    rw [protoPqRatchetStateCapOkAt_v1_eq]
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced,
      optProtoPqRatchetInnerCapOkAt, none3Cap] at hpc ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 324#64)
    wp_steps_sync_pool ((blkPl_325).base + 324#64)
    try simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    exact decodeState_v1_none_535e0_placed_ofEnv hc hv1_call x st0 st w0 optVn optCh rest1 iwt
      hrest1_le hrest1_suf hlen_bound
      (fun hnone => herr_of_none (by rw [hnone]; rfl)) s0 _ _ R post hpost
      hfits_v1
      (fun evs_v1 evs_drop n hnone =>
        hfits_err evs_v1 evs_drop n (by rw [htag3]; dsimp only; rw [hnone]; rfl))
      (fun evs_v1 evs_drop evs_p evs_f n hnone =>
        henv_err evs_v1 evs_drop evs_p evs_f n (by rw [htag3]; dsimp only; rw [hnone]; rfl))
      hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
      (by simp only [wp_norm, arm64_norm, htr])
      (by simp only [wp_norm, arm64_norm, hx0]) (by simp only [wp_norm, arm64_norm, hx19])
      (by simp only [wp_norm, arm64_norm, hx21]) (by simp only [wp_norm, arm64_norm, hx22])
      (by simp only [wp_norm, arm64_norm, hx23]) (by simp only [wp_norm, arm64_norm, hx24])
      (by simp only [wp_norm, arm64_norm, hx25]) (by simp only [wp_norm, arm64_norm, hx26])
      (by simp only [wp_norm, arm64_norm, hx27]) (by simp only [wp_norm, arm64_norm, hx28])
      (by simp only [wp_norm, arm64_norm, hx29])
      (by
        rw [protoPqRatchetStateCapOkAt_v1_eq]
        dsimp only [decodeStateLoopCommonPlaced, optProtoPqRatchetInnerCapOkAt, none3Cap, Reg.x19,
          Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
          Reg.x29, Reg.x30]
        sep_ac_rfl)
      (fun w0' v1' rest2 evs_v1 sf P' hv1 hpb hevs_v1 hle2 hsuf2 =>
        hdone w0' ⟨optVn, optCh, some (.v1 v1')⟩ rest2 evs_v1 sf P'
          (by rw [htag3]; dsimp only; rw [hv1]; rfl) hpb hevs_v1 hle2 hsuf2)
  | some inr =>
    cases inr with
    | v1 v1 =>
      dsimp only [pqRatchetStateV1OrDefault, pqRatchetStateV1MsgPtr] at hfits_v1 hfits_err henv_err hdone
      dsimp only at herr_of_none
      rw [protoPqRatchetStateCapOkAt_v1_eq]
      dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced,
        optProtoPqRatchetInnerCapOkAt] at hpc ⊢
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 476#64)
      refine SepWP.fold (optProtoInnerStateCapOkAt_expose_head H_inner A.repAlloc
        (s0.sp - 912#64) rest1.length v1.innerState) (by sep_focus) ?_
      wp_pull_exists
      rename_i q_head
      apply SepWP.pure_elim; intro hne3
      obtain ⟨hbne, hbeq⟩ := head_ne_none3Cap_branch hne3
      wp_steps_sync_pool ((blkPl_325).base + 476#64)
      try simp only [State.setMem_setMem]
      refine SepWP.fold (optProtoInnerStateCapOkAt_fold_head H_inner A.repAlloc
        (s0.sp - 912#64) q_head rest1.length v1.innerState) (by sep_focus) ?_
      apply SepWP.done (by simp only [wp_norm, arm64_norm, hbne, hbeq]) (by simp only [wp_norm, arm64_norm, hrun])
      exact decodeState_v1_some_53678_placed_ofEnv hc hv1_call x st0 st w0 optVn optCh v1 rest1 iwt
        hrest1_le hrest1_suf hlen_bound
        (fun hnone => herr_of_none (by rw [hnone]; rfl)) s0 _ _ R post hpost
        hfits_v1
        (fun evs_v1 n hnone hpb hevs_v1 hn =>
          hfits_err evs_v1 [] n (by rw [htag3]; dsimp only; rw [hnone]; rfl)
            hpb hevs_v1 FreeOnlyEvs.nil hn)
        (fun evs_v1 evs_p evs_f n hnone hpb hevs_v1 hn hp hf =>
          henv_err evs_v1 [] evs_p evs_f n (by rw [htag3]; dsimp only; rw [hnone]; rfl)
            hpb hevs_v1 FreeOnlyEvs.nil hn hp hf)
        hs0A
        (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm, hbne, hbeq])
        (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
        (by simp only [wp_norm, arm64_norm, htr])
        (by simp only [wp_norm, arm64_norm, hx0]) (by simp only [wp_norm, arm64_norm, hx19])
        (by simp only [wp_norm, arm64_norm, hx21]) (by simp only [wp_norm, arm64_norm, hx22])
        (by simp only [wp_norm, arm64_norm, hx23]) (by simp only [wp_norm, arm64_norm, hx24])
        (by simp only [wp_norm, arm64_norm, hx25]) (by simp only [wp_norm, arm64_norm, hx26])
        (by simp only [wp_norm, arm64_norm, hx27]) (by simp only [wp_norm, arm64_norm, hx28])
        (by simp only [wp_norm, arm64_norm, hx29])
        (by
          rw [protoPqRatchetStateCapOkAt_v1_eq]
          dsimp only [decodeStateLoopCommonPlaced, optProtoPqRatchetInnerCapOkAt, Reg.x19, Reg.x20,
            Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29,
            Reg.x30]
          sep_ac_rfl)
        (fun w0' v1' rest2 evs_v1 sf P' hv1 hpb hevs_v1 hle2 hsuf2 =>
          hdone w0' ⟨optVn, optCh, some (.v1 v1')⟩ rest2 evs_v1 sf P'
            (by rw [htag3]; dsimp only; rw [hv1]; rfl) hpb hevs_v1 hle2 hsuf2)

theorem decodeState_v1_entry_535d4_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (curSt : PqRatchetState)
    (rest1 : List (BitVec 8)) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (PqRatchetState.mergeField curSt 3#32 (codecWireTypeToProto iwt) rest1 100).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hfits_v1 : OptInnerStatePolyBound rest1.length (pqRatchetStateV1OrDefault curSt).innerState →
      FitsEnv M lim st
        (V1StateMergeEnv ⟨iwt, pqRatchetStateV1MsgPtr s0.sp curSt, pqRatchetStateV1OrDefault curSt,
          s0.sp - 336#64, s0.sp - 1056#64,
          x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩))
    (hfits_err : ∀ evs_v1 evs_drop n,
      (PqRatchetState.mergeField curSt 3#32 (codecWireTypeToProto iwt) rest1 100).toOption = none →
      OptInnerStatePolyBound rest1.length (pqRatchetStateV1OrDefault curSt).innerState →
      V1StateMergePostEnv ⟨iwt, pqRatchetStateV1MsgPtr s0.sp curSt, pqRatchetStateV1OrDefault curSt,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_v1 →
      FreeOnlyEvs evs_drop → n ≤ 4 →
      FitsEnv M lim (M.stepEvents evs_drop (M.stepEvents evs_v1 st)) (DecodeErrorPushEnv n))
    (henv_err : ∀ evs_v1 evs_drop evs_p evs_f n,
      (PqRatchetState.mergeField curSt 3#32 (codecWireTypeToProto iwt) rest1 100).toOption = none →
      OptInnerStatePolyBound rest1.length (pqRatchetStateV1OrDefault curSt).innerState →
      V1StateMergePostEnv ⟨iwt, pqRatchetStateV1MsgPtr s0.sp curSt, pqRatchetStateV1OrDefault curSt,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_v1 →
      FreeOnlyEvs evs_drop → n ≤ 4 →
      DecodeErrorPushEnv n evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_drop (M.stepEvents evs_v1 st))))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 312#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
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
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (w0' : BitVec 64) (st' : PqRatchetState) (rest2 : List (BitVec 8))
        (evs_v1 : List AllocEvent) (sf : State) (P' : SepProp),
      (PqRatchetState.mergeField curSt 3#32 (codecWireTypeToProto iwt) rest1 100).toOption =
        some (st', rest2) →
      OptInnerStatePolyBound rest1.length (pqRatchetStateV1OrDefault curSt).innerState →
      V1StateMergePostEnv ⟨iwt, pqRatchetStateV1MsgPtr s0.sp curSt, pqRatchetStateV1OrDefault curSt,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_v1 →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 rest2.length →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length st' ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_v1 st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_v1_entry_535d4_placed_ofEnv
    (V1PreEnv := V1StateMergeEnv) (V1PostEnv := V1StateMergePostEnv)
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc.toDecodeStateCalleeContractsPlaced hc.v1StateMerge
    x st0 st w0 curSt rest1 iwt hrest1_le hrest1_suf hlen_bound
    herr_of_none s0 s P R post hpost hfits_v1 hfits_err henv_err hs0A
    hpc hrun hsp htr hx0 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hdone

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlacedBudget
