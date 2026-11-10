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
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopClPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Code-Loaded `VersionNegotiationPB` Merge Loop & Tag-1 Entry (Block `325`)

Re-exports dispatch and body helpers from `VersionNegotiationLoopClPlacedBudgetAux` and proves
budget-threaded code-loaded merge-loop induction (`+1252`), delimited entry (`+216`), and outer
Tag-1 handling (`+184`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopClPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkLib_eq_325 blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.RustHeap (vecHeader)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join suffix_trans)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (codecWireTypeToProto mergeLoopBin protoPrefixStep_versionNegotiationPB_mergeField)
open CryptoVerification.LibsignalSpqrV1
  (ChainPB PqRatchetState VersionNegotiationPB spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred
   bv_len_sub_limit cap_add_one_beq_zero_false
   cmp_len_limit_bne_of_lt cmp_len_limit_of_eq cmp_len_limit_of_gt cmp_len_limit_of_lt
   decodeStatePlacedEntry decodeStatePlacedProg errFrame_parts_fold
   len_ult_of_ge len_ult_of_lt
   mergeLoopBin_eq_limit mergeLoopBin_lt_limit
   mergeMessage_toOption_of_decodeVarint_none mergeMessage_toOption_of_ge
   mergeMessage_toOption_of_lt mergeMessage_toOption_of_ne_lengthDelimited
   optVersionNegotiationPBCapOkAt optVersionNegotiationPB_none_split40
   protoPqRatchetStateCapOkAt protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt
   protoPqRatchetStateCapOkAt_mono protoPqRatchetStateCapOkAt_some_vn_eq
   sp_sub_1392_aligned suffix_eq_drop_of_len_eq truncate32_zeroExtend64_lsr3
   vecU8At_eq_header_heap vecU8At_header_fold vecU8CapOkAt vecU8Heap_cap_lt
   versionNegotiationPBCapOkAt_default_init wt64_ne_two_of_ne_lengthDelimited)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (DecodeVarint2Env)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv decodeVarintSliceEvents)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (DecodeStateEnv DecodeStateIterEnv DecodeStateLoopEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlaced DecodeStateCalleeContractsClPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget (decodeStateErrFramePlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced
   decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitClPlacedBudget
  (decodeState_err_push_53dcc_cl_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced bytesMerge3DetBudgetSpec decodeStateLoopCommonPlaced
   loopCommon_cursor_to_errFrame_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonClPlacedBudget
  (SepWPpIPlaced.call_decodeVarint2_cl)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrClPlacedBudget
  (decodeState_err_53bd8_cl_placed_ofEnv decodeState_err_53d00_cl_placed_ofEnv
   decodeState_err_54030_cl_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlacedBudgetAux
  (decodeState_codecWireTypeToProto_eq err3_env err3_fits1 err3_fits2)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopClPlacedBudgetAux
  (bytesMerge3Det_of_contractsClPlacedX
   decodeState_vn_body_5398c_cl_placed decodeState_vn_body_5398c_cl_placed_ofEnv
   decodeState_vn_dispatch_539b4_cl_placed decodeState_vn_dispatch_539b4_cl_placed_ofEnv)

export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopClPlacedBudgetAux
  (bytesMerge3Det_of_contractsClPlacedX decodeState_vn_dispatch_539b4_cl_placed_ofEnv
   decodeState_vn_dispatch_539b4_cl_placed decodeState_vn_body_5398c_cl_placed_ofEnv
   decodeState_vn_body_5398c_cl_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero truncate32_zeroExtend64_lsr3
attribute [local simp] truncate32_zeroExtend64_lsr3

private theorem decodeErrorFromEnv_iter {maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (h : DecodeErrorFromEnv evs) :
    DecodeStateIterEnv maxLen polyCapBound evs := by
  rw [h]
  exact .of_decodeErrorFrom

private theorem decodeVarint2Env_eq_nil_of_some {bs rest : List (BitVec 8)} {v : BitVec 64}
    {evs : List AllocEvent}
    (hdv : decodeVarint bs = some (v, rest)) (hevs : DecodeVarint2Env bs evs) :
    evs = [] := by
  simp only [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hdv] at hevs
  exact hevs

/-! ## 1. Inlined `VersionNegotiationPB` Merge Loop (`+1252`) -/

/-- Envelope-parameterized code-loaded inlined `VersionNegotiationPB` merge loop at `+1252`,
proved by induction on `fuel`. -/
theorem decodeState_vn_loop_53980_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {maxLen polyCapBound : Nat}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (hbm : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3DetBudgetSpec A lim)))
    (x : DecodeStateGhost) (st0 : M.σ) (w0 : BitVec 64)
    (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (limit : Nat) (hlim_bound : limit < 2 ^ 32) (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hx_max : x.st.bytes.length ≤ maxLen) (hmax : maxLen < 2 ^ 64)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hs0A : s0.spAligned = true) :
    ∀ (fuel : Nat) (vn : VersionNegotiationPB) (cur : List (BitVec 8)) (st : M.σ)
      (s : State) (P : SepProp),
      cur.length - limit ≤ fuel → cur.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes cur →
      (mergeLoopBin VersionNegotiationPB.mergeField (cur.length - limit) vn cur limit 99 = none →
        spqrDecodeState x.st.bytes = .error .stateDecode) →
      FitsEnv M lim st (DecodeStateLoopEnv (4 * cur.length + 8) maxLen polyCapBound) →
      (∀ evs_err,
        DecodeStateLoopEnv (4 * cur.length + 8) maxLen polyCapBound evs_err →
        ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = M.stepEvents evs_err st) →
      s.pc = decodeStatePlacedEntry + 1252#64 →
      s.status = .Running → s.sp = s0.sp - 1392#64 → TraceVRegs s s0 →
      s.readReg64 .x19 = x.outPtr → s.readReg64 .x20 = BitVec.ofNat 64 limit →
      s.readReg64 .x21 = 0x8000000000000006#64 → s.readReg64 .x22 = s0.sp - 1040#64 →
      s.readReg64 .x23 = -1#64 → s.readReg64 .x24 = s0.sp - 912#64 →
      s.readReg64 .x25 = s0.sp - 688#64 → s.readReg64 .x26 = -2#64 →
      s.readReg64 .x27 = v27 → s.readReg64 .x28 = 1#64 → s.readReg64 .x29 = s0.sp - 96#64 →
      P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length
          ⟨some vn, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 s →
      (∀ (vn' : VersionNegotiationPB) (rest : List (BitVec 8)) (evs_loop : List AllocEvent)
          (sf : State) (P' : SepProp),
        mergeLoopBin VersionNegotiationPB.mergeField (cur.length - limit) vn cur limit 99 =
          some vn' →
        DecodeStateLoopEnv (4 * (cur.length - rest.length)) maxLen polyCapBound evs_loop →
        rest.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes rest → rest.length = limit →
        sf.pc = decodeStatePlacedEntry + 1576#64 →
        sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
        sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 rest.length →
        sf.readReg64 .x21 = 0x8000000000000006#64 →
        sf.readReg64 .x22 = s0.sp - 1040#64 → sf.readReg64 .x23 = -1#64 →
        sf.readReg64 .x24 = s0.sp - 912#64 → sf.readReg64 .x25 = s0.sp - 688#64 →
        sf.readReg64 .x26 = -2#64 → sf.readReg64 .x27 = v27 →
        sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
        P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
          sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest ∗
          protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest.length
            ⟨some vn', optCh, inner⟩ ∗
          memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
          decodeStateLoopCommonPlaced A lim (M.stepEvents evs_loop st) x s0 sf →
        SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
          (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  intro fuel
  induction fuel with
  | zero =>
    intro vn cur st s P hfuel hcur_le hcur_suf herr_of_none hfits henv_err
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hdone
    have hle : cur.length ≤ limit := by omega
    have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
    subst hP
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, sliceCursorAfter] at hpc ⊢
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · have ⟨hult, hule, hbeq⟩ := cmp_len_limit_of_eq heq
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1576#64)
      wp_steps 4
      apply SepWP.done (by simp only [arm64_norm, hult, hule, hbeq])
        (by simp only [arm64_norm, hrun])
      exact hdone vn cur [] _ _
        (mergeLoopBin_eq_limit VersionNegotiationPB.mergeField (cur.length - limit) vn cur limit 99
          heq)
        .nil hcur_le hcur_suf heq
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hbeq])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19]) (by rw [heq]; simp only [arm64_norm, hx20])
        (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
        (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
        (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
        (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
        (by simp only [arm64_norm, hx29])
        (by
          dsimp only [sliceCursorAfter, decodeStateLoopCommonPlaced]
          simp only [M.stepEvents_nil, wp_norm, arm64_norm]
          try sep_ac_rfl)
    · have ⟨hult, hule, hbeq⟩ := cmp_len_limit_of_lt hlt (by omega)
      have hbne := cmp_len_limit_bne_of_lt hlt (by omega)
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2964#64)
      wp_steps 5
      refine SepWP.fold (loopCommon_cursor_to_errFrame_placed H_inner A lim st x cur cur.length
        ⟨some vn, optCh, inner⟩ s0 s)
        (by dsimp only [sliceCursorAfter]; sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, hult, hule, hbeq, hbne])
        (by simp only [arm64_norm, hrun])
      exact decodeState_err_54030_cl_placed_ofEnv hc x st0 st
        ⟨some vn, optCh, inner⟩ w0 s0 _ _ R post hpost
        (herr_of_none (mergeLoopBin_lt_limit VersionNegotiationPB.mergeField (cur.length - limit)
          vn cur limit 99 hlt))
        (err3_fits1 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits)
        (err3_fits2 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits)
        (err3_env (by omega) (fun _ => decodeErrorFromEnv_iter) henv_err)
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hbeq, hbne])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx21])
        (by
          unfold decodeStateErrFramePlaced
          dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26,
            Reg.x27, Reg.x28, Reg.x29, Reg.x30]
          simp only [wp_norm, arm64_norm]
          try sep_ac_rfl)
  | succ fuel ih =>
    intro vn cur st s P hfuel hcur_le hcur_suf herr_of_none hfits henv_err
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hdone
    have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
    by_cases hle : cur.length ≤ limit
    · subst hP
      dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, sliceCursorAfter] at hpc ⊢
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · have ⟨hult, hule, hbeq⟩ := cmp_len_limit_of_eq heq
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1576#64)
        wp_steps 4
        apply SepWP.done (by simp only [arm64_norm, hult, hule, hbeq])
          (by simp only [arm64_norm, hrun])
        exact hdone vn cur [] _ _
          (mergeLoopBin_eq_limit VersionNegotiationPB.mergeField (cur.length - limit) vn cur
            limit 99 heq)
          .nil hcur_le hcur_suf heq
          (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hbeq])
          (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
          (by simp only [arm64_norm, htr])
          (by simp only [arm64_norm, hx19]) (by rw [heq]; simp only [arm64_norm, hx20])
          (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
          (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
          (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
          (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
          (by simp only [arm64_norm, hx29])
          (by
            dsimp only [sliceCursorAfter, decodeStateLoopCommonPlaced]
            simp only [M.stepEvents_nil, wp_norm, arm64_norm]
            try sep_ac_rfl)
      · have ⟨hult, hule, hbeq⟩ := cmp_len_limit_of_lt hlt (by omega)
        have hbne := cmp_len_limit_bne_of_lt hlt (by omega)
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2964#64)
        wp_steps 5
        refine SepWP.fold (loopCommon_cursor_to_errFrame_placed H_inner A lim st x cur cur.length
          ⟨some vn, optCh, inner⟩ s0 s)
          (by dsimp only [sliceCursorAfter]; sep_focus) ?_
        apply SepWP.done (by simp only [arm64_norm, hult, hule, hbeq, hbne])
          (by simp only [arm64_norm, hrun])
        exact decodeState_err_54030_cl_placed_ofEnv hc x st0 st
          ⟨some vn, optCh, inner⟩ w0 s0 _ _ R post hpost
          (herr_of_none (mergeLoopBin_lt_limit VersionNegotiationPB.mergeField (cur.length - limit)
            vn cur limit 99 hlt))
          (err3_fits1 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits)
          (err3_fits2 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits)
          (err3_env (by omega) (fun _ => decodeErrorFromEnv_iter) henv_err)
          (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hbeq, hbne])
          (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
          (by simp only [arm64_norm, htr])
          (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx21])
          (by
            unfold decodeStateErrFramePlaced
            dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26,
              Reg.x27, Reg.x28, Reg.x29, Reg.x30]
            simp only [wp_norm, arm64_norm]
            try sep_ac_rfl)
    · have ⟨hult, hule⟩ := cmp_len_limit_of_gt hle (by omega)
      subst hP
      dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, sliceCursorAfter] at hpc ⊢
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1264#64)
      wp_steps 3
      apply SepWP.done (by simp only [arm64_norm, hult, hule]) (by simp only [arm64_norm, hrun])
      refine decodeState_vn_body_5398c_cl_placed_ofEnv
        (maxLen := maxLen) (polyCapBound := polyCapBound)
        (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := v27)
        hc hbm x st0 st w0 vn optCh inner cur limit
        hle hcur_le hcur_suf hlen_bound hx_max hmax herr_of_none s0 _ _ R post hpost
        hfits henv_err hs0A
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule])
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
          try sep_ac_rfl)
        ?_
      intro vn' rest2 evs_step sf P' hlt2 hle2 hsuf2 hstep_env hmerge_eq
        hpc' hrun' hsp' htr' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28' hx29' hP'
      have hfuel_split :
          4 * (cur.length - rest2.length) + (4 * rest2.length + 8) = 4 * cur.length + 8 := by
        omega
      have hfits' :
          FitsEnv M lim (M.stepEvents evs_step st)
            (DecodeStateLoopEnv (4 * rest2.length + 8) maxLen polyCapBound) :=
        SpecsBudget.FitsEnv.decodeStateLoop_split hstep_env (hfuel_split ▸ hfits)
      have henv_err' : ∀ evs_err,
          DecodeStateLoopEnv (4 * rest2.length + 8) maxLen polyCapBound evs_err →
          ∃ evs, PostEnv x evs ∧
            M.stepEvents evs st0 = M.stepEvents evs_err (M.stepEvents evs_step st) := by
        intro evs_err h_err
        obtain ⟨evs, hpost_evs, hstep⟩ :=
          henv_err (evs_step ++ evs_err) (hfuel_split ▸ hstep_env.append h_err)
        exact ⟨evs, hpost_evs, by rw [hstep, M.stepEvents_append]⟩
      refine ih vn' rest2 (M.stepEvents evs_step st) sf P' (by omega) hle2 hsuf2
        (fun hnone => herr_of_none (by rw [hmerge_eq, hnone]))
        hfits' henv_err'
        hpc' hrun' hsp' htr' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28' hx29' hP'
        ?_
      intro vn'' rest3 evs_rest sf' P'' hok hrest_env hrest3_le hrest3_suf hrest3_eq
        hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hx27''
        hx28'' hx29'' hP''
      have hrest3_le_rest2 : rest3.length ≤ rest2.length := by
        rw [hrest3_eq]
        apply Nat.not_lt.mp
        intro hlt_lim
        have hnone := mergeLoopBin_lt_limit VersionNegotiationPB.mergeField (rest2.length - limit)
          vn' rest2 limit 99 hlt_lim
        rw [hok] at hnone
        cases hnone
      have hcomb_env :
          DecodeStateLoopEnv (4 * (cur.length - rest3.length)) maxLen polyCapBound
            (evs_step ++ evs_rest) :=
        (hstep_env.append hrest_env).mono_fuel (by omega)
      exact hdone vn'' rest3 (evs_step ++ evs_rest) sf' P''
        (by rw [hmerge_eq, hok]) hcomb_env hrest3_le hrest3_suf hrest3_eq
        hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hx27''
        hx28'' hx29'' (by rw [M.stepEvents_append]; exact hP'')

theorem decodeState_vn_loop_53980_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 : M.σ) (w0 : BitVec 64)
    (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (limit : Nat) (hlim_bound : limit < 2 ^ 32) (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true) :
    ∀ (fuel : Nat) (vn : VersionNegotiationPB) (cur : List (BitVec 8)) (st : M.σ)
      (s : State) (P : SepProp),
      cur.length - limit ≤ fuel → cur.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes cur →
      (mergeLoopBin VersionNegotiationPB.mergeField (cur.length - limit) vn cur limit 99 = none →
        spqrDecodeState x.st.bytes = .error .stateDecode) →
      FitsEnv M lim st
        (DecodeStateLoopEnv (4 * cur.length + 8) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
      (∀ evs_err,
        DecodeStateLoopEnv (4 * cur.length + 8) x.st.bytes.length
          (2 * x.st.bytes.length + 16) evs_err →
        ∃ evs, DecodeStateEnv x evs ∧ M.stepEvents evs st0 = M.stepEvents evs_err st) →
      s.pc = decodeStatePlacedEntry + 1252#64 →
      s.status = .Running → s.sp = s0.sp - 1392#64 → TraceVRegs s s0 →
      s.readReg64 .x19 = x.outPtr → s.readReg64 .x20 = BitVec.ofNat 64 limit →
      s.readReg64 .x21 = 0x8000000000000006#64 → s.readReg64 .x22 = s0.sp - 1040#64 →
      s.readReg64 .x23 = -1#64 → s.readReg64 .x24 = s0.sp - 912#64 →
      s.readReg64 .x25 = s0.sp - 688#64 → s.readReg64 .x26 = -2#64 →
      s.readReg64 .x27 = v27 → s.readReg64 .x28 = 1#64 → s.readReg64 .x29 = s0.sp - 96#64 →
      P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length
          ⟨some vn, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 s →
      (∀ (vn' : VersionNegotiationPB) (rest : List (BitVec 8)) (evs_loop : List AllocEvent)
          (sf : State) (P' : SepProp),
        mergeLoopBin VersionNegotiationPB.mergeField (cur.length - limit) vn cur limit 99 =
          some vn' →
        DecodeStateLoopEnv (4 * (cur.length - rest.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16) evs_loop →
        rest.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes rest → rest.length = limit →
        sf.pc = decodeStatePlacedEntry + 1576#64 →
        sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
        sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 rest.length →
        sf.readReg64 .x21 = 0x8000000000000006#64 →
        sf.readReg64 .x22 = s0.sp - 1040#64 → sf.readReg64 .x23 = -1#64 →
        sf.readReg64 .x24 = s0.sp - 912#64 → sf.readReg64 .x25 = s0.sp - 688#64 →
        sf.readReg64 .x26 = -2#64 → sf.readReg64 .x27 = v27 →
        sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
        P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
          sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest ∗
          protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest.length
            ⟨some vn', optCh, inner⟩ ∗
          memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
          decodeStateLoopCommonPlaced A lim (M.stepEvents evs_loop st) x s0 sf →
        SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
          (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_vn_loop_53980_cl_placed_ofEnv
    (maxLen := x.st.bytes.length) (polyCapBound := 2 * x.st.bytes.length + 16)
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc.toDecodeStateCalleeContractsClPlaced (bytesMerge3Det_of_contractsClPlacedX hc)
    x st0 w0 optCh inner limit hlim_bound hlen_bound (Nat.le_refl _) (by omega)
    s0 R post hpost hs0A

/-! ## 2. Delimited `VersionNegotiationPB::merge` (`+216`) & Outer Tag-1 Entry (`+184`) -/

attribute [local irreducible]
  mergeMessage mergeLoopBin CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState

/-- Envelope-parameterized code-loaded delimited `VersionNegotiationPB::merge` entry at `+216`. -/
theorem decodeState_vn_merge_53574_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {maxLen polyCapBound : Nat}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (hbm : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3DetBudgetSpec A lim)))
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hx_max : x.st.bytes.length ≤ maxLen) (hmax : maxLen < 2 ^ 64)
    (herr_of_none :
      (mergeMessage VersionNegotiationPB.mergeField (codecWireTypeToProto iwt) vn rest1
        100).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hfits : FitsEnv M lim st (DecodeStateLoopEnv (4 * rest1.length + 8) maxLen polyCapBound))
    (henv_err : ∀ evs_err,
      DecodeStateLoopEnv (4 * rest1.length + 8) maxLen polyCapBound evs_err →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = M.stepEvents evs_err st)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 iwt.toNat)
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
        ⟨some vn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (vn' : VersionNegotiationPB) (rest2 : List (BitVec 8))
        (evs_vn : List AllocEvent) (sf : State) (P' : SepProp),
      (mergeMessage VersionNegotiationPB.mergeField (codecWireTypeToProto iwt) vn rest1
        100).toOption = some (vn', rest2) →
      DecodeStateLoopEnv (4 * (rest1.length - rest2.length)) maxLen polyCapBound evs_vn →
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
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨some vn', optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_vn st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  by_cases hwt : iwt = .lengthDelimited
  · subst hwt
    dsimp only [codecWireTypeToProto] at herr_of_none hdone
    have hdv_call := hc.decodeVarint2
    subst hP
    rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf]
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced,
      WireType.toNat, Reg.x0] at hpc hdv_call hx0 ⊢
    have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
    apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
    wp_steps_sync_pool (lsmpl.base 291)
    try simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
    have hsp1048 : s0.sp - 1056#64 + 8#64 = s0.sp - 1048#64 := by bv_omega
    refine SepWPpIPlaced.call_decodeVarint2_cl hdv_call
      (s0.sp - 336#64) (s0.sp - 1056#64)
      (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1 st
      (ret_pc := (blkPl_325).base + 232#64)
      (hpc := by simp only [wp_norm, arm64_norm]) (hrun := by simp only [wp_norm, arm64_norm, hrun])
      (hsp := by simp only [wp_norm, arm64_norm, hsp]) (hs0A := hs0A)
      (hlr := by simp only [wp_norm, arm64_norm]) (htr := by simp only [wp_norm, arm64_norm, htr])
      (hx0 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
      (hlen := by omega)
      (hfits := err3_fits1 (by omega) (fun _ => .of_decodeVarint2) hfits)
      (hP := by sep_focus) ?_ ?_
    · intro s1 len64 rest2 evs_dv hdv hevs_dv hlt2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_len
      have hevs_nil := decodeVarint2Env_eq_nil_of_some hdv hevs_dv
      subst hevs_nil
      simp only [M.stepEvents_nil]
      have hle2 : rest2.length ≤ rest1.length := Nat.le_of_lt hlt2
      have hrest2_le : rest2.length ≤ x.st.bytes.length := Nat.le_trans hle2 hrest1_le
      have hrest2_suf : IsDropSuffix x.st.bytes rest2 :=
        suffix_trans hrest1_le hrest1_suf hle2 hsuf2
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
        hx28_1, hx29_1, hvregs_1⟩
      simp only [arm64_norm, wp_norm] at hx0_0 hx1_len hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
      simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      have hsp1A : s1.spAligned = true := by
        rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
      by_cases hlt_len : rest2.length < len64.toNat
      · have ⟨hult, hule⟩ := len_ult_of_lt hlt_len
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2148#64)
        refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
          hrest1_le hrest1_suf hle2) (by sep_focus) ?_
        dsimp only [sliceCursorAfter]
        wp_steps 5
        refine SepWP.fold (loopCommon_cursor_to_errFrame_placed H_inner A lim st x rest2
          rest1.length ⟨some vn, optCh, inner⟩ s0 s1)
          (by dsimp only [sliceCursorAfter, decodeStateLoopCommonPlaced]; sep_focus) ?_
        apply SepWP.done (by simp only [arm64_norm, hx0_0, hult, hule])
          (by simp only [arm64_norm, hrun1])
        exact decodeState_err_53d00_cl_placed_ofEnv hc x st0 st
          ⟨some vn, optCh, inner⟩ w0 s0 _ _ R post hpost
          (herr_of_none (mergeMessage_toOption_of_lt VersionNegotiationPB.mergeField hdv hlt_len))
          (err3_fits1 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits)
          (err3_fits2 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits)
          (err3_env (by omega) (fun _ => decodeErrorFromEnv_iter) henv_err)
          (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hult, hule])
          (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
          (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
          (by
            unfold decodeStateErrFramePlaced
            dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26,
              Reg.x27, Reg.x28, Reg.x29, Reg.x30]
            simp only [wp_norm, arm64_norm]
            try sep_ac_rfl)
      · have ⟨hult, hule⟩ := len_ult_of_ge hlt_len (by omega)
        have hsub_lim := bv_len_sub_limit hlt_len
        have hmm_eq := mergeMessage_toOption_of_ge protoPrefixStep_versionNegotiationPB_mergeField
          (m := vn) (depth' := 99) hdv hlt_len
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1252#64)
        refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
          hrest1_le hrest1_suf hle2) (by sep_focus) ?_
        dsimp only [sliceCursorAfter]
        wp_steps 4
        refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
          (a := s0.sp - 1040#64) (rem1 := rest1.length) (rem2 := rest2.length)
          (st := ⟨some vn, optCh, inner⟩) hle2) (by sep_focus) ?_
        apply SepWP.done (by simp only [arm64_norm, hx0_0, hult, hule])
          (by simp only [arm64_norm, hrun1])
        refine decodeState_vn_loop_53980_cl_placed_ofEnv
          (maxLen := maxLen) (polyCapBound := polyCapBound)
          (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := v27)
          hc hbm x st0 w0 optCh inner (rest2.length - len64.toNat)
          (by omega) hlen_bound hx_max hmax s0 R post hpost hs0A
          (rest2.length - (rest2.length - len64.toNat)) vn rest2 st _ _
          (Nat.le_refl _) hrest2_le hrest2_suf
          (fun hnone => herr_of_none (by rw [hmm_eq, hnone]; rfl))
          (SpecsBudget.FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _)
            hfits)
          (fun evs_err h_err => henv_err evs_err (h_err.mono_fuel (by omega)))
          (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hult, hule])
          (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
          (by simp only [arm64_norm, htr1])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, hsub_lim, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by
            dsimp only [decodeStateLoopCommonPlaced, sliceCursorAfter]
            rw [hsp1048]
            simp only [wp_norm, arm64_norm]
            try sep_ac_rfl)
          ?_
        intro vn' rest3 evs_loop sf P' hloop_ok hloop_env hrest3_le hrest3_suf hrest3_eq
        have hdrop : rest3 = rest2.drop len64.toNat :=
          suffix_eq_drop_of_len_eq hrest2_le hrest2_suf hlt_len hrest3_le hrest3_suf hrest3_eq
        have hle3_2 : rest3.length ≤ rest2.length := by omega
        have hle3_1 : rest3.length ≤ rest1.length := Nat.le_trans hle3_2 hle2
        have hsuf3_2 : IsDropSuffix rest2 rest3 := by
          unfold IsDropSuffix
          rw [hrest3_eq, Nat.sub_sub_self (Nat.not_lt.mp hlt_len)]
          exact hdrop
        have hsuf3_1 : IsDropSuffix rest1 rest3 :=
          suffix_trans hle2 hsuf2 hle3_2 hsuf3_2
        have hok_mm :
            (mergeMessage VersionNegotiationPB.mergeField
              .lengthDelimited vn rest1 100).toOption = some (vn', rest3) := by
          rw [hmm_eq, hloop_ok, ← hdrop]; rfl
        exact hdone vn' rest3 evs_loop sf P' hok_mm
          (hloop_env.mono_fuel (by omega)) hle3_1 hsuf3_1
    · intro s1 evs_dv hdv hevs_dv hpc1 hrun1 hsp1 htr1 hcs1 hx0_1 hx1_ne
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
        hx28_1, hx29_1, hvregs_1⟩
      simp only [arm64_norm, wp_norm] at hx0_1 hx1_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
      simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2352#64)
      wp_steps 2
      wp_if hcbz
      · exact absurd hcbz hx1_ne
      · wp_steps 1
        refine SepWP.fold (errFrame_parts_fold A.repAlloc x s0 hrest1_le hrest1_suf)
          (by sep_focus) ?_
        refine SepWP.fold (protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner
          A.repAlloc (s0.sp - 1040#64) rest1.length ⟨some vn, optCh, inner⟩) (by sep_focus) ?_
        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
        exact decodeState_err_push_53dcc_cl_placed_ofEnv hc x st0
          (M.stepEvents evs_dv st) ⟨some vn, optCh, inner⟩ w0 0 s0 _ _ R post hpost
          (herr_of_none (mergeMessage_toOption_of_decodeVarint_none VersionNegotiationPB.mergeField
            hdv))
          (by decide)
          (err3_fits2 (by omega) (fun _ => .of_decodeVarint2) hfits evs_dv hevs_dv)
          (fun evs_p evs_f hp hfree =>
            err3_env (by omega) (fun _ => .of_decodeVarint2) henv_err evs_dv evs_p evs_f
              hevs_dv hp hfree)
          (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
          (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
          (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
          (by
            dsimp only [Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
              Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
            simp only [wp_norm, arm64_norm]
            try sep_ac_rfl)
  · have ⟨hbne, hbeq⟩ := wt64_ne_two_of_ne_lengthDelimited hwt
    subst hP
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, Reg.x0] at hpc hx0 ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1852#64)
    wp_steps 2
    refine SepWP.fold (loopCommon_cursor_to_errFrame_placed H_inner A lim st x rest1 rest1.length
      ⟨some vn, optCh, inner⟩ s0 s) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, Reg.x0, hx0, hbne, hbeq])
      (by simp only [arm64_norm, hrun])
    exact decodeState_err_53bd8_cl_placed_ofEnv hc x st0 st
      ⟨some vn, optCh, inner⟩ w0 s0 _ _ R post hpost
      (herr_of_none (by
        rw [← decodeState_codecWireTypeToProto_eq]
        exact mergeMessage_toOption_of_ne_lengthDelimited VersionNegotiationPB.mergeField hwt))
      (err3_fits1 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits)
      (err3_fits2 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits)
      (err3_env (by omega) (fun _ => decodeErrorFromEnv_iter) henv_err)
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, Reg.x0, hx0, hbne, hbeq])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx21])
      (by
        unfold decodeStateErrFramePlaced
        dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26,
          Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        simp only [wp_norm, arm64_norm]
        try sep_ac_rfl)

theorem decodeState_vn_merge_53574_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage VersionNegotiationPB.mergeField (codecWireTypeToProto iwt) vn rest1
        100).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hfits : FitsEnv M lim st
      (DecodeStateLoopEnv (4 * rest1.length + 8) x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (henv_err : ∀ evs_err,
      DecodeStateLoopEnv (4 * rest1.length + 8) x.st.bytes.length (2 * x.st.bytes.length + 16)
        evs_err →
      ∃ evs, DecodeStateEnv x evs ∧ M.stepEvents evs st0 = M.stepEvents evs_err st)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 iwt.toNat)
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
        ⟨some vn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (vn' : VersionNegotiationPB) (rest2 : List (BitVec 8))
        (evs_vn : List AllocEvent) (sf : State) (P' : SepProp),
      (mergeMessage VersionNegotiationPB.mergeField (codecWireTypeToProto iwt) vn rest1
        100).toOption = some (vn', rest2) →
      DecodeStateLoopEnv (4 * (rest1.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) evs_vn →
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
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨some vn', optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_vn st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_vn_merge_53574_cl_placed_ofEnv
    (maxLen := x.st.bytes.length) (polyCapBound := 2 * x.st.bytes.length + 16)
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc.toDecodeStateCalleeContractsClPlaced (bytesMerge3Det_of_contractsClPlacedX hc)
    x st0 st w0 vn optCh inner rest1 iwt hrest1_le hrest1_suf hlen_bound
    (Nat.le_refl _) (by omega) herr_of_none s0 s P R post hpost hfits henv_err hs0A
    hpc hrun hsp htr hx0 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hdone

/-- Envelope-parameterized code-loaded outer loop tag-1 (`PqRatchetState::version_negotiation`,
`+184`) reaching `entry + 1576`. -/
theorem decodeState_vn_entry_53554_cl_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {maxLen polyCapBound : Nat}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext)
    (hbm : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3DetBudgetSpec A lim)))
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (optCh : Option ChainPB)
    (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hx_max : x.st.bytes.length ≤ maxLen) (hmax : maxLen < 2 ^ 64)
    (herr_of_none :
      (mergeMessage VersionNegotiationPB.mergeField (codecWireTypeToProto iwt)
        (optVn.getD default) rest1 100).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hfits : FitsEnv M lim st (DecodeStateLoopEnv (4 * rest1.length + 8) maxLen polyCapBound))
    (henv_err : ∀ evs_err,
      DecodeStateLoopEnv (4 * rest1.length + 8) maxLen polyCapBound evs_err →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs st0 = M.stepEvents evs_err st)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 184#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 iwt.toNat)
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
        ⟨optVn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (vn' : VersionNegotiationPB) (rest2 : List (BitVec 8))
        (evs_vn : List AllocEvent) (sf : State) (P' : SepProp),
      (mergeMessage VersionNegotiationPB.mergeField (codecWireTypeToProto iwt)
        (optVn.getD default) rest1 100).toOption = some (vn', rest2) →
      DecodeStateLoopEnv (4 * (rest1.length - rest2.length)) maxLen polyCapBound evs_vn →
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
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨some vn', optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_vn st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  cases optVn with
  | none =>
    subst hP
    unfold protoPqRatchetStateCapOkAt optVersionNegotiationPBCapOkAt
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced,
      Option.getD] at hpc herr_of_none hdone ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 184#64)
    refine SepWP.fold (optVersionNegotiationPB_none_split40 (s0.sp - 1040#64)) (by sep_focus) ?_
    apply SepWP.done (by exact hpc) (by exact hrun)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPpIPlaced.exists_elim; intro w1
    apply SepWPpIPlaced.exists_elim; intro w2
    apply SepWPpIPlaced.exists_elim; intro w3
    apply SepWPpIPlaced.exists_elim; intro w4
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 216#64)
    wp_steps_sync_pool ((blkPl_325).base + 216#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold (versionNegotiationPBCapOkAt_default_init A.repAlloc (s0.sp - 1040#64)
      rest1.length) (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    exact decodeState_vn_merge_53574_cl_placed_ofEnv
      (maxLen := maxLen) (polyCapBound := polyCapBound)
      (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := v27)
      hc hbm x st0 st w0 default optCh inner rest1 iwt
      hrest1_le hrest1_suf hlen_bound hx_max hmax herr_of_none s0 _ _ R post hpost
      hfits henv_err hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by simp only [wp_norm, arm64_norm, hsp])
      (by simp only [wp_norm, arm64_norm, htr])
      (by simp only [wp_norm, arm64_norm, hx0])
      (by simp only [wp_norm, arm64_norm, hx19])
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
        unfold protoPqRatchetStateCapOkAt optVersionNegotiationPBCapOkAt
        dsimp only [decodeStateLoopCommonPlaced]
        try sep_ac_rfl)
      hdone
  | some vn =>
    subst hP
    rw [protoPqRatchetStateCapOkAt_some_vn_eq]
    unfold vecU8CapOkAt
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, Option.getD]
      at hpc herr_of_none hdone ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 216#64)
    wp_pull_exists
    rename_i cap ptr
    wp_focus_pure; intro hcap
    rw [vecU8At_eq_header_heap]
    refine SepWP.fold (vecU8Heap_cap_lt A.repAlloc cap ptr vn.authKey) (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    unfold vecHeader
    have hcmn : (cap + 1#64 != 0#64) = true := by
      rw [bne_iff_ne, ← beq_eq_false_iff_ne, Bool.eq_false_iff]
      exact cap_add_one_beq_zero_false hcap_lt
    wp_steps 3
    refine SepWP.fold (vecU8At_header_fold A.repAlloc (s0.sp - 1040#64) cap ptr vn.authKey
      rest1.length hcap) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hcmn]) (by simp only [arm64_norm, hrun])
    exact decodeState_vn_merge_53574_cl_placed_ofEnv
      (maxLen := maxLen) (polyCapBound := polyCapBound)
      (PreEnv := PreEnv) (PostEnv := PostEnv) (v27 := v27)
      hc hbm x st0 st w0 vn optCh inner rest1 iwt
      hrest1_le hrest1_suf hlen_bound hx_max hmax herr_of_none s0 _ _ R post hpost
      hfits henv_err hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hcmn])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx21])
      (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23])
      (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx25])
      (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm, hx27])
      (by simp only [arm64_norm, hx28]) (by simp only [arm64_norm, hx29])
      (by
        rw [protoPqRatchetStateCapOkAt_some_vn_eq]
        dsimp only [decodeStateLoopCommonPlaced]
        simp only [wp_norm, arm64_norm]
        try sep_ac_rfl)
      hdone

theorem decodeState_vn_entry_53554_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (optCh : Option ChainPB)
    (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (mergeMessage VersionNegotiationPB.mergeField (codecWireTypeToProto iwt)
        (optVn.getD default) rest1 100).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hfits : FitsEnv M lim st
      (DecodeStateLoopEnv (4 * rest1.length + 8) x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (henv_err : ∀ evs_err,
      DecodeStateLoopEnv (4 * rest1.length + 8) x.st.bytes.length (2 * x.st.bytes.length + 16)
        evs_err →
      ∃ evs, DecodeStateEnv x evs ∧ M.stepEvents evs st0 = M.stepEvents evs_err st)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 184#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 iwt.toNat)
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
        ⟨optVn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (vn' : VersionNegotiationPB) (rest2 : List (BitVec 8))
        (evs_vn : List AllocEvent) (sf : State) (P' : SepProp),
      (mergeMessage VersionNegotiationPB.mergeField (codecWireTypeToProto iwt)
        (optVn.getD default) rest1 100).toOption = some (vn', rest2) →
      DecodeStateLoopEnv (4 * (rest1.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) evs_vn →
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
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨some vn', optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_vn st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_vn_entry_53554_cl_placed_ofEnv
    (maxLen := x.st.bytes.length) (polyCapBound := 2 * x.st.bytes.length + 16)
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc.toDecodeStateCalleeContractsClPlaced (bytesMerge3Det_of_contractsClPlacedX hc)
    x st0 st w0 optVn optCh inner rest1 iwt hrest1_le hrest1_suf hlen_bound
    (Nat.le_refl _) (by omega) herr_of_none s0 s P R post hpost hfits henv_err hs0A
    hpc hrun hsp htr hx0 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hdone

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopClPlacedBudget
