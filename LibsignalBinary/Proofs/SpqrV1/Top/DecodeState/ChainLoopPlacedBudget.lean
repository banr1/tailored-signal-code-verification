/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainPushPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state` (Block `325`): Budget Relocatable `ChainPB` Merge Loop & Tag-2 Handler

Budget-threaded relocatable `[LibsignalPlacement]` proofs of the inductive `ChainPB` merge loop (`+508`),
length-delimited entry (`+284`), and outer tag-2 handler (`+244`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkLib_eq_325 blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.RustHeap (RustAlloc vecAt vecBuf vecHeader vecOf)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join suffix_trans)
open CryptoVerification.SpqrV1.ProtoRepr
  (chainEpochPBAt chainEpochPBSize chainLinksVecAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (codecWireTypeToProto mergeLoopBin protoPrefixStep_chainPB_mergeField)
open CryptoVerification.LibsignalSpqrV1
  (ChainEpochPB ChainPB PqRatchetState VersionNegotiationPB spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred
   bv_len_sub_limit cap_add_one_beq_zero_false
   chainPBCapOkAt_default_init
   cmp_len_limit_bne_of_lt cmp_len_limit_of_eq cmp_len_limit_of_gt cmp_len_limit_of_lt
   decodeStatePlacedEntry decodeStatePlacedProg errFrame_parts_fold
   len_ult_of_ge len_ult_of_lt memRegion_56_eq_quads7At
   mergeLoopBin_eq_limit mergeLoopBin_lt_limit
   mergeMessage_toOption_of_decodeVarint_none mergeMessage_toOption_of_ge
   mergeMessage_toOption_of_lt mergeMessage_toOption_of_ne_lengthDelimited
   optChainPBCapOkAt
   protoPqRatchetStateCapOkAt protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt
   protoPqRatchetStateCapOkAt_mono quads7At
   sp_sub_1392_aligned suffix_eq_drop_of_len_eq truncate32_zeroExtend64_lsr3
   wt64_ne_two_of_ne_lengthDelimited)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (DecodeStateEnv DecodeStateLoopEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStateCalleeContractsPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget (decodeStateErrFramePlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced
   decodeStatePostPlacedOfEnv decodeState_err_push_53cdc_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudget
  (decodeState_err_53ad8_placed_ofEnv decodeState_err_53bac_placed_ofEnv
   decodeState_err_53cc8_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced decodeStateLoopCommonPlaced loopCommon_cursor_to_errFrame_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStepPlacedBudget
  (protoPqRatchetStateCapOkAt_some_ch_eq_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoopPlacedBudgetAux
  (decodeState_codecWireTypeToProto_eq err3_env err3_fits1 err3_fits2)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlacedBudgetAux
  (acc_henv_err decodeErrorFromEnv_iter decodeState_chain_body_536a4_placed
   decodeState_chain_body_536a4_placed_ofEnv decodeState_chain_dispatch_536cc_placed
   decodeState_chain_dispatch_536cc_placed_ofEnv decodeVarint2Env_eq_nil_of_some)

export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlacedBudgetAux
  (decodeState_chain_dispatch_536cc_placed_ofEnv decodeState_chain_dispatch_536cc_placed
   decodeState_chain_body_536a4_placed_ofEnv decodeState_chain_body_536a4_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero truncate32_zeroExtend64_lsr3
attribute [local simp] truncate32_zeroExtend64_lsr3

/-! ## Full `ChainPB` Merge Loop (`+508`) -/

/-- Envelope-parameterized inlined `ChainPB` merge loop at `+508`, proved by induction on `fuel`
(placed). -/
theorem decodeState_chain_loop_53698_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 : M.σ)
    (optVn : Option VersionNegotiationPB) (inner : Option PqRatchetState.Inner)
    (limit : Nat) (hlim_bound : limit < 2 ^ 32) (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hpost_env : ∀ evs, DecodeStateEnv x evs → PostEnv x evs)
    (hs0A : s0.spAligned = true) :
    ∀ (fuel : Nat) (w0 : BitVec 64) (ch : ChainPB) (cur : List (BitVec 8))
      (st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat) (s : State) (P : SepProp),
      cur.length - limit ≤ fuel → cur.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes cur →
      ch.links.length + cur.length ≤ 2 * x.st.bytes.length + 4 →
      (mergeLoopBin ChainPB.mergeField (cur.length - limit) ch cur limit 99 = none →
        spqrDecodeState x.st.bytes = .error .stateDecode) →
      DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc →
      M.stepEvents evs_acc st0 = st →
      FitsEnv M lim st
        (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)) →
      4 * cur.length + 8 ≤ rem →
      f + 4 * cur.length + 8 ≤ 16 * x.st.bytes.length + 32 →
      s.pc = decodeStatePlacedEntry + 508#64 →
      s.status = .Running → s.sp = s0.sp - 1392#64 → TraceVRegs s s0 →
      s.readReg64 .x19 = x.outPtr → s.readReg64 .x20 = BitVec.ofNat 64 limit →
      s.readReg64 .x21 = 0x8000000000000006#64 → s.readReg64 .x22 = s0.sp - 1040#64 →
      s.readReg64 .x23 = -1#64 → s.readReg64 .x24 = s0.sp - 912#64 →
      s.readReg64 .x25 = s0.sp - 688#64 → s.readReg64 .x26 = -2#64 →
      s.readReg64 .x27 = 8#64 → s.readReg64 .x28 = 1#64 → s.readReg64 .x29 = s0.sp - 96#64 →
      P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length
          ⟨optVn, some ch, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 s →
      (∀ (w0' : BitVec 64) (ch' : ChainPB) (rest : List (BitVec 8))
          (evs_loop : List AllocEvent) (sf : State) (P' : SepProp),
        mergeLoopBin ChainPB.mergeField (cur.length - limit) ch cur limit 99 = some ch' →
        ch'.links.length + rest.length ≤ ch.links.length + cur.length →
        DecodeStateLoopEnv (f + 4 * (cur.length - rest.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16) (evs_acc ++ evs_loop) →
        M.stepEvents (evs_acc ++ evs_loop) st0 = M.stepEvents evs_loop st →
        FitsEnv M lim (M.stepEvents evs_loop st)
          (DecodeStateLoopEnv (rem - 4 * (cur.length - rest.length)) x.st.bytes.length
            (2 * x.st.bytes.length + 16)) →
        rest.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes rest → rest.length = limit →
        sf.pc = decodeStatePlacedEntry + 1576#64 →
        sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
        sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 rest.length →
        sf.readReg64 .x21 = 0x8000000000000006#64 →
        sf.readReg64 .x22 = s0.sp - 1040#64 → sf.readReg64 .x23 = -1#64 →
        sf.readReg64 .x24 = s0.sp - 912#64 → sf.readReg64 .x25 = s0.sp - 688#64 →
        sf.readReg64 .x26 = -2#64 → sf.readReg64 .x27 = 8#64 →
        sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
        P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
          sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest ∗
          protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest.length
            ⟨optVn, some ch', inner⟩ ∗
          memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
          decodeStateLoopCommonPlaced A lim (M.stepEvents evs_loop st) x s0 sf →
        SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
          (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  intro fuel
  induction fuel with
  | zero =>
    intro w0 ch cur st evs_acc f rem s P hfuel hcur_le hcur_suf hlinks herr_of_none
      hacc hst hFit hrem hf
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
      exact hdone w0 ch cur [] _ _
        (mergeLoopBin_eq_limit ChainPB.mergeField (cur.length - limit) ch cur limit 99 heq)
        (Nat.le_refl _)
        (by simpa [List.append_nil] using hacc.mono_fuel (by omega))
        (by simp only [List.append_nil, M.stepEvents_nil, hst])
        (by
          simp only [M.stepEvents_nil]
          exact SpecsBudget.FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _)
            hFit)
        hcur_le hcur_suf heq
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
    · have hfits8 : FitsEnv M lim st
          (DecodeStateLoopEnv (4 * cur.length + 8) x.st.bytes.length
            (2 * x.st.bytes.length + 16)) :=
        SpecsBudget.FitsEnv.decodeStateLoop_mono hrem (Nat.le_refl _) (Nat.le_refl _) hFit
      have henv_err8 := acc_henv_err (k := 4 * cur.length + 8) hacc hst (by omega) hpost_env
      have ⟨hult, hule, hbeq⟩ := cmp_len_limit_of_lt hlt (by omega)
      have hbne := cmp_len_limit_bne_of_lt hlt (by omega)
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1596#64)
      wp_steps 4
      refine SepWP.fold (loopCommon_cursor_to_errFrame_placed H_inner A lim st x cur cur.length
        ⟨optVn, some ch, inner⟩ s0 s)
        (by dsimp only [sliceCursorAfter]; sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, hult, hule, hbeq, hbne])
        (by simp only [arm64_norm, hrun])
      exact SepWPpIPlaced.of_sepWPp (decodeState_err_53ad8_placed_ofEnv
        hc.toDecodeStateCalleeContractsPlaced x st0 st ⟨optVn, some ch, inner⟩ w0 s0 _ _ R post
        hpost
        (herr_of_none (mergeLoopBin_lt_limit ChainPB.mergeField (cur.length - limit) ch cur limit 99
          hlt))
        (err3_fits1 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits8)
        (err3_fits2 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits8)
        (err3_env (by omega) (fun _ => decodeErrorFromEnv_iter) henv_err8)
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hbeq, hbne])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx21])
        (by
          unfold decodeStateErrFramePlaced
          dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26,
            Reg.x27, Reg.x28, Reg.x29, Reg.x30]
          simp only [wp_norm, arm64_norm]
          try sep_ac_rfl))
  | succ fuel ih =>
    intro w0 ch cur st evs_acc f rem s P hfuel hcur_le hcur_suf hlinks herr_of_none
      hacc hst hFit hrem hf
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
        exact hdone w0 ch cur [] _ _
          (mergeLoopBin_eq_limit ChainPB.mergeField (cur.length - limit) ch cur limit 99 heq)
          (Nat.le_refl _)
          (by simpa [List.append_nil] using hacc.mono_fuel (by omega))
          (by simp only [List.append_nil, M.stepEvents_nil, hst])
          (by
            simp only [M.stepEvents_nil]
            exact SpecsBudget.FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _)
              hFit)
          hcur_le hcur_suf heq
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
      · have hfits8 : FitsEnv M lim st
            (DecodeStateLoopEnv (4 * cur.length + 8) x.st.bytes.length
              (2 * x.st.bytes.length + 16)) :=
          SpecsBudget.FitsEnv.decodeStateLoop_mono hrem (Nat.le_refl _) (Nat.le_refl _) hFit
        have henv_err8 := acc_henv_err (k := 4 * cur.length + 8) hacc hst (by omega) hpost_env
        have ⟨hult, hule, hbeq⟩ := cmp_len_limit_of_lt hlt (by omega)
        have hbne := cmp_len_limit_bne_of_lt hlt (by omega)
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1596#64)
        wp_steps 4
        refine SepWP.fold (loopCommon_cursor_to_errFrame_placed H_inner A lim st x cur cur.length
          ⟨optVn, some ch, inner⟩ s0 s)
          (by dsimp only [sliceCursorAfter]; sep_focus) ?_
        apply SepWP.done (by simp only [arm64_norm, hult, hule, hbeq, hbne])
          (by simp only [arm64_norm, hrun])
        exact SepWPpIPlaced.of_sepWPp (decodeState_err_53ad8_placed_ofEnv
          hc.toDecodeStateCalleeContractsPlaced x st0 st ⟨optVn, some ch, inner⟩ w0 s0 _ _ R post
          hpost
          (herr_of_none (mergeLoopBin_lt_limit ChainPB.mergeField (cur.length - limit) ch cur
            limit 99 hlt))
          (err3_fits1 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits8)
          (err3_fits2 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits8)
          (err3_env (by omega) (fun _ => decodeErrorFromEnv_iter) henv_err8)
          (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hult, hule, hbeq, hbne])
          (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
          (by simp only [arm64_norm, htr])
          (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx21])
          (by
            unfold decodeStateErrFramePlaced
            dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26,
              Reg.x27, Reg.x28, Reg.x29, Reg.x30]
            simp only [wp_norm, arm64_norm]
            try sep_ac_rfl))
    · have ⟨hult, hule⟩ := cmp_len_limit_of_gt hle (by omega)
      subst hP
      dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, sliceCursorAfter] at hpc ⊢
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 520#64)
      wp_steps 3
      apply SepWP.done (by simp only [arm64_norm, hult, hule]) (by simp only [arm64_norm, hrun])
      refine decodeState_chain_body_536a4_placed_ofEnv
        (PreEnv := PreEnv) (PostEnv := PostEnv)
        hc x st0 st evs_acc f rem w0 optVn ch inner cur limit
        hle hcur_le hcur_suf hlen_bound hlinks herr_of_none
        hacc hst hFit hrem hf s0 _ _ R post hpost hpost_env hs0A
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
      intro w0' ch' rest2 evs_step sf P' hlt2 hle2 hsuf2 hlinks2 hacc2 hst2 hFit2 hmerge_eq
        hpc' hrun' hsp' htr' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28' hx29' hP'
      refine ih w0' ch' rest2 (M.stepEvents evs_step st) (evs_acc ++ evs_step)
        (f + 4 * (cur.length - rest2.length)) (rem - 4 * (cur.length - rest2.length)) sf P'
        (by omega) hle2 hsuf2 (by omega)
        (fun hnone => herr_of_none (by rw [hmerge_eq, hnone]))
        hacc2 hst2 hFit2 (by omega) (by omega)
        hpc' hrun' hsp' htr' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28' hx29' hP'
        ?_
      intro w0'' ch'' rest3 evs_rest sf' P'' hok hlinks3 hacc3 hst3 hFit3
        hrest3_le hrest3_suf hrest3_eq
        hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hx27''
        hx28'' hx29'' hP''
      have hrest3_le_rest2 : rest3.length ≤ rest2.length := by
        rw [hrest3_eq]
        apply Nat.not_lt.mp
        intro hlt_lim
        have hnone := mergeLoopBin_lt_limit ChainPB.mergeField (rest2.length - limit)
          ch' rest2 limit 99 hlt_lim
        rw [hok] at hnone
        cases hnone
      rw [List.append_assoc] at hacc3
      exact hdone w0'' ch'' rest3 (evs_step ++ evs_rest) sf' P''
        (by rw [hmerge_eq, hok])
        (by omega)
        (hacc3.mono_fuel (by omega))
        (by rw [M.stepEvents_append, hst])
        (by
          rw [M.stepEvents_append]
          exact SpecsBudget.FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _)
            hFit3)
        hrest3_le hrest3_suf hrest3_eq
        hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hx27''
        hx28'' hx29'' (by rw [M.stepEvents_append]; exact hP'')

theorem decodeState_chain_loop_53698_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 : M.σ)
    (optVn : Option VersionNegotiationPB) (inner : Option PqRatchetState.Inner)
    (limit : Nat) (hlim_bound : limit < 2 ^ 32) (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true) :
    ∀ (fuel : Nat) (w0 : BitVec 64) (ch : ChainPB) (cur : List (BitVec 8))
      (st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat) (s : State) (P : SepProp),
      cur.length - limit ≤ fuel → cur.length ≤ x.st.bytes.length →
      IsDropSuffix x.st.bytes cur →
      ch.links.length + cur.length ≤ 2 * x.st.bytes.length + 4 →
      (mergeLoopBin ChainPB.mergeField (cur.length - limit) ch cur limit 99 = none →
        spqrDecodeState x.st.bytes = .error .stateDecode) →
      DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc →
      M.stepEvents evs_acc st0 = st →
      FitsEnv M lim st
        (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)) →
      4 * cur.length + 8 ≤ rem →
      f + 4 * cur.length + 8 ≤ 16 * x.st.bytes.length + 32 →
      s.pc = decodeStatePlacedEntry + 508#64 →
      s.status = .Running → s.sp = s0.sp - 1392#64 → TraceVRegs s s0 →
      s.readReg64 .x19 = x.outPtr → s.readReg64 .x20 = BitVec.ofNat 64 limit →
      s.readReg64 .x21 = 0x8000000000000006#64 → s.readReg64 .x22 = s0.sp - 1040#64 →
      s.readReg64 .x23 = -1#64 → s.readReg64 .x24 = s0.sp - 912#64 →
      s.readReg64 .x25 = s0.sp - 688#64 → s.readReg64 .x26 = -2#64 →
      s.readReg64 .x27 = 8#64 → s.readReg64 .x28 = 1#64 → s.readReg64 .x29 = s0.sp - 96#64 →
      P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) cur.length
          ⟨optVn, some ch, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim st x s0 s →
      (∀ (w0' : BitVec 64) (ch' : ChainPB) (rest : List (BitVec 8))
          (evs_loop : List AllocEvent) (sf : State) (P' : SepProp),
        mergeLoopBin ChainPB.mergeField (cur.length - limit) ch cur limit 99 = some ch' →
        ch'.links.length + rest.length ≤ ch.links.length + cur.length →
        DecodeStateLoopEnv (f + 4 * (cur.length - rest.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16) (evs_acc ++ evs_loop) →
        M.stepEvents (evs_acc ++ evs_loop) st0 = M.stepEvents evs_loop st →
        FitsEnv M lim (M.stepEvents evs_loop st)
          (DecodeStateLoopEnv (rem - 4 * (cur.length - rest.length)) x.st.bytes.length
            (2 * x.st.bytes.length + 16)) →
        rest.length ≤ x.st.bytes.length → IsDropSuffix x.st.bytes rest → rest.length = limit →
        sf.pc = decodeStatePlacedEntry + 1576#64 →
        sf.status = .Running → sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 →
        sf.readReg64 .x19 = x.outPtr → sf.readReg64 .x20 = BitVec.ofNat 64 rest.length →
        sf.readReg64 .x21 = 0x8000000000000006#64 →
        sf.readReg64 .x22 = s0.sp - 1040#64 → sf.readReg64 .x23 = -1#64 →
        sf.readReg64 .x24 = s0.sp - 912#64 → sf.readReg64 .x25 = s0.sp - 688#64 →
        sf.readReg64 .x26 = -2#64 → sf.readReg64 .x27 = 8#64 →
        sf.readReg64 .x28 = 1#64 → sf.readReg64 .x29 = s0.sp - 96#64 →
        P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
          sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest ∗
          protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest.length
            ⟨optVn, some ch', inner⟩ ∗
          memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
          decodeStateLoopCommonPlaced A lim (M.stepEvents evs_loop st) x s0 sf →
        SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
          (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_chain_loop_53698_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 optVn inner limit hlim_bound hlen_bound s0 R post hpost (fun _ h => h) hs0A

/-! ## Outer Loop Tag-2 (`PqRatchetState::chain`, `+284` & `+244`) -/

private theorem optChainPB_none_split72 (a : BitVec 64) :
    memRegion (a + 8#64) 72 ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 32, ∃∗ w9 : BitVec 32,
        ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗
        ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₃₂ w8) ∗
        memRegion (a + 68#64) 8 ∗ ((a + 76#64) ↦₃₂ w9) := by
  rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 56) (k := 16)
      (b' := a + 64#64) rfl (by bv_omega) (by decide),
    memRegion_56_eq_quads7At (a + 8#64),
    ProofLib.memRegion_split' (b := a + 64#64) (n := 4) (k := 12)
      (b' := a + 68#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := a + 68#64) (n := 8) (k := 4)
      (b' := a + 76#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_four (a + 64#64),
    ProofLib.memRegion_four (a + 76#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w9
  apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; rintro ⟨w1, w2, w3, w4, w5, w6, w7⟩
  dsimp only [quads7At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4
      (Entails.sepExists_right w5 (Entails.sepExists_right w6
        (Entails.sepExists_right w7 (Entails.sepExists_right w8
          (Entails.sepExists_right w9 ?_))))))))
  exact Entails.of_eq (by sep_ac_rfl)

private theorem chainLinksVecAt_cap_lt (A : RustAlloc) (cap ptr : BitVec 64)
    (xs : List ChainEpochPB) :
    vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗
      vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs := by
  unfold vecBuf
  apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
  exact Entails.pure_right (by omega) (Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _))

private theorem chainLinksVecAt_header_fold (A : RustAlloc) (a cap ptr : BitVec 64)
    (xs : List ChainEpochPB) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
      vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs ⊢
    chainLinksVecAt A a xs := by
  unfold chainLinksVecAt chainEpochPBSize vecOf vecAt vecHeader
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by sep_ac_rfl)

attribute [local irreducible]
  mergeMessage mergeLoopBin CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState

/-- Envelope-parameterized delimited `ChainPB::merge` entry at `+284` (placed). -/
theorem decodeState_chain_merge_535b8_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hlinks : ch.links.length + rest1.length ≤ 2 * x.st.bytes.length + 4)
    (herr_of_none :
      (mergeMessage ChainPB.mergeField (codecWireTypeToProto iwt) ch rest1 100).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 * rest1.length + 8 ≤ rem)
    (hf : f + 4 * rest1.length + 8 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hpost_env : ∀ evs, DecodeStateEnv x evs → PostEnv x evs)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 284#64)
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
    (hx27 : s.readReg64 .x27 = 8#64)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨optVn, some ch, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (w0' : BitVec 64) (ch' : ChainPB) (rest2 : List (BitVec 8))
        (evs_ch : List AllocEvent) (sf : State) (P' : SepProp),
      (mergeMessage ChainPB.mergeField (codecWireTypeToProto iwt) ch rest1 100).toOption =
        some (ch', rest2) →
      ch'.links.length + rest2.length ≤ ch.links.length + rest1.length →
      DecodeStateLoopEnv (f + 4 * (rest1.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_ch) →
      M.stepEvents (evs_acc ++ evs_ch) st0 = M.stepEvents evs_ch st →
      FitsEnv M lim (M.stepEvents evs_ch st)
        (DecodeStateLoopEnv (rem - 4 * (rest1.length - rest2.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
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
      sf.readReg64 .x27 = 8#64 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, some ch', inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_ch st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hfits8 : FitsEnv M lim st
      (DecodeStateLoopEnv (4 * rest1.length + 8) x.st.bytes.length
        (2 * x.st.bytes.length + 16)) :=
    SpecsBudget.FitsEnv.decodeStateLoop_mono hrem (Nat.le_refl _) (Nat.le_refl _) hFit
  have henv_err8 := acc_henv_err (k := 4 * rest1.length + 8) hacc hst (by omega) hpost_env
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
    refine SepWPpIPlaced.call_decodeVarint2 hdv_call
      (s0.sp - 336#64) (s0.sp - 1056#64)
      (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1 st
      (ret_pc := (blkPl_325).base + 300#64)
      (hpc := by simp only [wp_norm, arm64_norm]) (hrun := by simp only [wp_norm, arm64_norm, hrun])
      (hsp := by simp only [wp_norm, arm64_norm, hsp]) (hs0A := hs0A)
      (hlr := by simp only [wp_norm, arm64_norm]) (htr := by simp only [wp_norm, arm64_norm, htr])
      (hx0 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
      (hlen := by omega)
      (hfits := err3_fits1 (by omega) (fun _ => .of_decodeVarint2) hfits8)
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
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2092#64)
        refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
          hrest1_le hrest1_suf hle2) (by sep_focus) ?_
        dsimp only [sliceCursorAfter]
        wp_steps 4
        refine SepWP.fold (loopCommon_cursor_to_errFrame_placed H_inner A lim st x rest2
          rest1.length ⟨optVn, some ch, inner⟩ s0 s1)
          (by dsimp only [sliceCursorAfter, decodeStateLoopCommonPlaced]; sep_focus) ?_
        apply SepWP.done (by simp only [arm64_norm, hx0_0, hult, hule])
          (by simp only [arm64_norm, hrun1])
        exact SepWPpIPlaced.of_sepWPp (decodeState_err_53cc8_placed_ofEnv
          hc.toDecodeStateCalleeContractsPlaced x st0 st ⟨optVn, some ch, inner⟩ w0 s0 _ _ R post
          hpost
          (herr_of_none (mergeMessage_toOption_of_lt ChainPB.mergeField hdv hlt_len))
          (err3_fits1 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits8)
          (err3_fits2 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits8)
          (err3_env (by omega) (fun _ => decodeErrorFromEnv_iter) henv_err8)
          (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0, hult, hule])
          (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
          (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
          (by
            unfold decodeStateErrFramePlaced
            dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26,
              Reg.x27, Reg.x28, Reg.x29, Reg.x30]
            simp only [wp_norm, arm64_norm]
            try sep_ac_rfl))
      · have ⟨hult, hule⟩ := len_ult_of_ge hlt_len (by omega)
        have hsub_lim := bv_len_sub_limit hlt_len
        have hmm_eq := mergeMessage_toOption_of_ge protoPrefixStep_chainPB_mergeField
          (m := ch) (depth' := 99) hdv hlt_len
        apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 508#64)
        refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
          hrest1_le hrest1_suf hle2) (by sep_focus) ?_
        dsimp only [sliceCursorAfter]
        wp_steps 4
        refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
          (a := s0.sp - 1040#64) (rem1 := rest1.length) (rem2 := rest2.length)
          (st := ⟨optVn, some ch, inner⟩) hle2) (by sep_focus) ?_
        apply SepWP.done (by simp only [arm64_norm, hx0_0, hult, hule])
          (by simp only [arm64_norm, hrun1])
        refine decodeState_chain_loop_53698_placed_ofEnv
          (PreEnv := PreEnv) (PostEnv := PostEnv)
          hc x st0 optVn inner (rest2.length - len64.toNat)
          (by omega) hlen_bound s0 R post hpost hpost_env hs0A
          (rest2.length - (rest2.length - len64.toNat)) w0 ch rest2 st evs_acc f rem _ _
          (Nat.le_refl _) hrest2_le hrest2_suf (by omega)
          (fun hnone => herr_of_none (by rw [hmm_eq, hnone]; rfl))
          hacc hst hFit (by omega) (by omega)
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
        intro w0' ch' rest3 evs_loop sf P' hloop_ok hlinks3 hacc3 hst3 hFit3
          hrest3_le hrest3_suf hrest3_eq
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
            (mergeMessage ChainPB.mergeField
              .lengthDelimited ch rest1 100).toOption = some (ch', rest3) := by
          rw [hmm_eq, hloop_ok, ← hdrop]; rfl
        exact hdone w0' ch' rest3 evs_loop sf P' hok_mm
          (by omega)
          (hacc3.mono_fuel (by omega))
          hst3
          (SpecsBudget.FitsEnv.decodeStateLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _)
            hFit3)
          hle3_1 hsuf3_1
    · intro s1 evs_dv hdv hevs_dv hpc1 hrun1 hsp1 htr1 hcs1 hx0_1 hx1_ne
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
        hx28_1, hx29_1, hvregs_1⟩
      simp only [arm64_norm, wp_norm] at hx0_1 hx1_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
      simp only [arm64_norm, wp_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2112#64)
      wp_steps 2
      wp_if hcbz
      · exact absurd hcbz hx1_ne
      · wp_steps 1
        refine SepWP.fold (errFrame_parts_fold A.repAlloc x s0 hrest1_le hrest1_suf)
          (by sep_focus) ?_
        refine SepWP.fold (protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner
          A.repAlloc (s0.sp - 1040#64) rest1.length ⟨optVn, some ch, inner⟩) (by sep_focus) ?_
        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
        exact SepWPpIPlaced.of_sepWPp (decodeState_err_push_53cdc_placed_ofEnv
          hc.toDecodeStateCalleeContractsPlaced x st0 (M.stepEvents evs_dv st)
          ⟨optVn, some ch, inner⟩ w0 0 s0 _ _ R post hpost
          (herr_of_none (mergeMessage_toOption_of_decodeVarint_none ChainPB.mergeField hdv))
          (by decide)
          (err3_fits2 (by omega) (fun _ => .of_decodeVarint2) hfits8 evs_dv hevs_dv)
          (fun evs_p evs_f hp hfree =>
            err3_env (by omega) (fun _ => .of_decodeVarint2) henv_err8 evs_dv evs_p evs_f
              hevs_dv hp hfree)
          (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
          (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
          (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
          (by
            dsimp only [Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
              Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
            simp only [wp_norm, arm64_norm]
            try sep_ac_rfl))
  · have ⟨hbne, hbeq⟩ := wt64_ne_two_of_ne_lengthDelimited hwt
    subst hP
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, Reg.x0] at hpc hx0 ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1808#64)
    wp_steps 2
    refine SepWP.fold (loopCommon_cursor_to_errFrame_placed H_inner A lim st x rest1 rest1.length
      ⟨optVn, some ch, inner⟩ s0 s) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, Reg.x0, hx0, hbne, hbeq])
      (by simp only [arm64_norm, hrun])
    exact SepWPpIPlaced.of_sepWPp (decodeState_err_53bac_placed_ofEnv
      hc.toDecodeStateCalleeContractsPlaced x st0 st ⟨optVn, some ch, inner⟩ w0 s0 _ _ R post hpost
      (herr_of_none (by
        rw [← decodeState_codecWireTypeToProto_eq]
        exact mergeMessage_toOption_of_ne_lengthDelimited ChainPB.mergeField hwt))
      (err3_fits1 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits8)
      (err3_fits2 (by omega) (fun _ => decodeErrorFromEnv_iter) hfits8)
      (err3_env (by omega) (fun _ => decodeErrorFromEnv_iter) henv_err8)
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, Reg.x0, hx0, hbne, hbeq])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx21])
      (by
        unfold decodeStateErrFramePlaced
        dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26,
          Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        simp only [wp_norm, arm64_norm]
        try sep_ac_rfl))

theorem decodeState_chain_merge_535b8_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hlinks : ch.links.length + rest1.length ≤ 2 * x.st.bytes.length + 4)
    (herr_of_none :
      (mergeMessage ChainPB.mergeField (codecWireTypeToProto iwt) ch rest1 100).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 * rest1.length + 8 ≤ rem)
    (hf : f + 4 * rest1.length + 8 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 284#64)
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
    (hx27 : s.readReg64 .x27 = 8#64)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨optVn, some ch, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (w0' : BitVec 64) (ch' : ChainPB) (rest2 : List (BitVec 8))
        (evs_ch : List AllocEvent) (sf : State) (P' : SepProp),
      (mergeMessage ChainPB.mergeField (codecWireTypeToProto iwt) ch rest1 100).toOption =
        some (ch', rest2) →
      ch'.links.length + rest2.length ≤ ch.links.length + rest1.length →
      DecodeStateLoopEnv (f + 4 * (rest1.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_ch) →
      M.stepEvents (evs_acc ++ evs_ch) st0 = M.stepEvents evs_ch st →
      FitsEnv M lim (M.stepEvents evs_ch st)
        (DecodeStateLoopEnv (rem - 4 * (rest1.length - rest2.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
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
      sf.readReg64 .x27 = 8#64 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, some ch', inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_ch st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_chain_merge_535b8_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st evs_acc f rem w0 optVn ch inner rest1 iwt hrest1_le hrest1_suf hlen_bound hlinks
    herr_of_none hacc hst hFit hrem hf s0 s P R post hpost (fun _ h => h) hs0A
    hpc hrun hsp htr hx0 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hdone

/-- Envelope-parameterized outer loop tag-2 (`PqRatchetState::chain`, `+244`) reaching
`entry + 1576` (placed). -/
theorem decodeState_chain_entry_53590_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (optCh : Option ChainPB)
    (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hlinks : (optCh.getD default).links.length + rest1.length ≤ 2 * x.st.bytes.length + 4)
    (herr_of_none :
      (mergeMessage ChainPB.mergeField (codecWireTypeToProto iwt)
        (optCh.getD default) rest1 100).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 * rest1.length + 8 ≤ rem)
    (hf : f + 4 * rest1.length + 8 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hpost_env : ∀ evs, DecodeStateEnv x evs → PostEnv x evs)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 244#64)
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
    (hx27 : s.readReg64 .x27 = 8#64)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨optVn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (w0' : BitVec 64) (ch' : ChainPB) (rest2 : List (BitVec 8))
        (evs_ch : List AllocEvent) (sf : State) (P' : SepProp),
      (mergeMessage ChainPB.mergeField (codecWireTypeToProto iwt)
        (optCh.getD default) rest1 100).toOption = some (ch', rest2) →
      ch'.links.length + rest2.length ≤ (optCh.getD default).links.length + rest1.length →
      DecodeStateLoopEnv (f + 4 * (rest1.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_ch) →
      M.stepEvents (evs_acc ++ evs_ch) st0 = M.stepEvents evs_ch st →
      FitsEnv M lim (M.stepEvents evs_ch st)
        (DecodeStateLoopEnv (rem - 4 * (rest1.length - rest2.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
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
      sf.readReg64 .x27 = 8#64 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, some ch', inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_ch st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  cases optCh with
  | none =>
    subst hP
    unfold protoPqRatchetStateCapOkAt optChainPBCapOkAt
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced,
      Option.getD] at hpc herr_of_none hlinks hdone ⊢
    have ha992 : s0.sp - 1040#64 + 48#64 = s0.sp - 992#64 := by bv_omega
    have ha912 : s0.sp - 1040#64 + 128#64 = s0.sp - 912#64 := by bv_omega
    rw [ha992, ha912]
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 244#64)
    refine SepWP.fold (optChainPB_none_split72 (s0.sp - 992#64)) (by sep_focus) ?_
    apply SepWP.done (by exact hpc) (by exact hrun)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPpIPlaced.exists_elim; intro w1
    apply SepWPpIPlaced.exists_elim; intro w2
    apply SepWPpIPlaced.exists_elim; intro w3
    apply SepWPpIPlaced.exists_elim; intro w4
    apply SepWPpIPlaced.exists_elim; intro w5
    apply SepWPpIPlaced.exists_elim; intro w6
    apply SepWPpIPlaced.exists_elim; intro w7
    apply SepWPpIPlaced.exists_elim; intro w8
    apply SepWPpIPlaced.exists_elim; intro w9
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 284#64)
    wp_steps_sync_pool ((blkPl_325).base + 284#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold (chainPBCapOkAt_default_init A.repAlloc (s0.sp - 992#64) rest1.length
      (by omega)) (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    exact decodeState_chain_merge_535b8_placed_ofEnv
      (PreEnv := PreEnv) (PostEnv := PostEnv)
      hc x st0 st evs_acc f rem w0 optVn default inner rest1 iwt
      hrest1_le hrest1_suf hlen_bound hlinks herr_of_none
      hacc hst hFit hrem hf s0 _ _ R post hpost hpost_env hs0A
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
        unfold protoPqRatchetStateCapOkAt optChainPBCapOkAt
        dsimp only [decodeStateLoopCommonPlaced]
        rw [ha992, ha912]
        try sep_ac_rfl)
      hdone
  | some ch =>
    subst hP
    rw [protoPqRatchetStateCapOkAt_some_ch_eq_placed]
    unfold chainLinksVecAt chainEpochPBSize vecOf vecAt
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, Option.getD]
      at hpc herr_of_none hlinks hdone ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 284#64)
    wp_pull_exists
    rename_i cap ptr
    refine SepWP.fold (chainLinksVecAt_cap_lt A.repAlloc cap ptr ch.links) (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    unfold vecHeader
    have hcmn : (cap + 1#64 != 0#64) = true := by
      rw [bne_iff_ne, ← beq_eq_false_iff_ne, Bool.eq_false_iff]
      exact cap_add_one_beq_zero_false hcap_lt
    wp_steps 3
    refine SepWP.fold (chainLinksVecAt_header_fold A.repAlloc (s0.sp - 992#64) cap ptr ch.links)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hcmn]) (by simp only [arm64_norm, hrun])
    exact decodeState_chain_merge_535b8_placed_ofEnv
      (PreEnv := PreEnv) (PostEnv := PostEnv)
      hc x st0 st evs_acc f rem w0 optVn ch inner rest1 iwt
      hrest1_le hrest1_suf hlen_bound hlinks herr_of_none
      hacc hst hFit hrem hf s0 _ _ R post hpost hpost_env hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hcmn])
      (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx0])
      (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm, hx21])
      (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23])
      (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25])
      (by simp only [arm64_norm, hx26])
      (by simp only [arm64_norm, hx27])
      (by simp only [arm64_norm, hx28])
      (by simp only [arm64_norm, hx29])
      (by
        rw [protoPqRatchetStateCapOkAt_some_ch_eq_placed]
        dsimp only [decodeStateLoopCommonPlaced]
        simp only [wp_norm, arm64_norm]
        try sep_ac_rfl)
      hdone

theorem decodeState_chain_entry_53590_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (evs_acc : List AllocEvent) (f rem : Nat)
    (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (optCh : Option ChainPB)
    (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (hlinks : (optCh.getD default).links.length + rest1.length ≤ 2 * x.st.bytes.length + 4)
    (herr_of_none :
      (mergeMessage ChainPB.mergeField (codecWireTypeToProto iwt)
        (optCh.getD default) rest1 100).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (hacc : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st)
    (hFit : FitsEnv M lim st
      (DecodeStateLoopEnv rem x.st.bytes.length (2 * x.st.bytes.length + 16)))
    (hrem : 4 * rest1.length + 8 ≤ rem)
    (hf : f + 4 * rest1.length + 8 ≤ 16 * x.st.bytes.length + 32)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 244#64)
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
    (hx27 : s.readReg64 .x27 = 8#64)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨optVn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hdone : ∀ (w0' : BitVec 64) (ch' : ChainPB) (rest2 : List (BitVec 8))
        (evs_ch : List AllocEvent) (sf : State) (P' : SepProp),
      (mergeMessage ChainPB.mergeField (codecWireTypeToProto iwt)
        (optCh.getD default) rest1 100).toOption = some (ch', rest2) →
      ch'.links.length + rest2.length ≤ (optCh.getD default).links.length + rest1.length →
      DecodeStateLoopEnv (f + 4 * (rest1.length - rest2.length)) x.st.bytes.length
        (2 * x.st.bytes.length + 16) (evs_acc ++ evs_ch) →
      M.stepEvents (evs_acc ++ evs_ch) st0 = M.stepEvents evs_ch st →
      FitsEnv M lim (M.stepEvents evs_ch st)
        (DecodeStateLoopEnv (rem - 4 * (rest1.length - rest2.length)) x.st.bytes.length
          (2 * x.st.bytes.length + 16)) →
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
      sf.readReg64 .x27 = 8#64 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨optVn, some ch', inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_ch st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_chain_entry_53590_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st evs_acc f rem w0 optVn optCh inner rest1 iwt hrest1_le hrest1_suf hlen_bound hlinks
    herr_of_none hacc hst hFit hrem hf s0 s P R post hpost (fun _ h => h) hs0A
    hpc hrun hsp htr hx0 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hdone

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoopPlacedBudget
