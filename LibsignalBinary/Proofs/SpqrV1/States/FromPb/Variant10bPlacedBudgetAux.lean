/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10bPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Variant 10 (`Ct2Sampled`, `+1632`) — Early Error Paths

Proves `[LibsignalPlacement]` `FreeOnlyEvs` early error exits at `+1632` (Block `333`) when
`s.uc = none` and when `s.uc = some { auth := none, .. }` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10bPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_333 lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (PolynomialEncoderPB pbToProtoPolyEncoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesSize none2Cap none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
   optProtoInnerStateSize protoChunkedCt2SampledAt)
open CryptoVerification.SpqrV1.Poly (optProtoPolynomialEncoderAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved resultChunkedStatesAt statesFromPbJumpTablePlacedAt
   statesFromPbSavedCells statesFromPbStack v10_fsp_unsplit_0 v10_optEncoderCapProp
   v10_optProtoPolyEncoderTail v10_optProtoPolyEncoder_expose_cap
   v10_optProtoPolyEncoder_unexpose_cap v10_pb_64_auth_none_entails_160
   v10_pb_64_none_entails_160 v10_pb_tag_56_160_entails_224
   v10_protoChunkedCt2SampledAt_auth_none v10_protoChunkedCt2SampledAt_uc_none
   v1_bv_add_add_lit v1_bv_sub_sub_lit v1_shl8_extract_0_8)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10aPlacedBudget
  (v10_states_from_pb_err_2064_of_sub_placed
   v10_sub_ok_drop_proto_poly_encoder_of_dealloc_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (FromPbAllocHooksBudget seq_clean_lscl_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (blk333_noSvc0 entails_pre_st)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_sub_sub_lit v1_shl8_extract_0_8 v1_bv_add_add_lit

local macro "wp_steps_sync_333 " mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_333).rebase (blkPl_333).base (hooksException _))
    blkLib_eq_333 blk333_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## 1. `Ct2Sampled` (`+1632`) Early Error Paths (`s.uc = none` and `auth = none`) -/

/-- Expose `cap_enc` and `none2Cap` on `memRegion fsp 2304` when `s.uc = none`. -/
theorem v10_ct2Sent_expose_pre_uc_none_2304_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (fsp out pbA : BitVec 64) (s0 s1 : State) (sendingCt2 : Option PolynomialEncoderPB) :
    stackAt fsp encoderFromPbStack ∗
      memRegion fsp 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗
       protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64) { sendingCt2 := sendingCt2, uc := none } ∗
       memRegion (pbA + 120#64) 104) ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st s1 ⊢
    ∃∗ cap_enc : BitVec 64,
      ⌜v10_optEncoderCapProp cap_enc (sendingCt2.map pbToProtoPolyEncoder)⌝ ∗
      (stackAt fsp encoderFromPbStack ∗
       memRegion fsp 2304 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x800000000000000a#64) ∗
       ((pbA + 8#64) ↦₆₄ cap_enc) ∗
       v10_optProtoPolyEncoderTail A.repAlloc (pbA + 8#64) cap_enc
         (sendingCt2.map pbToProtoPolyEncoder) ∗
       ((pbA + 64#64) ↦₆₄ none2Cap) ∗
       memRegion (pbA + 72#64) 48 ∗
       memRegion (pbA + 120#64) 104 ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool lim st s1) := by
  rw [v10_protoChunkedCt2SampledAt_uc_none]
  refine Entails.trans
    (Entails.of_eq (show _ =
      optProtoPolynomialEncoderAt A.repAlloc (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder) ∗
      (stackAt fsp encoderFromPbStack ∗
       memRegion fsp 2304 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x800000000000000a#64) ∗
       ((pbA + 64#64) ↦₆₄ none2Cap) ∗
       memRegion (pbA + 72#64) 48 ∗
       memRegion (pbA + 120#64) 104 ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool lim st s1) by sep_ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono_left
      (v10_optProtoPolyEncoder_expose_cap A.repAlloc (pbA + 8#64)
        (sendingCt2.map pbToProtoPolyEncoder))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.sepExists_elim fun cap_enc =>
    Entails.sepExists_right cap_enc (Entails.of_eq (by sep_ac_rfl))

/-- Expose `cap_enc` and `none2Cap` on `(fsp ↦₆₄ 0#64) ∗ memRegion (fsp + 8#64) 2296`
    when `s.uc = none`. -/
theorem v10_ct2Sent_expose_pre_uc_none_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (fsp out pbA : BitVec 64) (s0 s1 : State) (sendingCt2 : Option PolynomialEncoderPB) :
    stackAt fsp encoderFromPbStack ∗
      (fsp ↦₆₄ 0#64) ∗
      memRegion (fsp + 8#64) 2296 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗
       protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64) { sendingCt2 := sendingCt2, uc := none } ∗
       memRegion (pbA + 120#64) 104) ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st s1 ⊢
    ∃∗ cap_enc : BitVec 64,
      ⌜v10_optEncoderCapProp cap_enc (sendingCt2.map pbToProtoPolyEncoder)⌝ ∗
      (stackAt fsp encoderFromPbStack ∗
       memRegion fsp 2304 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x800000000000000a#64) ∗
       ((pbA + 8#64) ↦₆₄ cap_enc) ∗
       v10_optProtoPolyEncoderTail A.repAlloc (pbA + 8#64) cap_enc
         (sendingCt2.map pbToProtoPolyEncoder) ∗
       ((pbA + 64#64) ↦₆₄ none2Cap) ∗
       memRegion (pbA + 72#64) 48 ∗
       memRegion (pbA + 120#64) 104 ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool lim st s1) := by
  refine Entails.trans
    (Entails.of_eq (show _ =
      ((fsp ↦₆₄ 0#64) ∗ memRegion (fsp + 8#64) 2296) ∗
      (stackAt fsp encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       ((pbA ↦₆₄ 0x800000000000000a#64) ∗
        protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64) { sendingCt2 := sendingCt2, uc := none } ∗
        memRegion (pbA + 120#64) 104) ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool lim st s1) by sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (v10_fsp_unsplit_0 fsp)) ?_
  refine Entails.trans ?_
    (v10_ct2Sent_expose_pre_uc_none_2304_placed A lim st fsp out pbA s0 s1 sendingCt2)
  exact Entails.of_eq (by sep_ac_rfl)

/-- Expose `cap_enc` and `noneCap` on `memRegion fsp 2304` when `auth = none`. -/
theorem v10_ct2Sent_expose_pre_auth_none_2304_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (fsp out pbA epoch : BitVec 64) (s0 s1 : State) (sendingCt2 : Option PolynomialEncoderPB) :
    stackAt fsp encoderFromPbStack ∗
      memRegion fsp 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗
       protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64)
         { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } } ∗
       memRegion (pbA + 120#64) 104) ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st s1 ⊢
    ∃∗ cap_enc : BitVec 64,
      ⌜v10_optEncoderCapProp cap_enc (sendingCt2.map pbToProtoPolyEncoder)⌝ ∗
      (stackAt fsp encoderFromPbStack ∗
       memRegion fsp 2304 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x800000000000000a#64) ∗
       ((pbA + 8#64) ↦₆₄ cap_enc) ∗
       v10_optProtoPolyEncoderTail A.repAlloc (pbA + 8#64) cap_enc
         (sendingCt2.map pbToProtoPolyEncoder) ∗
       ((pbA + 64#64) ↦₆₄ noneCap) ∗
       memRegion (pbA + 72#64) 40 ∗
       ((pbA + 112#64) ↦₆₄ epoch) ∗
       memRegion (pbA + 120#64) 104 ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool lim st s1) := by
  rw [v10_protoChunkedCt2SampledAt_auth_none]
  refine Entails.trans
    (Entails.of_eq (show _ =
      optProtoPolynomialEncoderAt A.repAlloc (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder) ∗
      (stackAt fsp encoderFromPbStack ∗
       memRegion fsp 2304 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x800000000000000a#64) ∗
       ((pbA + 64#64) ↦₆₄ noneCap) ∗
       memRegion (pbA + 72#64) 40 ∗
       ((pbA + 112#64) ↦₆₄ epoch) ∗
       memRegion (pbA + 120#64) 104 ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool lim st s1) by sep_ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono_left
      (v10_optProtoPolyEncoder_expose_cap A.repAlloc (pbA + 8#64)
        (sendingCt2.map pbToProtoPolyEncoder))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.sepExists_elim fun cap_enc =>
    Entails.sepExists_right cap_enc (Entails.of_eq (by sep_ac_rfl))

/-- Expose `cap_enc` and `noneCap` on `(fsp ↦₆₄ 0#64) ∗ memRegion (fsp + 8#64) 2296`
    when `auth = none`. -/
theorem v10_ct2Sent_expose_pre_auth_none_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (fsp out pbA epoch : BitVec 64) (s0 s1 : State) (sendingCt2 : Option PolynomialEncoderPB) :
    stackAt fsp encoderFromPbStack ∗
      (fsp ↦₆₄ 0#64) ∗
      memRegion (fsp + 8#64) 2296 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗
       protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64)
         { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } } ∗
       memRegion (pbA + 120#64) 104) ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st s1 ⊢
    ∃∗ cap_enc : BitVec 64,
      ⌜v10_optEncoderCapProp cap_enc (sendingCt2.map pbToProtoPolyEncoder)⌝ ∗
      (stackAt fsp encoderFromPbStack ∗
       memRegion fsp 2304 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x800000000000000a#64) ∗
       ((pbA + 8#64) ↦₆₄ cap_enc) ∗
       v10_optProtoPolyEncoderTail A.repAlloc (pbA + 8#64) cap_enc
         (sendingCt2.map pbToProtoPolyEncoder) ∗
       ((pbA + 64#64) ↦₆₄ noneCap) ∗
       memRegion (pbA + 72#64) 40 ∗
       ((pbA + 112#64) ↦₆₄ epoch) ∗
       memRegion (pbA + 120#64) 104 ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool lim st s1) := by
  refine Entails.trans
    (Entails.of_eq (show _ =
      ((fsp ↦₆₄ 0#64) ∗ memRegion (fsp + 8#64) 2296) ∗
      (stackAt fsp encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       ((pbA ↦₆₄ 0x800000000000000a#64) ∗
        protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64)
          { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } } ∗
        memRegion (pbA + 120#64) 104) ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool lim st s1) by sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (v10_fsp_unsplit_0 fsp)) ?_
  refine Entails.trans ?_
    (v10_ct2Sent_expose_pre_auth_none_2304_placed A lim st fsp out pbA epoch s0 s1 sendingCt2)
  exact Entails.of_eq (by sep_ac_rfl)

/-- `Ct2Sampled` (`+1632`) early error path (`memRegion (s0.sp - 2400) 2304` form) when
    `s.uc = none`, parameterized by a Block-`271` `dropProtoPolyEncoderSpec` contract. -/
theorem v10_ct2Sent_err_1632_uc_none_2304_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop_ok : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 271) (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (st : M.σ) (s0 s1 : State) (out pbA : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64) { sendingCt2 := sendingCt2, uc := none } ∗
         memRegion (pbA + 120#64) 104) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  refine SepWP.weaken_pre
    (v10_ct2Sent_expose_pre_uc_none_2304_placed A lim st (s0.sp - 2400#64) out pbA s0 s1 sendingCt2) ?_
  apply ProofLib.SepWP.exists_left; intro cap_enc
  apply ProofLib.SepWP.pure_elim; intro hcap
  refine seq_clean_lscl_st hcl1
    (mid := lsmpl.base 333 + 2064#64)
    (P_mid := fun sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      optProtoPolynomialEncoderAt A.repAlloc (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder) ∗
      A.pool lim st sm ∗
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗
       memRegion (pbA + 64#64) 160 ∗
       statesFromPbJumpTablePlacedAt))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x23 = pbA + 8#64 ∧
      sm.readReg64 .x22 = cap_enc ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [BitVec.ofNat_eq_ofNat, none2Cap] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 1632#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 2064#64) s1 _ _
    wp_steps_sync_333 ((blkPl_333).base + 2064#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      have hunexp := v10_optProtoPolyEncoder_unexpose_cap A.repAlloc (pbA + 8#64) cap_enc
        (sendingCt2.map pbToProtoPolyEncoder)
      have hpb64 := v10_pb_64_none_entails_160 pbA
      unfold none2Cap at hpb64
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((pbA + 8#64) ↦₆₄ cap_enc) ∗
           v10_optProtoPolyEncoderTail A.repAlloc (pbA + 8#64) cap_enc
             (sendingCt2.map pbToProtoPolyEncoder)) ∗
          (((pbA + 64#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
           memRegion (pbA + 72#64) 48 ∗
           memRegion (pbA + 120#64) 104) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           (pbA ↦₆₄ 0x800000000000000a#64) ∗
           statesFromPbJumpTablePlacedAt ∗
           A.pool lim st sc) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hunexp (sepConj_mono_left hpb64))
        (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx23_2, hx22_2, htr2⟩
    have hx22_prop : match sendingCt2.map pbToProtoPolyEncoder with
        | none => s2.readReg64 .x22 = noneCap
        | some _ => (s2.readReg64 .x22).toNat < 2 ^ 63 := by
      rw [hx22_2]; exact hcap
    have h2064 := v10_states_from_pb_err_2064_of_sub_placed (F := F) hdrop_ok st s0 s2 out
      (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder)
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗
       memRegion (pbA + 64#64) 160 ∗
       statesFromPbJumpTablePlacedAt)
      hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx22_prop htr2
    refine SepWP.mono h2064 fun sf Pf _ _ ⟨evs, hevs, hPf, hsp_f, hcs_f, htr_f⟩ => ?_
    refine ⟨evs, hevs, Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
    have hpb := v10_pb_tag_56_160_entails_224 pbA 0x800000000000000a#64
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗ memRegion (pbA + 8#64) 56 ∗ memRegion (pbA + 64#64) 160) ∗
        (resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
         statesFromPbJumpTablePlacedAt ∗
         A.pool lim (M.stepEvents evs st) sf ∗
         stackAt s0.sp statesFromPbStack) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by sep_ac_rfl))

theorem v10_ct2Sent_err_1632_uc_none_2304_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out pbA : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64) { sendingCt2 := sendingCt2, uc := none } ∗
         memRegion (pbA + 120#64) 104) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v10_ct2Sent_err_1632_uc_none_2304_of_sub_placed
    (v10_sub_ok_drop_proto_poly_encoder_of_dealloc_placed hdealloc)
    st s0 s1 out pbA sendingCt2 hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

theorem v10_ct2Sent_err_1632_uc_none_2304_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out pbA : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64) { sendingCt2 := sendingCt2, uc := none } ∗
         memRegion (pbA + 120#64) 104) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v10_ct2Sent_err_1632_uc_none_2304_of_dealloc_placed hA.dealloc
    st s0 s1 out pbA sendingCt2 hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

/-- `Ct2Sampled` (`+1632`) early error path (`(fsp ↦₆₄ 0) ∗ memRegion (fsp + 8) 2296` form) when
    `s.uc = none`, parameterized by a Block-`271` `dropProtoPolyEncoderSpec` contract. -/
theorem v10_ct2Sent_err_1632_uc_none_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop_ok : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 271) (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (st : M.σ) (s0 s1 : State) (out pbA : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
        memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64) { sendingCt2 := sendingCt2, uc := none } ∗
         memRegion (pbA + 120#64) 104) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine SepWP.weaken_pre ?_
    (v10_ct2Sent_err_1632_uc_none_2304_of_sub_placed hdrop_ok
      st s0 s1 out pbA sendingCt2 hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)
  refine Entails.trans (Entails.of_eq (show _ =
    (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     ((pbA ↦₆₄ 0x800000000000000a#64) ∗
      protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64) { sendingCt2 := sendingCt2, uc := none } ∗
      memRegion (pbA + 120#64) 104) ∗
     statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1) by sep_ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left (v10_fsp_unsplit_0 (s0.sp - 2400#64)))
    (Entails.of_eq (by sep_ac_rfl))

theorem v10_ct2Sent_err_1632_uc_none_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out pbA : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
        memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64) { sendingCt2 := sendingCt2, uc := none } ∗
         memRegion (pbA + 120#64) 104) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v10_ct2Sent_err_1632_uc_none_of_sub_placed
    (v10_sub_ok_drop_proto_poly_encoder_of_dealloc_placed hdealloc)
    st s0 s1 out pbA sendingCt2 hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

theorem v10_ct2Sent_err_1632_uc_none_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out pbA : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
        memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64) { sendingCt2 := sendingCt2, uc := none } ∗
         memRegion (pbA + 120#64) 104) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v10_ct2Sent_err_1632_uc_none_of_dealloc_placed hA.dealloc
    st s0 s1 out pbA sendingCt2 hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

/-- `Ct2Sampled` (`+1632`) early error path (`memRegion (s0.sp - 2400) 2304` form) when
    `s.uc = some { auth := none, epoch := epoch }`, parameterized by a Block-`271`
    `dropProtoPolyEncoderSpec` contract. -/
theorem v10_ct2Sent_err_1632_auth_none_2304_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop_ok : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 271) (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (st : M.σ) (s0 s1 : State) (out pbA epoch : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64)
           { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } } ∗
         memRegion (pbA + 120#64) 104) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  refine SepWP.weaken_pre
    (v10_ct2Sent_expose_pre_auth_none_2304_placed A lim st (s0.sp - 2400#64) out pbA epoch s0 s1 sendingCt2) ?_
  apply ProofLib.SepWP.exists_left; intro cap_enc
  apply ProofLib.SepWP.pure_elim; intro hcap
  refine seq_clean_lscl_st hcl1
    (mid := lsmpl.base 333 + 2064#64)
    (P_mid := fun sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      optProtoPolynomialEncoderAt A.repAlloc (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder) ∗
      A.pool lim st sm ∗
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗
       memRegion (pbA + 64#64) 160 ∗
       statesFromPbJumpTablePlacedAt))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x23 = pbA + 8#64 ∧
      sm.readReg64 .x22 = cap_enc ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [BitVec.ofNat_eq_ofNat, noneCap] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 1632#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 2064#64) s1 _ _
    wp_steps_sync_333 ((blkPl_333).base + 2064#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      have hunexp := v10_optProtoPolyEncoder_unexpose_cap A.repAlloc (pbA + 8#64) cap_enc
        (sendingCt2.map pbToProtoPolyEncoder)
      have hpb64 := v10_pb_64_auth_none_entails_160 pbA epoch
      unfold noneCap at hpb64
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((pbA + 8#64) ↦₆₄ cap_enc) ∗
           v10_optProtoPolyEncoderTail A.repAlloc (pbA + 8#64) cap_enc
             (sendingCt2.map pbToProtoPolyEncoder)) ∗
          (((pbA + 64#64) ↦₆₄ 0xffffffffffffffff#64) ∗
           memRegion (pbA + 72#64) 40 ∗
           ((pbA + 112#64) ↦₆₄ epoch) ∗
           memRegion (pbA + 120#64) 104) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           (pbA ↦₆₄ 0x800000000000000a#64) ∗
           statesFromPbJumpTablePlacedAt ∗
           A.pool lim st sc) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hunexp (sepConj_mono_left hpb64))
        (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx23_2, hx22_2, htr2⟩
    have hx22_prop : match sendingCt2.map pbToProtoPolyEncoder with
        | none => s2.readReg64 .x22 = noneCap
        | some _ => (s2.readReg64 .x22).toNat < 2 ^ 63 := by
      rw [hx22_2]; exact hcap
    have h2064 := v10_states_from_pb_err_2064_of_sub_placed (F := F) hdrop_ok st s0 s2 out
      (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder)
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗
       memRegion (pbA + 64#64) 160 ∗
       statesFromPbJumpTablePlacedAt)
      hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx22_prop htr2
    refine SepWP.mono h2064 fun sf Pf _ _ ⟨evs, hevs, hPf, hsp_f, hcs_f, htr_f⟩ => ?_
    refine ⟨evs, hevs, Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
    have hpb := v10_pb_tag_56_160_entails_224 pbA 0x800000000000000a#64
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗ memRegion (pbA + 8#64) 56 ∗ memRegion (pbA + 64#64) 160) ∗
        (resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
         statesFromPbJumpTablePlacedAt ∗
         A.pool lim (M.stepEvents evs st) sf ∗
         stackAt s0.sp statesFromPbStack) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by sep_ac_rfl))

theorem v10_ct2Sent_err_1632_auth_none_2304_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out pbA epoch : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64)
           { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } } ∗
         memRegion (pbA + 120#64) 104) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v10_ct2Sent_err_1632_auth_none_2304_of_sub_placed
    (v10_sub_ok_drop_proto_poly_encoder_of_dealloc_placed hdealloc)
    st s0 s1 out pbA epoch sendingCt2 hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

theorem v10_ct2Sent_err_1632_auth_none_2304_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out pbA epoch : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64)
           { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } } ∗
         memRegion (pbA + 120#64) 104) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v10_ct2Sent_err_1632_auth_none_2304_of_dealloc_placed hA.dealloc
    st s0 s1 out pbA epoch sendingCt2 hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

/-- `Ct2Sampled` (`+1632`) early error path (`(fsp ↦₆₄ 0) ∗ memRegion (fsp + 8) 2296` form) when
    `s.uc = some { auth := none, epoch := epoch }`, parameterized by a Block-`271`
    `dropProtoPolyEncoderSpec` contract. -/
theorem v10_ct2Sent_err_1632_auth_none_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop_ok : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 271) (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (st : M.σ) (s0 s1 : State) (out pbA epoch : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
        memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64)
           { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } } ∗
         memRegion (pbA + 120#64) 104) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine SepWP.weaken_pre ?_
    (v10_ct2Sent_err_1632_auth_none_2304_of_sub_placed hdrop_ok
      st s0 s1 out pbA epoch sendingCt2 hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)
  refine Entails.trans (Entails.of_eq (show _ =
    (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     ((pbA ↦₆₄ 0x800000000000000a#64) ∗
      protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64)
        { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } } ∗
      memRegion (pbA + 120#64) 104) ∗
     statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1) by sep_ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left (v10_fsp_unsplit_0 (s0.sp - 2400#64)))
    (Entails.of_eq (by sep_ac_rfl))

theorem v10_ct2Sent_err_1632_auth_none_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out pbA epoch : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
        memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64)
           { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } } ∗
         memRegion (pbA + 120#64) 104) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v10_ct2Sent_err_1632_auth_none_of_sub_placed
    (v10_sub_ok_drop_proto_poly_encoder_of_dealloc_placed hdealloc)
    st s0 s1 out pbA epoch sendingCt2 hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

theorem v10_ct2Sent_err_1632_auth_none_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out pbA epoch : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
        memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ 0x800000000000000a#64) ∗
         protoChunkedCt2SampledAt A.repAlloc (pbA + 8#64)
           { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } } ∗
         memRegion (pbA + 120#64) 104) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v10_ct2Sent_err_1632_auth_none_of_dealloc_placed hA.dealloc
    st s0 s1 out pbA epoch sendingCt2 hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1


end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10bPlacedBudgetAux
