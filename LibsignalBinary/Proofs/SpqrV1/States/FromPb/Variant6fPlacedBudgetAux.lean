/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6dPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6fPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6d
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6e
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6f
import ProofLib.SepLogic.WPp

/-!
# Auxiliary Exit and Staging Lemmas for `Variant6fPlacedBudget`

Defines `V6hrAuthCloneEnv` and lifts the Variant 6 (`HeaderReceived`, Block `333`) error exits
(`+10324 -> ret`, `+10316 -> ret`), `Ok` staging (`+10000 -> +8180`), and `Ok` epilogue
(`+10000 -> ret`) to `VmPreserved` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6fPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1
  (PolyDecoder ProtoAuthenticator ProtoPolynomialDecoder States)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize)
open CryptoVerification.SpqrV1.Poly (polyDecoderAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack loByte unshiftWord)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved epilogueOutFull epilogueStackGaps epilogueStackSlots
   overlapWord7 resultChunkedStatesAt spqrErrorByte statesFromPbSavedCells statesFromPbStack
   v1_bv_add_add_lit v1_bv_sub_sub_lit v6hr_DecWords v6hr_Saved10324Preserved
   v6hr_decHeap v6hr_decHeap_w0_lt v6hr_decWordsAt v6hr_epilogueOutFull_entails_ok
   v6hr_lowStackAt v6hr_midQ128 v6hr_polyDecoderAt_unpack
   v6hr_stackAt_allocHook_to_encoderFromPbStack v6hr_stackAt_encoderFromPbStack_to_allocHook
   v6hr_stackRest10000 v6hr_stack_10000_ok_entails v6hr_stack_8180_entails
   v6hr_stagingSlotsPost v6hr_stagingSlotsPre)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
  (AuthFromPbEnv authKeyCloneEvents fitsEvents_of_fitsEnv_authFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget (FromPbDecEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6aPlacedBudget
  (v6hr_sub_ok_dealloc_of_placedHooks v6hr_sub_ok_dealloc_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
  v6hr_stagingSlotsPre v6hr_stagingSlotsPost v6hr_decWordsAt
  v6hr_stackRest10000 v6hr_decHeap epilogueStackSlots epilogueStackGaps epilogueOutFull
  resultChunkedStatesAt statesFromPbSavedCells vecU8Payload
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit

@[local simp] private theorem stripS_readReg32 (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (ProofLib.stripS keep s).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

/-! ## 0. Allocation Envelope Helpers for Variant 6 (`HeaderReceived`) -/

/-- Exact allocator event envelope of Variant 6's `ProtoAuthenticator` buffer clone + input cleanup
    phase (`+3760 -> +9936`): clones `rootKey` then `macKey`, followed by `FreeOnlyEvs` cleanup of
    the input `ProtoAuthenticator` buffers. -/
def V6hrAuthCloneEnv (rootKey macKey : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ∃ evs_free : List AllocEvent,
    FreeOnlyEvs evs_free ∧
    evs = authKeyCloneEvents rootKey ++ authKeyCloneEvents macKey ++ evs_free

theorem fitsEvents_authClone_of_fitsEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {authPb : ProtoAuthenticator}
    (h : FitsEnv M lim st (AuthFromPbEnv authPb)) :
    FitsEvents M lim st (authKeyCloneEvents authPb.rootKey ++ authKeyCloneEvents authPb.macKey) :=
  fitsEvents_of_fitsEnv_authFromPbEnv h

theorem fromPbDecEnv_append_freeOnly {pb : ProtoPolynomialDecoder}
    {evs1 evs2 : List AllocEvent}
    (h1 : FromPbDecEnv pb evs1) (h2 : FreeOnlyEvs evs2) :
    FromPbDecEnv pb (evs1 ++ evs2) := by
  rcases h1 with ⟨ea, ef, rfl, ha, hf⟩
  exact ⟨ea, ef ++ evs2, List.append_assoc ea ef evs2, ha, hf.append h2⟩

/-! ## 1. Error Exit Paths (`+10324 -> ret` and `+10316 -> ret`) -/

theorem v6hr_exit_err_10324_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ptsPtr ptsCap : BitVec 64)
    (pts : List (List (BitVec 8)))
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat) (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 10324#64) (hrun1 : s1.status = .Running)
    (hpres1 : v6hr_Saved10324Preserved s0 s1 (s0.sp - 2400#64) out ptsPtr ptsCap 2#64)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (if ptsCap = 0#64 then emp
         else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
             ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .msgDecode)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hif :
      (if ptsCap = 0#64 then emp
       else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
         arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
         memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
           ((ptsCap.toNat - pts.length) * 24)) =
      (if ptsCap = 0 then emp
       else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
         arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
         memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
           ((ptsCap.toNat - pts.length) * 24)) := rfl
  rw [hif]
  refine SepWP.weaken_pre
    (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  have h1 := Variant6aPlacedBudget.v6hr_states_from_pb_dealloc_proto_decoder_10324_of_sub_placed
    hdealloc_ok st s0 s1 (s0.sp - 2400#64) out ptsPtr ptsCap 2#64 pts
    (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
     v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
     memRegion (s0.sp - 2160#64) 2064 ∗
     statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ Rest)
    hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx23_1
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.seq h1 ?_)
  intro s2 P2 hpc2 hrun2 ⟨evs, hevs, hP2, ⟨hsp2, hx19_2, _, _, hx25_2, htr2⟩, _⟩
  refine SepWP.weaken_pre hP2 ?_
  have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
        (v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
         memRegion (s0.sp - 2160#64) 2064 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ A.pool lim (M.stepEvents evs st) s2 ∗ Rest) by
        sep_ac_rfl))
      (sepConj_mono_left hst)) ?_
  have hx25_b : (s2.readReg64 .x25).extractLsb' 0 8 = spqrErrorByte .msgDecode := by
    rw [hx25_2]; rfl
  have herr := Variant6aPlacedBudget.v6hr_states_from_pb_err_10396_placed_budget
    A lim (M.stepEvents evs st) (F := F) (ext := ext) s0 s2 out
    v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 .msgDecode Rest
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx25_b htr2
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono herr ?_)
  intro sf Pf _ _ ⟨hPf, _, hsp_f, hcs_f, htr_f⟩
  exact ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcs_f, htr_f⟩

theorem v6hr_exit_err_10324_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ptsPtr ptsCap : BitVec 64)
    (pts : List (List (BitVec 8)))
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat) (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 10324#64) (hrun1 : s1.status = .Running)
    (hpres1 : v6hr_Saved10324Preserved s0 s1 (s0.sp - 2400#64) out ptsPtr ptsCap 2#64)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (if ptsCap = 0#64 then emp
         else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
             ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .msgDecode)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v6hr_exit_err_10324_of_sub_placed (v6hr_sub_ok_dealloc_of_placedHooks hA) st s0 s1
    out ptsPtr ptsCap pts v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 Rest
    hsp0_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx23_1

theorem v6hr_exit_err_10324_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ptsPtr ptsCap : BitVec 64)
    (pts : List (List (BitVec 8)))
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat) (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 10324#64) (hrun1 : s1.status = .Running)
    (hpres1 : v6hr_Saved10324Preserved s0 s1 (s0.sp - 2400#64) out ptsPtr ptsCap 2#64)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (if ptsCap = 0#64 then emp
         else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
             ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .msgDecode)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v6hr_exit_err_10324_of_sub_placed (v6hr_sub_ok_dealloc_placed hA) st s0 s1
    out ptsPtr ptsCap pts v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 Rest
    hsp0_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx23_1

/-- `VmPreserved`-strengthened `+10316 -> ret` error exit when `receivingEk = none` (`ptsCap = noneCap`). -/
theorem v6hr_exit_err_10316_none_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out ptsPtr x25_val : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10316#64) (hrun1 : s1.status = .Running)
    (hx25_1 : x25_val.extractLsb' 0 8 = 0#8)
    (hpres1 : v6hr_Saved10324Preserved s0 s1 (s0.sp - 2400#64) out ptsPtr noneCap x25_val) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          (A.pool ∗ Rest) ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine SepWP.seq
    (Variant6aPlacedBudget.v6hr_states_from_pb_dealloc_none_proto_decoder_10316_placed
      s0 s1 (s0.sp - 2400#64) out ptsPtr x25_val _ hpc1 hrun1 hpres1) ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, ⟨hsp2, hx19_2, _, _, hx25_2, htr2⟩, hvm1, _⟩
  refine SepWP.weaken_pre hP2 ?_
  have hx25_b : (s2.readReg64 .x25).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx25_2, hx25_1]; rfl
  have herr := Variant6aPlacedBudget.v6hr_states_from_pb_err_10396_placed (A := A) (F := F)
    (ext := ext) s0 s2 out v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
    .stateDecode (A.pool ∗ Rest) hsp0_align hpc2 hrun2 hsp2 hx19_2 hx25_b htr2
  exact SepWP.mono herr fun sf Pf _ _ ⟨hPf, hvm2, hsp_f, hcs_f, htr_f⟩ =>
    ⟨hPf, hvm1.trans hvm2, hsp_f, hcs_f, htr_f⟩

theorem v6hr_exit_err_10316_none_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out ptsPtr x25_val : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10316#64) (hrun1 : s1.status = .Running)
    (hx25_1 : x25_val.extractLsb' 0 8 = 0#8)
    (hpres1 : v6hr_Saved10324Preserved s0 s1 (s0.sp - 2400#64) out ptsPtr noneCap x25_val) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
          (A.pool lim st sf ∗ Rest) ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hwp := v6hr_exit_err_10316_none_placed (A := A.repAlloc) (F := F) (ext := ext)
    s0 s1 out ptsPtr x25_val v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
    (A.pool lim st s1 ∗ Rest) hsp0_align hpc1 hrun1 hx25_1 hpres1
  have hpre_eq :
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗ Rest) =
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.repAlloc.pool ∗ (A.pool lim st s1 ∗ Rest)) := by
    simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj]
  rw [hpre_eq]
  refine SepWP.mono hwp fun sf Pf _ _ ⟨hPf, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPf
  simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj] at hPf
  exact ⟨hPf, hvm, hrest⟩

theorem v6hr_exit_err_10316_some_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ptsPtr ptsCap x25_val : BitVec 64)
    (pts : List (List (BitVec 8)))
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat) (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 10316#64) (hrun1 : s1.status = .Running)
    (hx25_1 : x25_val.extractLsb' 0 8 = 0#8)
    (hpres1 : v6hr_Saved10324Preserved s0 s1 (s0.sp - 2400#64) out ptsPtr ptsCap x25_val)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (if ptsCap = 0#64 then emp
         else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
             ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hif :
      (if ptsCap = 0#64 then emp
       else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
         arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
         memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
           ((ptsCap.toNat - pts.length) * 24)) =
      (if ptsCap = 0 then emp
       else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
         arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
         memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
           ((ptsCap.toNat - pts.length) * 24)) := rfl
  rw [hif]
  refine SepWP.weaken_pre
    (sepConj_mono_left (v6hr_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  have h1 := Variant6aPlacedBudget.v6hr_states_from_pb_dealloc_some_proto_decoder_10316_of_sub_placed
    hdealloc_ok st s0 s1 (s0.sp - 2400#64) out ptsPtr ptsCap x25_val pts
    (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
     v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
     memRegion (s0.sp - 2160#64) 2064 ∗
     statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ Rest)
    hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx23_1
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.seq h1 ?_)
  intro s2 P2 hpc2 hrun2 ⟨evs, hevs, hP2, ⟨hsp2, hx19_2, _, _, hx25_2, htr2⟩, _⟩
  refine SepWP.weaken_pre hP2 ?_
  have hst := v6hr_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
        (v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
         memRegion (s0.sp - 2160#64) 2064 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ A.pool lim (M.stepEvents evs st) s2 ∗ Rest) by
        sep_ac_rfl))
      (sepConj_mono_left hst)) ?_
  have hx25_b : (s2.readReg64 .x25).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx25_2, hx25_1]; rfl
  have herr := Variant6aPlacedBudget.v6hr_states_from_pb_err_10396_placed_budget
    A lim (M.stepEvents evs st) (F := F) (ext := ext) s0 s2 out
    v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 .stateDecode Rest
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx25_b htr2
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono herr ?_)
  intro sf Pf _ _ ⟨hPf, _, hsp_f, hcs_f, htr_f⟩
  exact ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcs_f, htr_f⟩

theorem v6hr_exit_err_10316_some_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ptsPtr ptsCap x25_val : BitVec 64)
    (pts : List (List (BitVec 8)))
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat) (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 10316#64) (hrun1 : s1.status = .Running)
    (hx25_1 : x25_val.extractLsb' 0 8 = 0#8)
    (hpres1 : v6hr_Saved10324Preserved s0 s1 (s0.sp - 2400#64) out ptsPtr ptsCap x25_val)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (if ptsCap = 0#64 then emp
         else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
             ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v6hr_exit_err_10316_some_of_sub_placed (v6hr_sub_ok_dealloc_of_placedHooks hA) st s0 s1
    out ptsPtr ptsCap x25_val pts v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 Rest
    hsp0_align hpts_le hpts_cap_lt hpc1 hrun1 hx25_1 hpres1 hx23_1

theorem v6hr_exit_err_10316_some_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ptsPtr ptsCap x25_val : BitVec 64)
    (pts : List (List (BitVec 8)))
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat) (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 10316#64) (hrun1 : s1.status = .Running)
    (hx25_1 : x25_val.extractLsb' 0 8 = 0#8)
    (hpres1 : v6hr_Saved10324Preserved s0 s1 (s0.sp - 2400#64) out ptsPtr ptsCap x25_val)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (if ptsCap = 0#64 then emp
         else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
             ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v6hr_exit_err_10316_some_of_sub_placed (v6hr_sub_ok_dealloc_placed hA) st s0 s1
    out ptsPtr ptsCap x25_val pts v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 Rest
    hsp0_align hpts_le hpts_cap_lt hpc1 hrun1 hx25_1 hpres1 hx23_1

/-! ## 2. `Ok` Staging (`+10000 -> +8180`) and Epilogue (`+10000 -> ret`) -/

/-- `VmPreserved`-strengthened Variant 6 `Ok` staging step (`+10000 -> +8180`, 77 instructions). -/
theorem v6hr_step_10000_ok_to_8180_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out c0 p0 l0 l1 p1_new l2 p2_new ep : BitVec 64)
    (dw : v6hr_DecWords)
    (u160 : BitVec 64) (d172 : BitVec 32) (u208 u224 u232 : BitVec 64)
    (uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816 : BitVec 128)
    (u832 : BitVec 64) (uq848 : BitVec 128) (u864 u880 u888 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hw0_lt : dw.g0.w0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 10000#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = p1_new)
    (hx26 : s.readReg64 .x26 = l1) (hx27 : s.readReg64 .x27 = c0)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8180#64) s
      (((fsp + 80#64) ↦₆₄ l0) ∗ ((fsp + 128#64) ↦₆₄ ep) ∗
        ((fsp + 136#64) ↦₆₄ p2_new) ∗ ((fsp + 144#64) ↦₆₄ p0) ∗
        ((fsp + 216#64) ↦₆₄ l2) ∗
        v6hr_stagingSlotsPre fsp u160 d172 u208 u224 u232
          uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
          u832 uq848 u864 u880 u888 ∗
        v6hr_decWordsAt (fsp + 1888#64) dw ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((fsp + 80#64) ↦₆₄ l0) ∗ ((fsp + 128#64) ↦₆₄ ep) ∗
          ((fsp + 136#64) ↦₆₄ p2_new) ∗ ((fsp + 144#64) ↦₆₄ p0) ∗
          ((fsp + 216#64) ↦₆₄ l2) ∗
          v6hr_stagingSlotsPost fsp dw p1_new ∗
          v6hr_decWordsAt (fsp + 1888#64) dw ∗ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = fsp ∧
        s2.readReg64 .x6 = fsp + 576#64 ∧
        s2.readReg64 .x8 = 8#64 ∧
        s2.readReg64 .x15 = l1 ∧
        s2.readReg64 .x20 = l1 ∧
        s2.readReg64 .x13 = l2 ∧
        s2.readReg64 .x25 = p2_new ∧
        s2.readReg64 .x30 = l2 ∧
        s2.readReg64 .x9 = c0 ∧
        s2.readReg64 .x14 = p0 ∧
        s2.readReg64 .x18 = l0 ∧
        s2.readReg64 .x17 = ep ∧
        s2.readReg64 .x0 = dw.g0.w0 ∧
        (s2.readReg32 .x3).setWidth 8 = dw.g0.w8.extractLsb' 0 8 ∧
        s2.readReg32 .x27 = dw.g0.w8.extractLsb' 8 32 ∧
        ((s2.readReg64 .x27 >>> 32).setWidth 32).setWidth 16 = dw.g0.w8.extractLsb' 40 16 ∧
        ((s2.readReg64 .x27 >>> 48).setWidth 32).setWidth 8 = dw.g0.w8.extractLsb' 56 8 ∧
        s2.readReg64 .x4 = dw.g0.w16 ∧
        s2.readReg64 .x5 = dw.g0.w24 ∧
        (s2.readReg32 .x21).setWidth 8 = loByte dw.g0.w32 ∧
        s2.readReg64 .x7 = dw.g0.w48 ∧
        s2.readReg64 .x2 = dw.g3.u312 ∧
        s2.readReg64 .x11 = dw.g3.u320 ∧
        s2.readReg64 .x22 = dw.g3.u328 ∧
        s2.readReg64 .x24 = dw.g3.u336 ∧
        s2.readReg64 .x10 = dw.g4.u352 ∧
        s2.readReg64 .x26 = dw.g4.u368 ∧
        s2.readReg64 .x12 = dw.g4.u376 ∧
        s2.readReg64 .x1 = dw.g4.u384 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x23 = fsp + 848#64 ∧
        TraceCalleeSaved s2 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant6dPlaced.v6hr_step_10000_ok_to_8180_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out c0 p0 l0 l1 p1_new l2 p2_new ep dw
      u160 d172 u208 u224 u232
      uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
      u832 uq848 u864 u880 u888 Rest hfsp_align hw0_lt
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx21) (by simpa using hx26) (by simpa using hx27)
      ⟨by simpa using htr.1, by simpa using htr.2⟩)
    fun s2 P2 hvm
      ⟨hP2, hsp2, hx6_2, hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2,
       hx18_2, hx17_2, hx0_2, hx3_2, hx27_lo, hx27_mid, hx27_hi, hx4_2, hx5_2, hx21_2,
       hx7_2, hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2, hx12_2, hx1_2, hx19_2, hx23_2,
       htr2⟩ =>
      ⟨hP2, hvm, by simpa using hsp2, by simpa using hx6_2, by simpa using hx8_2,
       by simpa using hx15_2, by simpa using hx20_2, by simpa using hx13_2,
       by simpa using hx25_2, by simpa using hx30_2, by simpa using hx9_2,
       by simpa using hx14_2, by simpa using hx18_2, by simpa using hx17_2,
       by simpa using hx0_2, by simpa using hx3_2, by simpa using hx27_lo,
       by simpa using hx27_mid, by simpa using hx27_hi, by simpa using hx4_2,
       by simpa using hx5_2, by simpa using hx21_2, by simpa using hx7_2,
       by simpa using hx2_2, by simpa using hx11_2, by simpa using hx22_2,
       by simpa using hx24_2, by simpa using hx10_2, by simpa using hx26_2,
       by simpa using hx12_2, by simpa using hx1_2, by simpa using hx19_2,
       by simpa using hx23_2, ⟨by simpa using htr2.1, by simpa using htr2.2⟩⟩

set_option maxHeartbeats 800000 in
theorem v6hr_step_10000_ok_to_exit_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_ok : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsρ "memcpy") allocMemcpyVmSpec)
    (s0 s1 : State) (out c0 p0 p1_new p2_new ep p2 w120 ptsPtr : BitVec 64)
    (d184 d200 : BitVec 32) (rootKey macKey hdrBytes : List (BitVec 8))
    (dec : PolyDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hhdr : hdrBytes.length = 64)
    (hpc1 : s1.pc = lsmpl.base 333 + 10000#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = BitVec.ofNat 64 rootKey.length)
    (hx27_1 : s1.readReg64 .x27 = c0) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (polyDecoderAt A.repAlloc ((s0.sp - 2400#64) + 1888#64) dec ∗
        (v6hr_lowStackAt s0.sp 64#64 ep p2_new p0 d184 p1_new d200 p2
           (BitVec.ofNat 64 macKey.length) w120 ptsPtr ∗
         memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
         (memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗
          memRegion ((s0.sp - 2400#64) + 1432#64) 456 ∗
          memRegion ((s0.sp - 2400#64) + 2288#64) 16)) ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
        vecU8Payload A.repAlloc c0 p0 hdrBytes ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out
            (.ok (.headerReceived
              { uc := { epoch := ep, auth := { rootKey := rootKey, macKey := macKey }, hdr := hdrBytes },
                receiving_ek := dec })) ∗
          (A.pool lim st sf ∗ Rest) ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine SepWP.weaken_pre
    (sepConj_mono (v6hr_polyDecoderAt_unpack A.repAlloc ((s0.sp - 2400#64) + 1888#64) dec)
      (sepConj_mono_left
        (v6hr_stack_10000_ok_entails s0.sp 64#64 ep p2_new p0 d184 p1_new d200 p2
          (BitVec.ofNat 64 macKey.length) w120 ptsPtr))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine ProofLib.SepWP.exists_left fun u160 => ProofLib.SepWP.exists_left fun d172 =>
    ProofLib.SepWP.exists_left fun uq608 => ProofLib.SepWP.exists_left fun uq624 =>
    ProofLib.SepWP.exists_left fun uq640 => ProofLib.SepWP.exists_left fun uq656 =>
    ProofLib.SepWP.exists_left fun uq672 => ProofLib.SepWP.exists_left fun uq688 =>
    ProofLib.SepWP.exists_left fun uq704 => ProofLib.SepWP.exists_left fun uq720 =>
    ProofLib.SepWP.exists_left fun uq736 => ProofLib.SepWP.exists_left fun uq752 =>
    ProofLib.SepWP.exists_left fun uq768 => ProofLib.SepWP.exists_left fun uq784 =>
    ProofLib.SepWP.exists_left fun uq800 => ProofLib.SepWP.exists_left fun uq816 =>
    ProofLib.SepWP.exists_left fun u832 => ProofLib.SepWP.exists_left fun uq848 =>
    ProofLib.SepWP.exists_left fun u864 => ProofLib.SepWP.exists_left fun u880 =>
    ProofLib.SepWP.exists_left fun u888 => ProofLib.SepWP.exists_left fun dw => ?_
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        v6hr_decHeap A.repAlloc dec dw ∗
        (v6hr_decWordsAt ((s0.sp - 2400#64) + 1888#64) dw ∗
         (((s0.sp - 2400#64) + 80#64) ↦₆₄ 64#64) ∗
         (((s0.sp - 2400#64) + 128#64) ↦₆₄ ep) ∗
         (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
         (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
         (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
         v6hr_stagingSlotsPre (s0.sp - 2400#64) u160 d172 p2 w120 ptsPtr
           uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
           u832 uq848 u864 u880 u888 ∗
         v6hr_stackRest10000 (s0.sp - 2400#64) ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
         vecU8Payload A.repAlloc c0 p0 hdrBytes ∗
         A.pool lim st s1 ∗ Rest) by sep_ac_rfl))
      (Entails.trans (sepConj_mono_left (v6hr_decHeap_w0_lt A.repAlloc dec dw))
        (Entails.of_eq (by rw [sepConj_assoc])))) ?_
  apply ProofLib.SepWP.pure_elim; intro hw0_lt
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hstep1 := v6hr_step_10000_ok_to_8180_placed (ext := ext) s0 s1 (s0.sp - 2400#64)
    out c0 p0 64#64 (BitVec.ofNat 64 rootKey.length) p1_new
    (BitVec.ofNat 64 macKey.length) p2_new ep dw
    u160 d172 p2 w120 ptsPtr
    uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
    u832 uq848 u864 u880 u888
    (v6hr_stackRest10000 (s0.sp - 2400#64) ∗
     stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗
     vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
     vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
     vecU8Payload A.repAlloc c0 p0 hdrBytes ∗
     v6hr_decHeap A.repAlloc dec dw ∗ A.pool lim st s1 ∗ Rest)
    hfsp_align hw0_lt hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 hx27_1 htr1
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.seq hstep1 ?_)
  intro s2 P2 hpc2 hrun2
    ⟨hP2, hvm2, hsp2, hx6_2, hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2,
     hx18_2, hx17_2, hx0_2, hx3_2, hx27_lo, hx27_mid, hx27_hi, hx4_2, hx5_2, hx21_2,
     hx7_2, hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2, hx12_2, hx1_2, hx19_2, hx23_2, htr2⟩
  rw [← A.pool_of_vmPreserved hvm2] at hP2
  refine SepWP.weaken_pre hP2 ?_
  have h8180_st := v6hr_stack_8180_entails (s0.sp - 2400#64) 64#64 ep p2_new p0
    (BitVec.ofNat 64 macKey.length) p1_new dw
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        ((((s0.sp - 2400#64) + 80#64) ↦₆₄ 64#64) ∗
         (((s0.sp - 2400#64) + 128#64) ↦₆₄ ep) ∗
         (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
         (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
         (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
         v6hr_stagingSlotsPost (s0.sp - 2400#64) dw p1_new ∗
         v6hr_decWordsAt ((s0.sp - 2400#64) + 1888#64) dw ∗
         v6hr_stackRest10000 (s0.sp - 2400#64)) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
         vecU8Payload A.repAlloc c0 p0 hdrBytes ∗
         v6hr_decHeap A.repAlloc dec dw ∗ A.pool lim st s2 ∗ Rest) by sep_ac_rfl))
      (sepConj_mono_left h8180_st)) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine ProofLib.SepWP.exists_left fun d92 => ProofLib.SepWP.exists_left fun w104_s =>
    ProofLib.SepWP.exists_left fun w112_s => ProofLib.SepWP.exists_left fun w120_s =>
    ProofLib.SepWP.exists_left fun w192 => ProofLib.SepWP.exists_left fun bs240 =>
    ProofLib.SepWP.exists_left fun q576 => ProofLib.SepWP.exists_left fun w592 => ?_
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.mono
      (Variant1bPlacedBudgetAux.states_from_pb_epilogue_8180_placed A lim st hmemcpy_ok s0 s2 out
        d92 ((loByte dw.g0.w56).zeroExtend 32)
        w104_s w112_s w120_s dw.g4.u360 w192 p1_new dw.g4.u392 dw.g3.u344
        bs240.val bs240.property q576 w592
        dw.g1.q80 dw.g1.q96 dw.g1.q112 dw.g1.q128 dw.g1.q144 dw.g1.q160
        dw.g2.q176 dw.g2.q192 dw.g2.q208 dw.g2.q224 dw.g2.q240 dw.g2.q256 dw.g2.q272 dw.g2.q288
        dw.g3.u304 (v6hr_midQ128 dw.g0.w56 dw.g1.w64 dw.g1.w72) (dw.g1.w72 >>> 8)
        (unshiftWord dw.g0.w32 (loByte dw.g0.w40)) (dw.g0.w40 >>> 8)
        (dw.g0.w8 ++ dw.g0.w0) (dw.g0.w24 ++ dw.g0.w16) dw.g0.w32
        (vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
         vecU8Payload A.repAlloc c0 p0 hdrBytes ∗
         v6hr_decHeap A.repAlloc dec dw ∗ Rest)
        hsp0_align hpc2 hrun2 hsp2 hx6_2 hx19_2 hx23_2 htr2) ?_)
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f, hvm_f⟩
  refine ⟨?_, hvm2.trans hvm_f, hsp_f, hcs_f, htr_f⟩
  rw [hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2,
      hx18_2, hx17_2, hx0_2, hx3_2, hx27_lo, hx27_mid, hx27_hi, hx4_2, hx5_2, hx21_2,
      hx7_2, hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2, hx12_2, hx1_2] at hPf
  have hok_out := v6hr_epilogueOutFull_entails_ok A.repAlloc (F := F) out c0 p0 p1_new p2_new ep
    rootKey macKey hdrBytes dec dw
    (s2.readReg64 .x28) w192 (s2.readReg64 .x16) w104_s w112_s w120_s
    (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
    bs240.val bs240.property
    (dw.g0.w8 ++ dw.g0.w0) (dw.g0.w24 ++ dw.g0.w16) dw.g0.w32 hhdr
  refine Entails.trans hPf ?_
  refine Entails.trans
    (Entails.of_eq (show _ =
      (epilogueOutFull out 8#64
        (BitVec.ofNat 64 rootKey.length) p1_new (BitVec.ofNat 64 rootKey.length)
        (BitVec.ofNat 64 macKey.length) p2_new (BitVec.ofNat 64 macKey.length)
        c0 p0 64#64 ep dw.g0.w0
        (dw.g0.w8.extractLsb' 0 8) (dw.g0.w8.extractLsb' 8 32)
        (dw.g0.w8.extractLsb' 40 16) (dw.g0.w8.extractLsb' 56 8)
        dw.g0.w16 dw.g0.w24 (loByte dw.g0.w32)
        (unshiftWord dw.g0.w32 (loByte dw.g0.w40))
        (overlapWord7 (unshiftWord dw.g0.w32 (loByte dw.g0.w40)) (dw.g0.w40 >>> 8))
        dw.g0.w48
        (((loByte dw.g0.w56).zeroExtend 32).setWidth 8)
        (v6hr_midQ128 dw.g0.w56 dw.g1.w64 dw.g1.w72)
        (overlapWord7 ((v6hr_midQ128 dw.g0.w56 dw.g1.w64 dw.g1.w72).extractLsb' 64 64) (dw.g1.w72 >>> 8))
        dw.g1.q80 dw.g1.q96 dw.g1.q112 dw.g1.q128 dw.g1.q144 dw.g1.q160
        dw.g2.q176 dw.g2.q192 dw.g2.q208 dw.g2.q224 dw.g2.q240 dw.g2.q256 dw.g2.q272 dw.g2.q288
        dw.g3.u304 dw.g3.u312 dw.g3.u320 dw.g3.u328 dw.g3.u336 dw.g3.u344
        dw.g4.u352 dw.g4.u360 dw.g4.u368 dw.g4.u376 dw.g4.u384 dw.g4.u392
        (s2.readReg64 .x28) w192 (s2.readReg64 .x16) w104_s w112_s w120_s
        (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
        bs240.val (dw.g0.w8 ++ dw.g0.w0) (dw.g0.w24 ++ dw.g0.w16) dw.g0.w32 ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
       vecU8Payload A.repAlloc c0 p0 hdrBytes ∗
       v6hr_decHeap A.repAlloc dec dw) ∗
      (A.pool lim st sf ∗ Rest) ∗ stackAt s0.sp statesFromPbStack by sep_ac_rfl))
    (sepConj_mono_left hok_out)

theorem v6hr_step_10000_ok_to_exit_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) (st : M.σ)
    (s0 s1 : State) (out c0 p0 p1_new p2_new ep p2 w120 ptsPtr : BitVec 64)
    (d184 d200 : BitVec 32) (rootKey macKey hdrBytes : List (BitVec 8))
    (dec : PolyDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hhdr : hdrBytes.length = 64)
    (hpc1 : s1.pc = lsmpl.base 333 + 10000#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = BitVec.ofNat 64 rootKey.length)
    (hx27_1 : s1.readReg64 .x27 = c0) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (polyDecoderAt A.repAlloc ((s0.sp - 2400#64) + 1888#64) dec ∗
        (v6hr_lowStackAt s0.sp 64#64 ep p2_new p0 d184 p1_new d200 p2
           (BitVec.ofNat 64 macKey.length) w120 ptsPtr ∗
         memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
         (memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗
          memRegion ((s0.sp - 2400#64) + 1432#64) 456 ∗
          memRegion ((s0.sp - 2400#64) + 2288#64) 16)) ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
        vecU8Payload A.repAlloc c0 p0 hdrBytes ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out
            (.ok (.headerReceived
              { uc := { epoch := ep, auth := { rootKey := rootKey, macKey := macKey }, hdr := hdrBytes },
                receiving_ek := dec })) ∗
          (A.pool lim st sf ∗ Rest) ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v6hr_step_10000_ok_to_exit_of_sub_placed A lim st hA.memcpy_ok s0 s1
    out c0 p0 p1_new p2_new ep p2 w120 ptsPtr d184 d200 rootKey macKey hdrBytes dec Rest
    hsp0_align hhdr hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 hx27_1 htr1

theorem v6hr_step_10000_ok_to_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ)
    (s0 s1 : State) (out c0 p0 p1_new p2_new ep p2 w120 ptsPtr : BitVec 64)
    (d184 d200 : BitVec 32) (rootKey macKey hdrBytes : List (BitVec 8))
    (dec : PolyDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hhdr : hdrBytes.length = 64)
    (hpc1 : s1.pc = lsmpl.base 333 + 10000#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = BitVec.ofNat 64 rootKey.length)
    (hx27_1 : s1.readReg64 .x27 = c0) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (polyDecoderAt A.repAlloc ((s0.sp - 2400#64) + 1888#64) dec ∗
        (v6hr_lowStackAt s0.sp 64#64 ep p2_new p0 d184 p1_new d200 p2
           (BitVec.ofNat 64 macKey.length) w120 ptsPtr ∗
         memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
         (memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗
          memRegion ((s0.sp - 2400#64) + 1432#64) 456 ∗
          memRegion ((s0.sp - 2400#64) + 2288#64) 16)) ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
        vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
        vecU8Payload A.repAlloc c0 p0 hdrBytes ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out
            (.ok (.headerReceived
              { uc := { epoch := ep, auth := { rootKey := rootKey, macKey := macKey }, hdr := hdrBytes },
                receiving_ek := dec })) ∗
          (A.pool lim st sf ∗ Rest) ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v6hr_step_10000_ok_to_exit_of_placedHooks (F := F) hA.toPlacedBudget st s0 s1
    out c0 p0 p1_new p2_new ep p2 w120 ptsPtr d184 d200 rootKey macKey hdrBytes dec Rest
    hsp0_align hhdr hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 hx27_1 htr1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6fPlacedBudgetAux
