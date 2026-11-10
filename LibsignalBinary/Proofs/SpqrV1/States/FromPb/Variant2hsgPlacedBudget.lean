/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsaPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb0PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsbPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsgPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 2 (`HeaderSent`) — Part G

Relocatable Block-`333` `FreeOnlyEvs` error-branch exits (`+9152`, `+3348`) and allocator
event envelopes for the `+9036 -> ret` continuation under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsgPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1
  (PolyEncoder PolynomialDecoder PolynomialEncoder ProtoAuthenticator ProtoPolynomialDecoder
   ProtoPolynomialEncoder States V1State pbToProtoPolyDecoder pbToProtoPolyEncoder spqrAuthApi
   spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize optProtoInnerStateSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack fromPbResult)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved optEncoderPtsBound resultChunkedStatesAt sp_sub_2400_align spqrErrorByte
   stackAt_encoderFromPb_split_allocHook statesFromPbJumpTablePlacedAt statesFromPbOnPanic
   statesFromPbSavedCells statesFromPbStack v1_bv_add_add_lit v1_bv_sub_sub_lit
   v1_optProtoAuthHeap v1_optProtoPolyEncoderHeap v1_optProtoPolyEncoderWordsAt
   v2hs_ekSentWordsAt v2hs_optProtoDecoderHeap v2hs_optProtoDecoderWordsAt
   v2hs_stack896ScratchRest v2hs_ucWordsAt v2hsc_optProtoPolyDecoderHeap
   v2hsc_optProtoPolyDecoderWordsAt v2hstop_collapse_2304_from_9228
   v2hstop_collapse_976_from_err_uc v2hstop_optProtoDecoderHeap_eq_v2hsc
   v2hstop_optProtoDecoderWordsAt_eq_v2hsc v2hstop_pbEncTailAt
   v2hstop_vecU8Heap_entails_dealloc v4b_vecU8Heap)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload vecU8Payload_entails_dealloc)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved
   fitsEvents_append rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
  (FromPbDecAllocEnv FromPbDecEnv fromPbDecAllocEnv_imp_fromPbDecEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
  (EncoderFromPbAllocEnv EncoderFromPbEnv encoderFromPbAllocEnv_imp_encoderFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2 (seq_clean_evs)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (FromPbAllocHooksBudget seq_clean_evs_lscl seq_clean_lscl_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsaPlacedBudget
  (v2hs_err_cleanup_9228_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb0PlacedBudget
  (v2hs_epilogue_4396_ret_placed v2hs_err_uc_4660_to_4396_placed v2hs_err_uc_4720_to_4396_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsbPlacedBudgetAux
  (v2hs_validate_err_auth_3348_to_4720_placed_budget
   v2hs_validate_err_dk_3348_to_4660_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlacedBudget
  (v2hsc_cleanup_9152_to_9212_of_sub_placed v2hsc_cleanup_9212_to_9228_of_sub_placed
   v2hsc_sub_ok_dealloc_of_dealloc_placed v2hsc_sub_ok_dealloc_of_placedHooks
   v2hsc_sub_ok_dealloc_placed)

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit

/-! ## Error Branch Helpers (`+9152 -> s0.x30`, `+3348 (bad dk) -> s0.x30`, `+3348 (auth none) -> s0.x30`) -/

/-- Budget-threaded `+9152 -> s0.x30` (`sendingEk = none`) cleanup and `Err(.stateDecode)` exit
    under an explicit Block-`333` `__rust_dealloc` contract: deallocates `(u48, pa1)`,
    `(u72, pa2)`, `(u8, u16)` and `optDec` under `FreeOnlyEvs`, collapses the `2304`-byte frame,
    and returns via `v2hs_err_cleanup_9228_placed_budget`. -/
theorem v2hstop_branch_sendingEk_none_9152_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (out : BitVec 64)
    (dk : List (BitVec 8)) (auth : ProtoAuthenticator)
    (u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hu48 : u48 = BitVec.ofNat 64 auth.rootKey.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 9152#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx0 : s.readReg64 .x0 = pa2) (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = d_w0) (hx25 : s.readReg64 .x25 = u48)
    (hx26 : s.readReg64 .x26 = u8) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 736 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v4b_vecU8Heap A.repAlloc dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        memRegion (s0.sp - 2400#64 + 1344#64) 960 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hd_dk := v2hstop_vecU8Heap_entails_dealloc A.repAlloc dk u8 u16 u24
  have hd_r : vecU8Payload A.repAlloc u48 pa1 auth.rootKey ⊢ vecCapPtrDealloc A.repAlloc u48 pa1 := by
    rw [hu48]; exact vecU8Payload_entails_dealloc A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey
  have hd_m : vecU8Payload A.repAlloc u72 pa2 auth.macKey ⊢ vecCapPtrDealloc A.repAlloc u72 pa2 := by
    rw [hu72]; exact vecU8Payload_entails_dealloc A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey
  have hek_split :
      v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 =
      ((fsp + 1272#64) ↦₆₄ pa1) ∗
      (((fsp + 1264#64) ↦₆₄ u48) ∗ ((fsp + 1280#64) ↦₆₄ u48) ∗ ((fsp + 1288#64) ↦₆₄ u72) ∗
       ((fsp + 1296#64) ↦₆₄ pa2) ∗ ((fsp + 1304#64) ↦₆₄ u72) ∗ ((fsp + 1312#64) ↦₆₄ u8) ∗
       ((fsp + 1320#64) ↦₆₄ u16) ∗ ((fsp + 1328#64) ↦₆₄ u24) ∗ ((fsp + 1336#64) ↦₆₄ u80)) := by
    dsimp +zetaDelta only [v2hs_ekSentWordsAt, fsp]; simp only [arm64_norm]; sep_ac_rfl
  let EkRest : SepProp :=
    ((fsp + 1264#64) ↦₆₄ u48) ∗ ((fsp + 1280#64) ↦₆₄ u48) ∗ ((fsp + 1288#64) ↦₆₄ u72) ∗
    ((fsp + 1296#64) ↦₆₄ pa2) ∗ ((fsp + 1304#64) ↦₆₄ u72) ∗ ((fsp + 1312#64) ↦₆₄ u8) ∗
    ((fsp + 1320#64) ↦₆₄ u16) ∗ ((fsp + 1328#64) ↦₆₄ u24) ∗ ((fsp + 1336#64) ↦₆₄ u80)
  let Frame9152 : SepProp :=
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗
    ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗ memRegion (fsp + 240#64) 736 ∗
    v2hs_stack896ScratchRest fsp ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 192 ∗ EkRest ∗ memRegion (fsp + 1344#64) 960 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre9152 :
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
        ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
        v2hs_stack896ScratchRest fsp ∗ v4b_vecU8Heap A.repAlloc dk u8 u16 u24 ∗
        vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        memRegion (fsp + 1344#64) 960 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s ∗ Rest) ⊢
      stackAt fsp encoderFromPbStack ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        vecCapPtrDealloc A.repAlloc u48 pa1 ∗ vecCapPtrDealloc A.repAlloc u72 pa2 ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗ A.pool lim st s ∗ Frame9152 := by
    rw [hek_split]; dsimp +zetaDelta only [Frame9152, EkRest]
    refine Entails.trans (Entails.of_eq (show _ =
      vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
      v4b_vecU8Heap A.repAlloc dk u8 u16 u24 ∗
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗ A.pool lim st s ∗
       (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗
        ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗ memRegion (fsp + 240#64) 736 ∗
        v2hs_stack896ScratchRest fsp ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        (((fsp + 1264#64) ↦₆₄ u48) ∗ ((fsp + 1280#64) ↦₆₄ u48) ∗ ((fsp + 1288#64) ↦₆₄ u72) ∗
         ((fsp + 1296#64) ↦₆₄ pa2) ∗ ((fsp + 1304#64) ↦₆₄ u72) ∗ ((fsp + 1312#64) ↦₆₄ u8) ∗
         ((fsp + 1320#64) ↦₆₄ u16) ∗ ((fsp + 1328#64) ↦₆₄ u24) ∗ ((fsp + 1336#64) ↦₆₄ u80)) ∗
        memRegion (fsp + 1344#64) 960 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hd_r (sepConj_mono hd_m (sepConj_mono_left hd_dk)))
      (Entails.of_eq (by sep_ac_rfl))
  refine SepWP.weaken_pre hpre9152 ?_
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 9212#64)
    (P_evs := fun evs1 sm =>
      stackAt fsp encoderFromPbStack ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ Frame9152)
    (Q := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
      s1.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved s1 s0)
    (v2hsc_cleanup_9152_to_9212_of_sub_placed hdealloc_ok s0 s fsp out d_w0
      u48 pa1 u72 pa2 u8 u16 st Frame9152
      hfsp_align hpc hrun hsp hx0 hx19 hx22 hx25 hx26 htr) ?_
  intro evs1 s1 hevs1 hpc1 hrun1 ⟨hsp1, hx19_1, hx22_1, htr1⟩
  let Frame9212 : SepProp :=
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
    ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
    ((fsp + 224#64) ↦₆₄ u80) ∗ memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion (fsp + 1072#64) 192 ∗
    v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
    memRegion (fsp + 1344#64) 960 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre9212 :
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 1272#64) ↦₆₄ pa1) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
        A.pool lim (M.stepEvents evs1 st) s1 ∗ Frame9152) =
      (stackAt fsp encoderFromPbStack ∗
        v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        v2hsc_optProtoPolyDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗
        A.pool lim (M.stepEvents evs1 st) s1 ∗ Frame9212) := by
    dsimp +zetaDelta only [Frame9152, Frame9212, EkRest]
    rw [hek_split,
        v2hstop_optProtoDecoderWordsAt_eq_v2hsc (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32,
        v2hstop_optProtoDecoderHeap_eq_v2hsc A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32]
    sep_ac_rfl
  refine SepWP.weaken_pre (Entails.of_eq hpre9212) ?_
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 9228#64)
    (P_evs := fun evs2 sm =>
      stackAt fsp encoderFromPbStack ∗
      v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
        (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
      ((fsp + 232#64) ↦₆₄ u72) ∗
      A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) sm ∗ Frame9212)
    (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
      s2.readReg64 .x23 = 0#64 ∧ TraceCalleeSaved s2 s0)
    (v2hsc_cleanup_9212_to_9228_of_sub_placed hdealloc_ok s0 s1 fsp out optDec d_w0 d_w8 d_w16
      (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 u72
      (M.stepEvents evs1 st) Frame9212
      hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1) ?_
  intro evs2 s2 hevs2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, htr2⟩
  have hcol2304 := v2hstop_collapse_2304_from_9228 fsp u8 u16 u24 u40 u48 u72 u80 pa1 pa2
    w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
  have hpre9228 :
      (stackAt fsp encoderFromPbStack ∗
        v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16
          (d_w24.extractLsb' 0 32) (d_w24.extractLsb' 32 32) d_w32 ∗
        ((fsp + 232#64) ↦₆₄ u72) ∗
        A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s2 ∗ Frame9212) ⊢
      stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        Rest ∗ A.pool lim (M.stepEvents (evs1 ++ evs2) st) s2 := by
    rw [← v2hstop_optProtoDecoderWordsAt_eq_v2hsc (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32,
        ← M.stepEvents_append evs1 evs2 st]
    dsimp +zetaDelta only [Frame9212]
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
       ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
       v2hs_stack896ScratchRest fsp ∗
       v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       memRegion (fsp + 1072#64) 192 ∗
       v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
       memRegion (fsp + 1344#64) 960) ∗
      (stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ Rest ∗
       A.pool lim (M.stepEvents (evs1 ++ evs2) st) s2) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hcol2304) (Entails.of_eq (by sep_ac_rfl))
  refine SepWP.weaken_pre hpre9228 ?_
  have hx23_lo : (s2.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx23_2]; rfl
  have h9228 := v2hs_err_cleanup_9228_placed_budget A lim (M.stepEvents (evs1 ++ evs2) st)
    (F := F) (ext := ext) s0 s2 out .stateDecode Rest
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_lo htr2
  exact SepWP.mono h9228 fun sf Pf _ _ ⟨hPf, _hvm, hspf, hcsf, htrf⟩ =>
    ⟨evs1 ++ evs2, hevs1.append hevs2,
     Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hspf, hcsf, htrf⟩

theorem v2hstop_branch_sendingEk_none_9152_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (out : BitVec 64)
    (dk : List (BitVec 8)) (auth : ProtoAuthenticator)
    (u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hu48 : u48 = BitVec.ofNat 64 auth.rootKey.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 9152#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx0 : s.readReg64 .x0 = pa2) (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = d_w0) (hx25 : s.readReg64 .x25 = u48)
    (hx26 : s.readReg64 .x26 = u8) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 736 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v4b_vecU8Heap A.repAlloc dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        memRegion (s0.sp - 2400#64 + 1344#64) 960 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v2hstop_branch_sendingEk_none_9152_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_dealloc_placed hdealloc) st s0 s out dk auth
    u8 u16 u24 u40 u48 u72 u80 pa1 pa2 w0 w8 w16 w24 w32 w40 w48
    optDec d_w0 d_w8 d_w16 d_w24 d_w32 Rest
    hu48 hu72 hsp0_align hpc hrun hsp hx0 hx19 hx22 hx25 hx26 htr

theorem v2hstop_branch_sendingEk_none_9152_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s : State) (out : BitVec 64)
    (dk : List (BitVec 8)) (auth : ProtoAuthenticator)
    (u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hu48 : u48 = BitVec.ofNat 64 auth.rootKey.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 9152#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx0 : s.readReg64 .x0 = pa2) (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = d_w0) (hx25 : s.readReg64 .x25 = u48)
    (hx26 : s.readReg64 .x26 = u8) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 736 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v4b_vecU8Heap A.repAlloc dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        memRegion (s0.sp - 2400#64 + 1344#64) 960 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v2hstop_branch_sendingEk_none_9152_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_placedHooks hA) st s0 s out dk auth
    u8 u16 u24 u40 u48 u72 u80 pa1 pa2 w0 w8 w16 w24 w32 w40 w48
    optDec d_w0 d_w8 d_w16 d_w24 d_w32 Rest
    hu48 hu72 hsp0_align hpc hrun hsp hx0 hx19 hx22 hx25 hx26 htr

theorem v2hstop_branch_sendingEk_none_9152_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (out : BitVec 64)
    (dk : List (BitVec 8)) (auth : ProtoAuthenticator)
    (u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hu48 : u48 = BitVec.ofNat 64 auth.rootKey.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.macKey.length)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 9152#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx0 : s.readReg64 .x0 = pa2) (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = d_w0) (hx25 : s.readReg64 .x25 = u48)
    (hx26 : s.readReg64 .x26 = u8) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 736 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v4b_vecU8Heap A.repAlloc dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        memRegion (s0.sp - 2400#64 + 1344#64) 960 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v2hstop_branch_sendingEk_none_9152_of_sub_placed
    (v2hsc_sub_ok_dealloc_placed hA) st s0 s out dk auth
    u8 u16 u24 u40 u48 u72 u80 pa1 pa2 w0 w8 w16 w24 w32 w40 w48
    optDec d_w0 d_w8 d_w16 d_w24 d_w32 Rest
    hu48 hu72 hsp0_align hpc hrun hsp hx0 hx19 hx22 hx25 hx26 htr

/-- Budget-threaded `+3348 (u24 != 2400) -> +4660 -> +4396 -> s0.x30` cleanup and
    `Err(.stateDecode)` exit for Variant 2 (`HeaderSent`) when `u.dk.length != 2400`. -/
theorem v2hstop_branch_bad_dk_3348_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (out : BitVec 64)
    (u : V1State.Unchunked.EkSent)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (w96 w152 w176 w184 w200 w216 w224 w232 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63) (hdk : (u24 == 2400#64) = false)
    (hpc : s.pc = lsmpl.base 333 + 3348#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ w96) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ w176) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ w184) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ w216) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ w224) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 656 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗
        v1_optProtoAuthHeap A.repAlloc u.auth u32 u40 u48 u56 u64 u72 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hd_dk := v2hstop_vecU8Heap_entails_dealloc A.repAlloc u.dk u8 u16 u24
  let Rest3348 : SepProp :=
    stackAt fsp encoderFromPbStack ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
    ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
    ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
    vecCapPtrDealloc A.repAlloc u8 u16 ∗
    v1_optProtoAuthHeap A.repAlloc u.auth u32 u40 u48 u56 u64 u72 ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre3348 :
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
        ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
        ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
        memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗
        v1_optProtoAuthHeap A.repAlloc u.auth u32 u40 u48 u56 u64 u72 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s ∗ Rest) ⊢
      ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        Rest3348 ∗ A.pool lim st s := by
    dsimp +zetaDelta only [Rest3348]
    refine Entails.trans (Entails.of_eq (show _ =
      v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗
      (((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
       v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
       stackAt fsp encoderFromPbStack ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
       ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
       ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
       v1_optProtoAuthHeap A.repAlloc u.auth u32 u40 u48 u56 u64 u72 ∗
       v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
       v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       memRegion (fsp + 1072#64) 1232 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest ∗ A.pool lim st s) by
      sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hd_dk) (Entails.of_eq (by sep_ac_rfl))
  refine SepWP.weaken_pre hpre3348 ?_
  refine seq_clean_lscl_st hcl
    (mid := lsmpl.base 333 + 4660#64)
    (P_mid := fun sm => ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
      v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
      Rest3348 ∗ A.pool lim st sm)
    (Q := fun s1 => VmPreserved s s1 ∧ s1.sp = fsp ∧ s1.readReg64 .x0 = u40 ∧
      s1.readReg64 .x9 = u16 ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x22 = d_w0 ∧
      s1.readReg64 .x24 = u56 ∧ s1.readReg64 .x25 = u64 ∧
      s1.readReg64 .x26 = u32 ∧ TraceCalleeSaved s1 s0)
    (v2hs_validate_err_dk_3348_to_4660_placed_budget A lim st (ext := ext) s0 s out d_w0
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 w96 w152 Rest3348
      hsp0_align hu8 hdk hpc hrun hsp hx19 hx22 htr) ?_
  intro s1 hpc1 hrun1 hcl1 ⟨_hvm1, hsp1, hx0_1, hx9_1, hx19_1, hx22_1, hx24_1, hx25_1, hx26_1, htr1⟩
  let Frame4660 : SepProp :=
    memRegion (fsp - 5152#64) 1056 ∗ ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
    ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
    memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
    v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre4660 :
      (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        Rest3348 ∗ A.pool lim st s1) =
      (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗
        v1_optProtoAuthHeap A.repAlloc u.auth u32 u40 u48 u56 u64 u72 ∗
        A.pool lim st s1 ∗ stackAt fsp allocHookStack ∗ Frame4660) := by
    dsimp +zetaDelta only [Rest3348, Frame4660]
    rw [stackAt_encoderFromPb_split_allocHook fsp]; sep_ac_rfl
  refine SepWP.weaken_pre (Entails.of_eq hpre4660) ?_
  refine seq_clean_evs_lscl hcl1
    (mid := lsmpl.base 333 + 4396#64)
    (P_evs := fun evs1 sm =>
      ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame4660)
    (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x22 = d_w0 ∧
      s2.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64 ∧ TraceCalleeSaved s2 s0)
    (v2hs_err_uc_4660_to_4396_placed hA st s0 s1 fsp out u8 u16 u32 u40 u48 u56 u64 u72
      w176 w200 d_w0 u.auth Frame4660
      hfsp_align hpc1 hrun1 hsp1 hx0_1 hx9_1 hx19_1 hx22_1 hx24_1 hx25_1 hx26_1 htr1) ?_
  intro evs1 s2 hevs1 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx22_2, hx23_2, htr2⟩
  have hcol976 := v2hstop_collapse_976_from_err_uc fsp u24 u8 w184 w216 w224 w232
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
  have hpre4396 :
      (((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
        A.pool lim (M.stepEvents evs1 st) s2 ∗ stackAt fsp allocHookStack ∗ Frame4660) ⊢
      stackAt fsp encoderFromPbStack ∗ memRegion fsp 976 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        A.pool lim (M.stepEvents evs1 st) s2 ∗ Rest := by
    have hre :
        (((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
          A.pool lim (M.stepEvents evs1 st) s2 ∗ stackAt fsp allocHookStack ∗ Frame4660) =
        (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗
         ((fsp + 184#64) ↦₆₄ w184) ∗ memRegion (fsp + 200#64) 8 ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
         ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗
         v2hs_stack896ScratchRest fsp ∗
         v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80) ∗
        ((memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack) ∗
         v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
         v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (fsp + 1072#64) 1232 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         A.pool lim (M.stepEvents evs1 st) s2 ∗ Rest) := by
      dsimp +zetaDelta only [Frame4660]; sep_ac_rfl
    rw [← stackAt_encoderFromPb_split_allocHook fsp] at hre
    exact Entails.trans (Entails.of_eq hre)
      (Entails.trans (sepConj_mono_left hcol976) (Entails.of_eq (by sep_ac_rfl)))
  refine SepWP.weaken_pre hpre4396 ?_
  have hep := v2hs_epilogue_4396_ret_placed (F := F) hA (M.stepEvents evs1 st)
    s0 s2 out .stateDecode optEnc w0 w8 w16 w24 w32 w40 w48
    optDec d_w0 d_w8 d_w16 d_w24 d_w32 Rest
    hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx23_2 htr2
  refine SepWP.mono hep fun sf Pf _ _ ⟨evs2, hevs2, hPf, hspf, hcsf, htrf⟩ => ?_
  refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hspf, hcsf, htrf⟩
  rw [M.stepEvents_append]
  exact hPf

/-- Budget-threaded `+3348 (auth = none) -> +4720 -> +4396 -> s0.x30` cleanup and
    `Err(.stateDecode)` exit for Variant 2 (`HeaderSent`) when `u.auth = none`. -/
theorem v2hstop_branch_auth_none_3348_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (out : BitVec 64)
    (dk : List (BitVec 8))
    (u8 u16 u24 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (w96 w152 w176 w184 w200 w216 w224 w232 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63) (hdk : (u24 == 2400#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 3348#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ w96) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ w176) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ w184) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ w216) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ w224) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 656 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗
        v4b_vecU8Heap A.repAlloc dk u8 u16 u24 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hd_dk := v2hstop_vecU8Heap_entails_dealloc A.repAlloc dk u8 u16 u24
  let Rest3348 : SepProp :=
    stackAt fsp encoderFromPbStack ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
    ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
    ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
    vecCapPtrDealloc A.repAlloc u8 u16 ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre3348 :
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
        ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
        ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
        memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗
        v4b_vecU8Heap A.repAlloc dk u8 u16 u24 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s ∗ Rest) ⊢
      ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗
        Rest3348 ∗ A.pool lim st s := by
    dsimp +zetaDelta only [Rest3348]
    refine Entails.trans (Entails.of_eq (show _ =
      v4b_vecU8Heap A.repAlloc dk u8 u16 u24 ∗
      (((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
       v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗
       stackAt fsp encoderFromPbStack ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
       ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
       ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
       v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
       v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       memRegion (fsp + 1072#64) 1232 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest ∗ A.pool lim st s) by
      sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hd_dk) (Entails.of_eq (by sep_ac_rfl))
  refine SepWP.weaken_pre hpre3348 ?_
  refine seq_clean_lscl_st hcl
    (mid := lsmpl.base 333 + 4720#64)
    (P_mid := fun sm => ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
      v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗
      Rest3348 ∗ A.pool lim st sm)
    (Q := fun s1 => VmPreserved s s1 ∧ s1.sp = fsp ∧ s1.readReg64 .x9 = u16 ∧
      s1.readReg64 .x19 = out ∧ s1.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved s1 s0)
    (v2hs_validate_err_auth_3348_to_4720_placed_budget A lim st (ext := ext) s0 s out d_w0
      u8 u16 u24 u40 u48 u56 u64 u72 u80 w96 w152 Rest3348
      hsp0_align hu8 hdk hpc hrun hsp hx19 hx22 htr) ?_
  intro s1 hpc1 hrun1 hcl1 ⟨_hvm1, hsp1, hx9_1, hx19_1, hx22_1, htr1⟩
  let Frame4720 : SepProp :=
    memRegion (fsp - 5152#64) 1056 ∗ ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
    ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
    memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
    v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre4720 :
      (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗
        Rest3348 ∗ A.pool lim st s1) =
      (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗ A.pool lim st s1 ∗
        stackAt fsp allocHookStack ∗ Frame4720) := by
    dsimp +zetaDelta only [Rest3348, Frame4720]
    rw [stackAt_encoderFromPb_split_allocHook fsp]; sep_ac_rfl
  refine SepWP.weaken_pre (Entails.of_eq hpre4720) ?_
  refine seq_clean_evs_lscl hcl1
    (mid := lsmpl.base 333 + 4396#64)
    (P_evs := fun evs1 sm =>
      ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame4720)
    (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x22 = d_w0 ∧
      s2.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64 ∧ TraceCalleeSaved s2 s0)
    (v2hs_err_uc_4720_to_4396_placed hA st s0 s1 fsp out u8 u16 w176 w200 d_w0
      Frame4720 hfsp_align hpc1 hrun1 hsp1 hx9_1 hx19_1 hx22_1 htr1) ?_
  intro evs1 s2 hevs1 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx22_2, hx23_2, htr2⟩
  have hcol976 := v2hstop_collapse_976_from_err_uc fsp u24 u8 w184 w216 w224 w232
    u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80
  have hpre4396 :
      (((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
        A.pool lim (M.stepEvents evs1 st) s2 ∗ stackAt fsp allocHookStack ∗ Frame4720) ⊢
      stackAt fsp encoderFromPbStack ∗ memRegion fsp 976 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        A.pool lim (M.stepEvents evs1 st) s2 ∗ Rest := by
    have hre :
        (((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
          A.pool lim (M.stepEvents evs1 st) s2 ∗ stackAt fsp allocHookStack ∗ Frame4720) =
        (((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗
         ((fsp + 184#64) ↦₆₄ w184) ∗ memRegion (fsp + 200#64) 8 ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
         ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗
         v2hs_stack896ScratchRest fsp ∗
         v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80) ∗
        ((memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack) ∗
         v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
         v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (fsp + 1072#64) 1232 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         A.pool lim (M.stepEvents evs1 st) s2 ∗ Rest) := by
      dsimp +zetaDelta only [Frame4720]; sep_ac_rfl
    rw [← stackAt_encoderFromPb_split_allocHook fsp] at hre
    exact Entails.trans (Entails.of_eq hre)
      (Entails.trans (sepConj_mono_left hcol976) (Entails.of_eq (by sep_ac_rfl)))
  refine SepWP.weaken_pre hpre4396 ?_
  have hep := v2hs_epilogue_4396_ret_placed (F := F) hA (M.stepEvents evs1 st)
    s0 s2 out .stateDecode optEnc w0 w8 w16 w24 w32 w40 w48
    optDec d_w0 d_w8 d_w16 d_w24 d_w32 Rest
    hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx23_2 htr2
  refine SepWP.mono hep fun sf Pf _ _ ⟨evs2, hevs2, hPf, hspf, hcsf, htrf⟩ => ?_
  refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hspf, hcsf, htrf⟩
  rw [M.stepEvents_append]
  exact hPf

/-! ## `+9036 -> s0.x30` Continuation Envelope & Interface Hypothesis -/

/-- `EncoderFromPbEnv` is closed under appending trailing `FreeOnlyEvs` drops. -/
theorem encoderFromPbEnv_append_freeOnly {pb : ProtoPolynomialEncoder}
    {evs1 evs2 : List AllocEvent}
    (h1 : EncoderFromPbEnv pb evs1) (h2 : FreeOnlyEvs evs2) :
    EncoderFromPbEnv pb (evs1 ++ evs2) := by
  rcases h1 with ⟨ea, ef, rfl, ha, hf⟩
  exact ⟨ea, ef ++ evs2, List.append_assoc ea ef evs2, ha, hf.append h2⟩

/-- `FromPbDecEnv` is closed under appending trailing `FreeOnlyEvs` drops. -/
theorem fromPbDecEnv_append_freeOnly {pb : ProtoPolynomialDecoder}
    {evs1 evs2 : List AllocEvent}
    (h1 : FromPbDecEnv pb evs1) (h2 : FreeOnlyEvs evs2) :
    FromPbDecEnv pb (evs1 ++ evs2) := by
  rcases h1 with ⟨ea, ef, rfl, ha, hf⟩
  exact ⟨ea, ef ++ evs2, List.append_assoc ea ef evs2, ha, hf.append h2⟩

/-- Complete binary allocator event envelope for the `+9036 -> s0.x30` (`sendingEk = some pbEnc`)
    continuation of Variant 2 (`HeaderSent`) in `<States>::from_pb`:
    - when `<PolyEncoder>::from_pb` returns `.error _` (or `s.receivingCt1 = none`),
      `EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc)` (including trailing `FreeOnlyEvs` drops);
    - when `<PolyEncoder>::from_pb` returns `.ok _` and `s.receivingCt1 = some pbDec`,
      either an early drop path (`EncoderFromPbEnv`) or `EncoderFromPbEnv` followed by
      `FromPbDecEnv (pbToProtoPolyDecoder pbDec)` (including trailing `FreeOnlyEvs` drops). -/
def HeaderSentSomeEnc9036Env (s : V1State.Chunked.HeaderSent) (pbEnc : PolynomialEncoder)
    (evs : List AllocEvent) : Prop :=
  match fromPbResult (pbToProtoPolyEncoder pbEnc) with
  | .error _ => EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs
  | .ok _ =>
    match s.receivingCt1 with
    | none => EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs
    | some pbDec =>
      EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs ∨
        ∃ evs1 evs2,
          evs = evs1 ++ evs2 ∧
          EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs1 ∧
          FromPbDecEnv (pbToProtoPolyDecoder pbDec) evs2

/-- Option-lifted `+9036 -> s0.x30` envelope indexed only by `s : V1State.Chunked.HeaderSent`
    (so callers before unpacking `s.sendingEk` can pass a single `List AllocEvent → Prop`). -/
def HeaderSentSomeEncOptEnv (s : V1State.Chunked.HeaderSent) (evs : List AllocEvent) : Prop :=
  match s.sendingEk with
  | none => evs = []
  | some pbEnc => HeaderSentSomeEnc9036Env s pbEnc evs

theorem encoderFromPbEnv_imp_headerSentSomeEnc9036Env
    {s : V1State.Chunked.HeaderSent} {pbEnc : PolynomialEncoder} {evs : List AllocEvent}
    (h : EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs) :
    HeaderSentSomeEnc9036Env s pbEnc evs := by
  unfold HeaderSentSomeEnc9036Env
  cases fromPbResult (pbToProtoPolyEncoder pbEnc) with
  | error _ => exact h
  | ok _ =>
    cases s.receivingCt1 with
    | none => exact h
    | some _ => exact Or.inl h

theorem headerSentSomeEnc9036Env_append_freeOnly
    {s : V1State.Chunked.HeaderSent} {pbEnc : PolynomialEncoder}
    {evs evs_free : List AllocEvent}
    (h : HeaderSentSomeEnc9036Env s pbEnc evs) (hfree : FreeOnlyEvs evs_free) :
    HeaderSentSomeEnc9036Env s pbEnc (evs ++ evs_free) := by
  unfold HeaderSentSomeEnc9036Env at h ⊢
  revert h
  cases fromPbResult (pbToProtoPolyEncoder pbEnc) with
  | error _ =>
    intro h
    exact encoderFromPbEnv_append_freeOnly h hfree
  | ok _ =>
    cases s.receivingCt1 with
    | none =>
      intro h
      exact encoderFromPbEnv_append_freeOnly h hfree
    | some pbDec =>
      rintro (h1 | ⟨evs1, evs2, rfl, h1, h2⟩)
      · exact Or.inl (encoderFromPbEnv_append_freeOnly h1 hfree)
      · exact Or.inr ⟨evs1, evs2 ++ evs_free, List.append_assoc evs1 evs2 evs_free,
          h1, fromPbDecEnv_append_freeOnly h2 hfree⟩

theorem headerSentSomeEnc9036Env_of_some_dec
    {s : V1State.Chunked.HeaderSent} {pbEnc : PolynomialEncoder}
    {enc : CryptoVerification.LibsignalSpqrV1.PolyEncoder}
    {pbDec : CryptoVerification.LibsignalSpqrV1.PolynomialDecoder}
    {evs1 evs2 : List AllocEvent}
    (hres : fromPbResult (pbToProtoPolyEncoder pbEnc) = .ok enc)
    (hdec : s.receivingCt1 = some pbDec)
    (h1 : EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs1)
    (h2 : FromPbDecEnv (pbToProtoPolyDecoder pbDec) evs2) :
    HeaderSentSomeEnc9036Env s pbEnc (evs1 ++ evs2) := by
  unfold HeaderSentSomeEnc9036Env
  rw [hres, hdec]
  exact Or.inr ⟨evs1, evs2, rfl, h1, h2⟩

theorem headerSentSomeEncOptEnv_of_some
    {s : V1State.Chunked.HeaderSent} {pbEnc : PolynomialEncoder} {evs : List AllocEvent}
    (henc : s.sendingEk = some pbEnc) (h : HeaderSentSomeEnc9036Env s pbEnc evs) :
    HeaderSentSomeEncOptEnv s evs := by
  unfold HeaderSentSomeEncOptEnv
  rw [henc]
  exact h

/-- `FitsEnv` projection for the `<PolyEncoder>::from_pb` call (`+9080`) at entry to `+9036`. -/
theorem fitsEnv_encoderAlloc_of_headerSentSomeEnc9036Env
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {s : V1State.Chunked.HeaderSent} {pbEnc : PolynomialEncoder}
    (h : FitsEnv M lim st (HeaderSentSomeEnc9036Env s pbEnc)) :
    FitsEnv M lim st (EncoderFromPbAllocEnv (pbToProtoPolyEncoder pbEnc)) :=
  fun evs hevs =>
    h evs (encoderFromPbEnv_imp_headerSentSomeEnc9036Env
      (encoderFromPbAllocEnv_imp_encoderFromPbEnv hevs))

/-- `FitsEnv` projection for the `<PolyDecoder>::from_pb` call (`+9384`) after `<PolyEncoder>::from_pb`
    succeeds with `evs1` satisfying `EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs1`. -/
theorem fitsEnv_decoderAlloc_of_headerSentSomeEnc9036Env
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {s : V1State.Chunked.HeaderSent} {pbEnc : PolynomialEncoder}
    {enc : CryptoVerification.LibsignalSpqrV1.PolyEncoder}
    {pbDec : CryptoVerification.LibsignalSpqrV1.PolynomialDecoder}
    {evs1 : List AllocEvent}
    (hres : fromPbResult (pbToProtoPolyEncoder pbEnc) = .ok enc)
    (hdec : s.receivingCt1 = some pbDec)
    (hfits : FitsEnv M lim st (HeaderSentSomeEnc9036Env s pbEnc))
    (hevs1 : EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs1) :
    FitsEnv M lim (M.stepEvents evs1 st) (FromPbDecAllocEnv (pbToProtoPolyDecoder pbDec)) := by
  intro evs2 hevs2
  have hmem := headerSentSomeEnc9036Env_of_some_dec hres hdec hevs1
    (fromPbDecAllocEnv_imp_fromPbDecEnv hevs2)
  exact ((fitsEvents_append M lim evs1 evs2 st).mp (hfits (evs1 ++ evs2) hmem)).2

/-- Envelope-parametric pure-`SepWP` interface hypothesis for the `+9036 -> s0.x30`
    (`sendingEk = some pbEnc`) continuation of Variant 2 (`HeaderSent`) under
    `RustCliAllocBudget M`. -/
def v2hstop_SomeEnc9036SepWPHypPlacedOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (ext : String → Option (State → State))
    (s : V1State.Chunked.HeaderSent) (Env : List AllocEvent → Prop) : Prop :=
  ∀ (st : M.σ) (s0 sm : State) (out pbA : BitVec 64)
    (u : V1State.Unchunked.EkSent) (auth : ProtoAuthenticator) (pbEnc : PolynomialEncoder)
    (u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64),
    LibsignalCodeLoaded lsmpl sm.mem →
    optEncoderPtsBound s.sendingEk →
    (match s.receivingCt1 with | none => True | some d => (d.ptsNeeded == 480#32) = true) →
    FitsEnv M lim st (HeaderSentSomeEnc9036Env s pbEnc) →
    s.uc = some u → u.dk.length = 2400 → u.auth = some auth → s.sendingEk = some pbEnc →
    u8.toNat < 2 ^ 63 → u24 = 2400#64 → u48 = BitVec.ofNat 64 auth.rootKey.length →
    u72 = BitVec.ofNat 64 auth.macKey.length → u80 = u.epoch → auth.rootKey.length < 2 ^ 63 →
    (s0.sp &&& 15#64 == 0#64) = true →
    sm.pc = lsmpl.base 333 + 9036#64 →
    sm.status = .Running → sm.sp = s0.sp - 2400#64 →
    sm.readReg64 .x0 = pa2 → sm.readReg64 .x8 = w0 → sm.readReg64 .x9 = u24 →
    sm.readReg64 .x10 = (s0.sp - 2400#64) + 1264#64 → sm.readReg64 .x19 = out →
    sm.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 →
    sm.readReg64 .x22 = d_w0 → sm.readReg64 .x23 = pa1 → sm.readReg64 .x25 = u48 →
    sm.readReg64 .x26 = u8 → sm.readReg64 .x27 = pbA → sm.readReg64 .x28 = u80 →
    TraceCalleeSaved sm s0 →
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) sm
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 736 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        memRegion (s0.sp - 2400#64 + 1344#64) 960 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTablePlacedAt ∗
        A.pool lim st sm)
      (fun sf Pf =>
        (∃ evs : List AllocEvent, Env evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerSent s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)

/-- Concrete pure-`SepWP` `+9036 -> s0.x30` continuation hypothesis specialized to
    `HeaderSentSomeEncOptEnv s`. -/
abbrev v2hstop_SomeEnc9036SepWPHypPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (ext : String → Option (State → State))
    (s : V1State.Chunked.HeaderSent) : Prop :=
  v2hstop_SomeEnc9036SepWPHypPlacedOfEnv M A lim F ext s (HeaderSentSomeEncOptEnv s)

/-- Envelope-parametric `SepWPp` interface hypothesis for the `+9036 -> s0.x30`
    (`sendingEk = some pbEnc`) continuation of Variant 2 (`HeaderSent`) under
    `RustCliAllocBudget M`. -/
def v2hstop_SomeEnc9036HypPlacedOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (ext : String → Option (State → State))
    (s : V1State.Chunked.HeaderSent) (Env : List AllocEvent → Prop) : Prop :=
  ∀ (st : M.σ) (s0 sm : State) (out pbA : BitVec 64) (R : SepProp)
    (u : V1State.Unchunked.EkSent) (auth : ProtoAuthenticator) (pbEnc : PolynomialEncoder)
    (u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64),
    LibsignalCodeLoaded lsmpl sm.mem →
    optEncoderPtsBound s.sendingEk →
    (match s.receivingCt1 with | none => True | some d => (d.ptsNeeded == 480#32) = true) →
    FitsEnv M lim st (HeaderSentSomeEnc9036Env s pbEnc) →
    s.uc = some u → u.dk.length = 2400 → u.auth = some auth → s.sendingEk = some pbEnc →
    u8.toNat < 2 ^ 63 → u24 = 2400#64 → u48 = BitVec.ofNat 64 auth.rootKey.length →
    u72 = BitVec.ofNat 64 auth.macKey.length → u80 = u.epoch → auth.rootKey.length < 2 ^ 63 →
    (s0.sp &&& 15#64 == 0#64) = true →
    sm.pc = lsmpl.base 333 + 9036#64 →
    sm.status = .Running → sm.sp = s0.sp - 2400#64 →
    sm.readReg64 .x0 = pa2 → sm.readReg64 .x8 = w0 → sm.readReg64 .x9 = u24 →
    sm.readReg64 .x10 = (s0.sp - 2400#64) + 1264#64 → sm.readReg64 .x19 = out →
    sm.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 →
    sm.readReg64 .x22 = d_w0 → sm.readReg64 .x23 = pa1 → sm.readReg64 .x25 = u48 →
    sm.readReg64 .x26 = u8 → sm.readReg64 .x27 = pbA → sm.readReg64 .x28 = u80 →
    TraceCalleeSaved sm s0 →
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) sm
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 736 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        memRegion (s0.sp - 2400#64 + 1344#64) 960 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTablePlacedAt ∗
        A.pool lim st sm)
      (fun sf Pf =>
        (∃ evs : List AllocEvent, Env evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerSent s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))

/-- Concrete `SepWPp` `+9036 -> s0.x30` continuation hypothesis specialized to
    `HeaderSentSomeEncOptEnv s`. -/
abbrev v2hstop_SomeEnc9036HypPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (ext : String → Option (State → State))
    (s : V1State.Chunked.HeaderSent) : Prop :=
  v2hstop_SomeEnc9036HypPlacedOfEnv M A lim F ext s (HeaderSentSomeEncOptEnv s)

theorem v2hstop_someEnc9036HypPlacedOfEnv_of_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {s : V1State.Chunked.HeaderSent} {Env : List AllocEvent → Prop}
    (h : v2hstop_SomeEnc9036SepWPHypPlacedOfEnv M A lim F ext s Env) :
    v2hstop_SomeEnc9036HypPlacedOfEnv M A lim F ext s Env :=
  fun st s0 sm out pbA _R u auth pbEnc u8 u16 u24 u40 u48 u72 u80 pa1 pa2
      w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
      hcl hpts hdec hfits huc hdk hauth henc hu8 hu24 hu48 hu72 hu80 hrk
      hsp0 hpc hrun hsp hx0 hx8 hx9 hx10 hx19 hx21 hx22 hx23 hx25 hx26 hx27 hx28 htr =>
    SepWPp.of_sepWP_ret
      (h st s0 sm out pbA u auth pbEnc u8 u16 u24 u40 u48 u72 u80 pa1 pa2
        w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
        hcl hpts hdec hfits huc hdk hauth henc hu8 hu24 hu48 hu72 hu80 hrk
        hsp0 hpc hrun hsp hx0 hx8 hx9 hx10 hx19 hx21 hx22 hx23 hx25 hx26 hx27 hx28 htr)

/-- Post-envelope weakening for `v2hstop_SomeEnc9036SepWPHypPlacedOfEnv`. -/
theorem v2hstop_someEnc9036SepWPHypPlacedOfEnv_mono [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {s : V1State.Chunked.HeaderSent} {Env₁ Env₂ : List AllocEvent → Prop}
    (himp : ∀ evs, Env₁ evs → Env₂ evs)
    (h : v2hstop_SomeEnc9036SepWPHypPlacedOfEnv M A lim F ext s Env₁) :
    v2hstop_SomeEnc9036SepWPHypPlacedOfEnv M A lim F ext s Env₂ :=
  fun st s0 sm out pbA u auth pbEnc u8 u16 u24 u40 u48 u72 u80 pa1 pa2
      w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
      hcl hpts hdec hfits huc hdk hauth henc hu8 hu24 hu48 hu72 hu80 hrk
      hsp0 hpc hrun hsp hx0 hx8 hx9 hx10 hx19 hx21 hx22 hx23 hx25 hx26 hx27 hx28 htr =>
    SepWP.mono
      (h st s0 sm out pbA u auth pbEnc u8 u16 u24 u40 u48 u72 u80 pa1 pa2
        w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
        hcl hpts hdec hfits huc hdk hauth henc hu8 hu24 hu48 hu72 hu80 hrk
        hsp0 hpc hrun hsp hx0 hx8 hx9 hx10 hx19 hx21 hx22 hx23 hx25 hx26 hx27 hx28 htr)
      fun _sf _Pf _ _ ⟨⟨evs, henv, hPf⟩, hrest⟩ => ⟨⟨evs, himp evs henv, hPf⟩, hrest⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsgPlacedBudget
