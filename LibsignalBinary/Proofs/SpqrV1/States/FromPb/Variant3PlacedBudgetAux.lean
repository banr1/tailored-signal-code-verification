/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3Placed
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3cPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3dPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3d
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeBase
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeGrow
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 3 (`Ct1Received`) Envelopes and `+860` Continuation

Pure Block-`333` segment lifts (`+692`, `+784`, `+860`), allocator event envelopes, and
post-`<EkSentCt1Received>::from_pb` continuation (`+860 -> ret`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CryptoVerification (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 lsProg_333 lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (PolynomialEncoder ProtoAuthenticator ProtoPolynomialEncoder V1State pbToProtoPolyEncoder spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize optProtoInnerStateSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly (optProtoPolynomialEncoderAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb (TraceCalleeSaved resultChunkedStatesAt spqrErrorByte statesFromPbJumpTablePlacedAt statesFromPbSavedCells statesFromPbStack v1_optProtoPolyEncoderHeap v1_optProtoPolyEncoderHeap_extract_w0 v1_optProtoPolyEncoderWordsAt v1_ucWordsAt v3_collapse_1552_752_err v3_collapse_232_2072_none v3_collapse_pbA_112_224 v3_ekSentCt1ReceivedAt_eq_unchunked v3_split_1496_none v3_split_1496_some v3cr_bv_add_add_lit v3cr_ekResult_err_unpack v3cr_ekSentCt1Received_from_pb_err_eq v3cr_optProtoPolyEncoderAt_pack v3cr_states_from_pb_ct1Received_sendingEk_none_eq v3cr_states_from_pb_ct1Received_uc_err_eq v3cr_unchunkedEkSentCt1ReceivedAt_open v3cr_unchunkedEkSentCt1ReceivedHeap v3cr_unchunkedHeap_ca1_lt v3cr_unchunkedHeap_entails_dealloc)
open CryptoVerification.SpqrV1.Top.StateSize (length_le_encodeMessage length_le_encodeOptMessage optRaw rawAuth rawUcEkSentCt1Received rawUcEkSentCt1Received_le_encodeRaw sum_length_le_encodeRepeatedBytes)
open CryptoVerification.SpqrV1.Unchunked (ekSentCt1ReceivedResultAt extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget VmPreserved fitsEvents_append rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget seq_clean_lscl_st)

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3PlacedBudgetAux

open scoped CryptoVerification.RustHeap
open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk (EkSentCt1Received)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget (authFromPbEvents authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
  (EncoderFromPbAllocEnv EncoderFromPbEnv encoderFromPbAllocEnv_imp_encoderFromPbEnv
   encoderFromPbPolysInitEvents encoderFromPbPolysLoopEvents encoderFromPbPolysSlotEvents
   encoderFromPbPtsLoopEvents encoderFromPbPtsSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (spqrBoundedEvs_authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget seq_clean_lscl_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3bPlacedBudget
  (v3cr_states_from_pb_err_4176_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3dPlacedBudget
  (v3_ct1Received_some_enc_924_placed_sepWP)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3dPlacedBudgetAux
  (v3_ct1Received_err_4884_to_exit_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs nonFreeCount)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
  (EkSentCt1ReceivedFromPbPostEnv EkSentCt1ReceivedFromPbPreEnv authFromPbAllocEvents
   ekSentCt1ReceivedFromPb ekSentCt1ReceivedFromPbAllocEvents)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm] v3cr_bv_add_add_lit

/-! ## `VmPreserved` & Pool-Threading Pure Block-`333` Steps (`+692`, `+784`, `+860`) -/

/-- Total-correctness (`SepWP`) call rule for a `withLsCodeLoaded` contract that also threads
    `LibsignalCodeLoaded lsmpl sf.mem` to the continuation `hnext`. -/
theorem v3_sepWP_call_lscl_cl [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    {x : α} {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    {P_step F : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_step ⊢ spec.pre x s)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post) :
    SepWP prog target_pc s (P_step ∗ F) post := by
  have hpre_cl : P_step ⊢ (withLsCodeLoaded lsmpl spec).pre x s := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl s.mem⌝]
    exact Entails.pure_right hcl hpre
  have h1 : SepWP prog ret_pc s (P_step ∗ F)
      (fun sm Pm => (Pm ⊢ spec.post x s sm ∗ F) ∧ sm.sp = s.sp ∧ CalleeSavedPreserved s sm) :=
    SepWP.call_subroutine_frame hcall (x := x) (F := F) hpc hrun hsp_align hlr
      (fun R' hm => by
        rw [sepConj_assoc] at hm
        exact Satisfies.mono (sepConj_mono_left hpre_cl) hm)
      (fun sf _ _ hm => by
        dsimp only [withLsCodeLoaded] at hm
        rw [hpan_eq] at hm
        exact not_satisfies_false_sepConj hm)
      (fun sf code _ _ hm => by
        dsimp only [withLsCodeLoaded] at hm
        rw [hexit_eq] at hm
        exact not_satisfies_false_sepConj hm)
      (fun sm hpcm hrunm hspm hcsm => SepWP.done hpcm hrunm ⟨Entails.refl _, hspm, hcsm⟩)
      (fun sf _ _ hm => by
        dsimp only [withLsCodeLoaded] at hm
        rw [hoom_eq] at hm
        exact False.elim (not_satisfies_false_sepConj hm))
  exact seq_clean_lscl_st hcl h1 fun sf hpc_f hrun_f hcl_f ⟨hsp_f, hcs_f⟩ =>
    hnext sf hpc_f hrun_f hcl_f hsp_f hcs_f

/-- `VmPreserved`-strengthened `+692 -> +4176` (`uc = none`). -/
theorem v3cr_copy_pb_692_none_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s1 : State) (fsp out pbA : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
     d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104
     e0 e8 e16 e24 e32 e40 e48 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 692#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4176#64) s1
      (v1_ucWordsAt (pbA + 8#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_ucWordsAt (fsp + 1392#64) d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) e0 e8 e16 e24 e32 e40 e48 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v1_ucWordsAt (pbA + 8#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_ucWordsAt (fsp + 1392#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = 0#64 ∧ TraceCalleeSaved sm s1) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.v3cr_copy_pb_692_none_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out pbA
      u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
      d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104
      e0 e8 e16 e24 e32 e40 e48 Rest hfsp_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx27_1))
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, hx22_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx19_m, by simpa using hx22_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v3cr_copy_pb_692_none_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)} (s1 : State) (fsp out pbA : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
     d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104
     e0 e8 e16 e24 e32 e40 e48 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 692#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4176#64) s1
      (v1_ucWordsAt (pbA + 8#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_ucWordsAt (fsp + 1392#64) d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) e0 e8 e16 e24 e32 e40 e48 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v1_ucWordsAt (pbA + 8#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_ucWordsAt (fsp + 1392#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
          A.pool lim st sm ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = 0#64 ∧ TraceCalleeSaved sm s1) := by
  have hwp := v3cr_copy_pb_692_none_placed (ext := ext) s1 fsp out pbA
    u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
    d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104
    e0 e8 e16 e24 e32 e40 e48 (A.pool lim st s1 ∗ Rest)
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx27_1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- `VmPreserved`-strengthened `+692 -> +784` (`uc = some u`). -/
theorem v3cr_copy_pb_692_some_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s1 : State) (fsp out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
     d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104
     e0 e8 e16 e24 e32 e40 e48 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hu8_lt : u8.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 692#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64) (hx27_1 : s1.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 784#64) s1
      (v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_ucWordsAt (fsp + 1392#64) d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) e0 e8 e16 e24 e32 e40 e48 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_ucWordsAt (fsp + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x8 = u8 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧ sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x29 = s1.readReg64 .x29 ∧ TraceCalleeSaved sm s1) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.v3cr_copy_pb_692_some_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out pbA
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
      d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104
      e0 e8 e16 e24 e32 e40 e48 Rest hfsp_align hu8_lt
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx23_1) (by simpa using hx25_1)
      (by simpa using hx27_1))
    fun sm Pm hvm ⟨hPm, hsp_m, hx8_m, hx19_m, hx23_m, hx25_m, hx27_m, hx29_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx8_m, by simpa using hx19_m,
       by simpa using hx23_m, by simpa using hx25_m, by simpa using hx27_m,
       by simpa using hx29_m, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v3cr_copy_pb_692_some_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)} (s1 : State) (fsp out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
     d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104
     e0 e8 e16 e24 e32 e40 e48 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hu8_lt : u8.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 692#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64) (hx27_1 : s1.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 784#64) s1
      (v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_ucWordsAt (fsp + 1392#64) d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) e0 e8 e16 e24 e32 e40 e48 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_ucWordsAt (fsp + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
          A.pool lim st sm ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x8 = u8 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧ sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x29 = s1.readReg64 .x29 ∧ TraceCalleeSaved sm s1) := by
  have hwp := v3cr_copy_pb_692_some_placed (ext := ext) s1 fsp out pbA
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 w0 w8 w16 w24 w32 w40 w48
    d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104
    e0 e8 e16 e24 e32 e40 e48 (A.pool lim st s1 ∗ Rest)
    hfsp_align hu8_lt hpc1 hrun1 hsp1 hx19_1 hx23_1 hx25_1 hx27_1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- `VmPreserved`-strengthened `+784 -> lsmpl.base 348` (`<EkSentCt1Received>::from_pb` call setup). -/
theorem v3cr_copy_uc_to_call_784_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s1 : State) (fsp out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
     d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 784#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx8_1 : s1.readReg64 .x8 = u8) (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64) (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 348) s1
      (v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        ((fsp + 1400#64) ↦₆₄ u16) ∗
        v1_ucWordsAt (fsp + 896#64) d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          ((fsp + 1400#64) ↦₆₄ u16) ∗
          v1_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = fsp + 1888#64 ∧ sm.readReg64 .x1 = fsp + 896#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧ sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x29 = s1.readReg64 .x29 ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 860#64 ∧
        TraceCalleeSaved sm s1) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.v3cr_copy_uc_to_call_784_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out pbA
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
      d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104
      Rest hfsp_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx8_1) (by simpa using hx19_1) (by simpa using hx23_1)
      (by simpa using hx25_1) (by simpa using hx27_1))
    fun sm Pm hvm ⟨hPm, hsp_m, hx0_m, hx1_m, hx19_m, hx23_m, hx25_m, hx27_m, hx29_m, hx30_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx0_m, by simpa using hx1_m,
       by simpa using hx19_m, by simpa using hx23_m, by simpa using hx25_m,
       by simpa using hx27_m, by simpa using hx29_m, by simpa using hx30_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v3cr_copy_uc_to_call_784_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)} (s1 : State) (fsp out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
     d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 784#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp)
    (hx8_1 : s1.readReg64 .x8 = u8) (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64) (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 348) s1
      (v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
        ((fsp + 1400#64) ↦₆₄ u16) ∗
        v1_ucWordsAt (fsp + 896#64) d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          ((fsp + 1400#64) ↦₆₄ u16) ∗
          v1_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
          A.pool lim st sm ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = fsp + 1888#64 ∧ sm.readReg64 .x1 = fsp + 896#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧ sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x29 = s1.readReg64 .x29 ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 860#64 ∧
        TraceCalleeSaved sm s1) := by
  have hwp := v3cr_copy_uc_to_call_784_placed (ext := ext) s1 fsp out pbA
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104
    (A.pool lim st s1 ∗ Rest)
    hfsp_align hpc1 hrun1 hsp1 hx8_1 hx19_1 hx23_1 hx25_1 hx27_1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- `VmPreserved`-strengthened `+860 -> +4176` (`EkSentCt1Received::from_pb` returned `Err`). -/
theorem v3cr_post_uc_860_err_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s1 : State) (fsp out w1896 w1904 w1912 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 860#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp) (hx19_1 : s1.readReg64 .x19 = out) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4176#64) s1
      (((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
        ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
          ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = w1896 ∧ TraceCalleeSaved sm s1) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.v3cr_post_uc_860_err_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out w1896 w1904 w1912 Rest hfsp_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1))
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, hx22_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx19_m, by simpa using hx22_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v3cr_post_uc_860_err_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s1 : State) (fsp out w1896 w1904 w1912 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 860#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp) (hx19_1 : s1.readReg64 .x19 = out) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4176#64) s1
      (((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
        ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
          ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗
          A.pool lim st sm ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = w1896 ∧ TraceCalleeSaved sm s1) := by
  have hwp := v3cr_post_uc_860_err_placed (ext := ext) s1 fsp out w1896 w1904 w1912
    (A.pool lim st s1 ∗ Rest) hfsp_align hpc1 hrun1 hsp1 hx19_1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- `VmPreserved`-strengthened `+860 -> +4884` (`uc = Ok(ucSt)`, `sendingEk = none`). -/
theorem v3cr_post_uc_860_ok_none_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s1 : State)
    (fsp out ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep v176 v224 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hca1_lt : ca1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 860#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp) (hx19_1 : s1.readReg64 .x19 = out) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4884#64) s1
      (((fsp + 176#64) ↦₆₄ v176) ∗ ((fsp + 224#64) ↦₆₄ v224) ∗ ((fsp + 1496#64) ↦₆₄ noneCap) ∗
        v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗ ((fsp + 1496#64) ↦₆₄ noneCap) ∗
          v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = pa2 ∧ sm.readReg64 .x1 = ca1 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = pa4 ∧ sm.readReg64 .x22 = pa1 ∧
        sm.readReg64 .x26 = ca3 ∧ sm.readReg64 .x28 = ca2 ∧ TraceCalleeSaved sm s1) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.v3cr_post_uc_860_ok_none_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep v176 v224 Rest
      hfsp_align hca1_lt
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1))
    fun sm Pm hvm ⟨hPm, hsp_m, hx0_m, hx1_m, hx19_m, hx21_m, hx22_m, hx26_m, hx28_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx0_m, by simpa using hx1_m,
       by simpa using hx19_m, by simpa using hx21_m, by simpa using hx22_m,
       by simpa using hx26_m, by simpa using hx28_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v3cr_post_uc_860_ok_none_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)} (s1 : State)
    (fsp out ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep v176 v224 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hca1_lt : ca1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 860#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp) (hx19_1 : s1.readReg64 .x19 = out) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4884#64) s1
      (((fsp + 176#64) ↦₆₄ v176) ∗ ((fsp + 224#64) ↦₆₄ v224) ∗ ((fsp + 1496#64) ↦₆₄ noneCap) ∗
        v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗ ((fsp + 1496#64) ↦₆₄ noneCap) ∗
          v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
          A.pool lim st sm ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = pa2 ∧ sm.readReg64 .x1 = ca1 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = pa4 ∧ sm.readReg64 .x22 = pa1 ∧
        sm.readReg64 .x26 = ca3 ∧ sm.readReg64 .x28 = ca2 ∧ TraceCalleeSaved sm s1) := by
  have hwp := v3cr_post_uc_860_ok_none_placed (ext := ext) s1 fsp out
    ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep v176 v224
    (A.pool lim st s1 ∗ Rest) hfsp_align hca1_lt hpc1 hrun1 hsp1 hx19_1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- `VmPreserved`-strengthened `+860 -> +924` (`uc = Ok(ucSt)`, `sendingEk = some pbEnc`). -/
theorem v3cr_post_uc_860_ok_some_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s1 : State)
    (fsp out pbA ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep w0 v176 v224 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hca1_lt : ca1.toNat < 2 ^ 63) (hw0_lt : w0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 860#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp) (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64) (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 924#64) s1
      (((fsp + 176#64) ↦₆₄ v176) ∗ ((fsp + 224#64) ↦₆₄ v224) ∗ ((fsp + 1496#64) ↦₆₄ w0) ∗
        v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗ ((fsp + 1496#64) ↦₆₄ w0) ∗
          v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = pa2 ∧ sm.readReg64 .x1 = ca1 ∧ sm.readReg64 .x8 = w0 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = pa4 ∧ sm.readReg64 .x22 = pa1 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧ sm.readReg64 .x24 = la1 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧ sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = ca2 ∧
        sm.readReg64 .x29 = s1.readReg64 .x29 ∧ TraceCalleeSaved sm s1) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.v3cr_post_uc_860_ok_some_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out pbA ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep w0 v176 v224 Rest
      hfsp_align hca1_lt hw0_lt
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx23_1) (by simpa using hx25_1)
      (by simpa using hx27_1))
    fun sm Pm hvm ⟨hPm, hsp_m, hx0_m, hx1_m, hx8_m, hx19_m, hx21_m, hx22_m, hx23_m,
        hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hx29_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx0_m, by simpa using hx1_m,
       by simpa using hx8_m, by simpa using hx19_m, by simpa using hx21_m,
       by simpa using hx22_m, by simpa using hx23_m, by simpa using hx24_m,
       by simpa using hx25_m, by simpa using hx26_m, by simpa using hx27_m,
       by simpa using hx28_m, by simpa using hx29_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v3cr_post_uc_860_ok_some_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)} (s1 : State)
    (fsp out pbA ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep w0 v176 v224 : BitVec 64)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hca1_lt : ca1.toNat < 2 ^ 63) (hw0_lt : w0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 860#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = fsp) (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64) (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 924#64) s1
      (((fsp + 176#64) ↦₆₄ v176) ∗ ((fsp + 224#64) ↦₆₄ v224) ∗ ((fsp + 1496#64) ↦₆₄ w0) ∗
        v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗ ((fsp + 1496#64) ↦₆₄ w0) ∗
          v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
          A.pool lim st sm ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = pa2 ∧ sm.readReg64 .x1 = ca1 ∧ sm.readReg64 .x8 = w0 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = pa4 ∧ sm.readReg64 .x22 = pa1 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧ sm.readReg64 .x24 = la1 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧ sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = ca2 ∧
        sm.readReg64 .x29 = s1.readReg64 .x29 ∧ TraceCalleeSaved sm s1) := by
  have hwp := v3cr_post_uc_860_ok_some_placed (ext := ext) s1 fsp out pbA
    ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep w0 v176 v224
    (A.pool lim st s1 ∗ Rest) hfsp_align hca1_lt hw0_lt
    hpc1 hrun1 hsp1 hx19_1 hx23_1 hx25_1 hx27_1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-! ## Exact Envelopes & `StatesFromPbEnv` Subsumption for Variant 3 (`Ct1Received`) -/

/-- Exact allocation-prefix envelope for Variant 3 (`InnerState.ct1Received`, `+692`) of
    `<spqr::v1::chunked::states::States>::from_pb`. -/
def Ct1ReceivedFromPbAllocEnv (F : ShaCompress)
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.Ct1Received) (evs : List AllocEvent) : Prop :=
  match s.uc with
  | none => evs = []
  | some u =>
    match ekSentCt1ReceivedFromPb (spqrAuthApi F) u with
    | .error _ => evs = []
    | .ok _ =>
      match s.sendingEk with
      | none => evs = ekSentCt1ReceivedFromPbAllocEvents F u
      | some pbEnc =>
        evs = ekSentCt1ReceivedFromPbAllocEvents F u ∨
          ∃ evs_uf evs_enc,
            FreeOnlyEvs evs_uf ∧
            EncoderFromPbAllocEnv (pbToProtoPolyEncoder pbEnc) evs_enc ∧
            evs_enc ≠ [] ∧
            evs = ekSentCt1ReceivedFromPbAllocEvents F u ++ evs_uf ++ evs_enc

/-- Complete allocator event envelope for Variant 3 (`InnerState.ct1Received`, `+692`) of
    `<spqr::v1::chunked::states::States>::from_pb`, including `FreeOnlyEvs` drops. -/
def Ct1ReceivedFromPbEnv (F : ShaCompress)
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.Ct1Received) (evs : List AllocEvent) : Prop :=
  match s.uc with
  | none => FreeOnlyEvs evs
  | some u =>
    match ekSentCt1ReceivedFromPb (spqrAuthApi F) u with
    | .error _ => FreeOnlyEvs evs
    | .ok _ =>
      match s.sendingEk with
      | none =>
        ∃ evs_free, FreeOnlyEvs evs_free ∧
          evs = ekSentCt1ReceivedFromPbAllocEvents F u ++ evs_free
      | some pbEnc =>
        ∃ evs_uf evs_enc,
          FreeOnlyEvs evs_uf ∧
          EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs_enc ∧
          evs = ekSentCt1ReceivedFromPbAllocEvents F u ++ evs_uf ++ evs_enc

/-- Tail `FitsEnv` precondition at `+860` after `<EkSentCt1Received>::from_pb` returns. -/
def Ct1ReceivedTailFits (M : AllocCostModel) (lim : BudgetLimits) (st : M.σ)
    (F : ShaCompress) (u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.EkSentCt1Received)
    (optEnc : Option PolynomialEncoder) : Prop :=
  match ekSentCt1ReceivedFromPb (spqrAuthApi F) u with
  | .error _ => True
  | .ok _ =>
    match optEnc with
    | none => True
    | some pbEnc => FitsEnv M lim st (EncoderFromPbAllocEnv (pbToProtoPolyEncoder pbEnc))

/-- Tail postcondition envelope from `+860` to `s0.x30`. -/
def Ct1ReceivedTailEnv (F : ShaCompress) (u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.EkSentCt1Received)
    (optEnc : Option PolynomialEncoder) (evs : List AllocEvent) : Prop :=
  match ekSentCt1ReceivedFromPb (spqrAuthApi F) u with
  | .error _ => FreeOnlyEvs evs
  | .ok _ =>
    match optEnc with
    | none => FreeOnlyEvs evs
    | some pbEnc => EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs

theorem ct1ReceivedAllocEnv_imp_ct1ReceivedEnv {F : ShaCompress}
    {s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.Ct1Received} {evs : List AllocEvent}
    (h : Ct1ReceivedFromPbAllocEnv F s evs) :
    Ct1ReceivedFromPbEnv F s evs := by
  cases s with | mk optUc optEnc =>
  cases optUc with
  | none =>
    dsimp only [Ct1ReceivedFromPbAllocEnv, Ct1ReceivedFromPbEnv] at h ⊢
    subst h
    exact LibsignalBinary.Heap.FreeOnlyEvs.nil
  | some u =>
    dsimp only [Ct1ReceivedFromPbAllocEnv, Ct1ReceivedFromPbEnv] at h ⊢
    cases huc : ekSentCt1ReceivedFromPb (spqrAuthApi F) u with
    | error _ =>
      rw [huc] at h
      subst h
      exact LibsignalBinary.Heap.FreeOnlyEvs.nil
    | ok _ =>
      rw [huc] at h
      cases optEnc with
      | none =>
        exact ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, by rw [h, List.append_nil]⟩
      | some pbEnc =>
        rcases h with hek | ⟨evs_uf, evs_enc, hfree_uf, henc, _, rfl⟩
        · refine ⟨[], [], LibsignalBinary.Heap.FreeOnlyEvs.nil,
            encoderFromPbAllocEnv_imp_encoderFromPbEnv (Or.inl rfl), ?_⟩
          simp [hek]
        · exact ⟨evs_uf, evs_enc, hfree_uf,
            encoderFromPbAllocEnv_imp_encoderFromPbEnv henc, rfl⟩

theorem fitsEnv_alloc_of_ct1ReceivedEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {F : ShaCompress} {s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.Ct1Received}
    (h : FitsEnv M lim st (Ct1ReceivedFromPbEnv F s)) :
    FitsEnv M lim st (Ct1ReceivedFromPbAllocEnv F s) :=
  LibsignalBinary.Heap.FitsEnv.mono (fun _ => ct1ReceivedAllocEnv_imp_ct1ReceivedEnv) h

theorem fitsEnv_ekPre_of_ct1ReceivedAllocEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {F : ShaCompress} {u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.EkSentCt1Received}
    {optEnc : Option PolynomialEncoder}
    (hfits : FitsEnv M lim st
      (Ct1ReceivedFromPbAllocEnv F { uc := some u, sendingEk := optEnc })) :
    FitsEnv M lim st (EkSentCt1ReceivedFromPbPreEnv F u) := by
  intro evs hevs
  dsimp only [EkSentCt1ReceivedFromPbPreEnv] at hevs
  subst hevs
  apply hfits
  dsimp only [Ct1ReceivedFromPbAllocEnv]
  cases huc : ekSentCt1ReceivedFromPb (spqrAuthApi F) u with
  | error _ =>
    simp [ekSentCt1ReceivedFromPbAllocEvents, huc]
  | ok _ =>
    cases optEnc with
    | none => rfl
    | some _ => exact Or.inl rfl

theorem ct1ReceivedTailFits_of_ct1ReceivedAllocEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {F : ShaCompress} {u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.EkSentCt1Received}
    {optEnc : Option PolynomialEncoder} {evs_uc : List AllocEvent}
    (hfits : FitsEnv M lim st
      (Ct1ReceivedFromPbAllocEnv F { uc := some u, sendingEk := optEnc }))
    (henv_uc : EkSentCt1ReceivedFromPbPostEnv F u evs_uc) :
    Ct1ReceivedTailFits M lim (M.stepEvents evs_uc st) F u optEnc := by
  dsimp only [Ct1ReceivedTailFits]
  cases huc : ekSentCt1ReceivedFromPb (spqrAuthApi F) u with
  | error _ => trivial
  | ok _ =>
    cases optEnc with
    | none => trivial
    | some pbEnc =>
      rcases henv_uc with ⟨evs_uf, hfree_uf, rfl⟩
      intro evs_enc henc
      by_cases hne : evs_enc = []
      · subst hne; simp [FitsEvents]
      · have hev : Ct1ReceivedFromPbAllocEnv F { uc := some u, sendingEk := some pbEnc }
            ((ekSentCt1ReceivedFromPbAllocEvents F u ++ evs_uf) ++ evs_enc) := by
          dsimp only [Ct1ReceivedFromPbAllocEnv]
          rw [huc]
          exact Or.inr ⟨evs_uf, evs_enc, hfree_uf, henc, hne, rfl⟩
        exact ((fitsEvents_append M lim
          (ekSentCt1ReceivedFromPbAllocEvents F u ++ evs_uf) evs_enc st).mp
          (hfits _ hev)).2

theorem ct1ReceivedEnv_of_tail {F : ShaCompress} {u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.EkSentCt1Received}
    {optEnc : Option PolynomialEncoder} {evs_uc evs_tail : List AllocEvent}
    (henv_uc : EkSentCt1ReceivedFromPbPostEnv F u evs_uc)
    (htail : Ct1ReceivedTailEnv F u optEnc evs_tail) :
    Ct1ReceivedFromPbEnv F { uc := some u, sendingEk := optEnc } (evs_uc ++ evs_tail) := by
  rcases henv_uc with ⟨evs_uf, hfree_uf, rfl⟩
  dsimp only [Ct1ReceivedFromPbEnv, Ct1ReceivedTailEnv] at htail ⊢
  cases huc : ekSentCt1ReceivedFromPb (spqrAuthApi F) u with
  | error _ =>
    rw [huc] at htail
    have hemp : ekSentCt1ReceivedFromPbAllocEvents F u = [] := by
      simp [ekSentCt1ReceivedFromPbAllocEvents, huc]
    rw [hemp, List.nil_append]
    exact LibsignalBinary.Heap.FreeOnlyEvs.append hfree_uf htail
  | ok _ =>
    rw [huc] at htail
    cases optEnc with
    | none =>
      exact ⟨evs_uf ++ evs_tail, LibsignalBinary.Heap.FreeOnlyEvs.append hfree_uf htail,
        List.append_assoc _ evs_uf evs_tail⟩
    | some pbEnc =>
      exact ⟨evs_uf, evs_tail, hfree_uf, htail, rfl⟩

private theorem authFromPbAllocEvents_eq_authFromPbEvents (auth : ProtoAuthenticator) :
    authFromPbAllocEvents auth = authFromPbEvents auth := by
  unfold authFromPbAllocEvents authFromPbEvents authKeyCloneEvents
  cases auth.rootKey <;> cases auth.macKey <;> simp

private theorem spqrBoundedEvs_alloc_singleton {sz : Nat}
    (hmax : sz ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs 1 sz [.alloc sz] := by
  refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
  simp only [List.mem_singleton] at hev
  subst hev
  exact ⟨hmax, Nat.le_refl sz, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem spqrBoundedEvs_ptsLoopEvents (pts : List (List (BitVec 8)))
    (hmax : 2 * (pts.map List.length).sum ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs pts.length (2 * (pts.map List.length).sum)
      (encoderFromPbPtsLoopEvents pts) := by
  unfold encoderFromPbPtsLoopEvents
  induction pts with
  | nil => exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.nil 0 0
  | cons bs rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hmax ⊢
    by_cases heven : (bs.length % 2 == 0) = true
    · simp only [List.takeWhile_cons, heven, ↓reduceIte, List.flatMap_cons]
      have hih := ih (by omega)
      unfold encoderFromPbPtsSlotEvents
      by_cases hemp : bs.isEmpty = true
      · simp only [hemp, ↓reduceIte, List.nil_append]
        exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by omega) (by omega) hih
      · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
        have hpos : 1 ≤ bs.length := by
          cases bs with
          | nil => simp at hemp
          | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
        have h2 : 2 ≤ 2 * bs.length := by omega
        have hre : rustAllocEvents (2 * bs.length) 2 = [.alloc (2 * bs.length)] := by
          simp [rustAllocEvents, h2]
        rw [hre]
        exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by omega) (by omega)
          (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append (spqrBoundedEvs_alloc_singleton (by omega)) hih)
    · have hfls : (bs.length % 2 == 0) = false := Bool.eq_false_iff.mpr heven
      simp only [List.takeWhile_cons, hfls, Bool.false_eq_true, ↓reduceIte, List.flatMap_nil]
      exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.nil _ _

private theorem spqrBoundedEvs_replicate_alloc2 :
    ∀ n : Nat, SpqrBoundedEvs n 2 ((List.replicate n (rustAllocEvents 2 2)).flatten)
  | 0 => LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.nil 0 2
  | n + 1 => by
    simp only [List.replicate_succ, List.flatten_cons]
    have hre : rustAllocEvents 2 2 = [.alloc 2] := by simp [rustAllocEvents]
    rw [hre]
    have h2max : 2 ≤ MallocngMaxAllocSize := by
      dsimp only [MMAP_MIN_ADDR, PAGE_SIZE, MallocngMaxAllocSize]; omega
    exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by omega) (by omega)
      (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append (spqrBoundedEvs_alloc_singleton h2max)
        (spqrBoundedEvs_replicate_alloc2 n))

private theorem spqrBoundedEvs_polysLoopEvents (polys : List (List (BitVec 8)))
    (hmax : (polys.map List.length).sum ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs polys.length (polys.map List.length).sum
      (encoderFromPbPolysLoopEvents polys) := by
  unfold encoderFromPbPolysLoopEvents
  induction polys with
  | nil => exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.nil 0 0
  | cons bs rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hmax ⊢
    by_cases hok : (!bs.isEmpty && (bs.length % 2 == 0)) = true
    · simp only [List.takeWhile_cons, hok, ↓reduceIte, List.flatMap_cons]
      have hih := ih (by omega)
      rw [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hok
      have hne : 1 ≤ bs.length := by
        cases bs with
        | nil => simp at hok
        | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
      have h2 : 2 ≤ bs.length := by omega
      unfold encoderFromPbPolysSlotEvents
      have hre : rustAllocEvents bs.length 2 = [.alloc bs.length] := by
        simp [rustAllocEvents, h2]
      rw [hre]
      have hslot : SpqrBoundedEvs 1 bs.length ([.alloc bs.length] ++ rustDeallocEvents 2 2) :=
        LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by omega) (by omega)
          (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append (spqrBoundedEvs_alloc_singleton (by omega))
            (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.of_freeOnly (LibsignalBinary.Heap.FreeOnlyEvs.singleton 2 2)))
      exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by omega) (by omega) (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append hslot hih)
    · have hfls : (!bs.isEmpty && (bs.length % 2 == 0)) = false := Bool.eq_false_iff.mpr hok
      simp only [List.takeWhile_cons, hfls, Bool.false_eq_true, ↓reduceIte, List.flatMap_nil]
      exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.nil _ _

private theorem spqrBoundedEvs_encoderFromPbEnv {pb : ProtoPolynomialEncoder}
    {evs : List AllocEvent}
    (hmax : 2 * (pb.pts.map List.length).sum + (pb.polys.map List.length).sum + 2 ≤
      MallocngMaxAllocSize)
    (hevs : EncoderFromPbEnv pb evs) :
    SpqrBoundedEvs 32
      (2 * (pb.pts.map List.length).sum + (pb.polys.map List.length).sum + 2) evs := by
  rcases hevs with ⟨evs_a, evs_f, rfl, ha, hf⟩
  have hba : SpqrBoundedEvs 32
      (2 * (pb.pts.map List.length).sum + (pb.polys.map List.length).sum + 2) evs_a := by
    rcases ha with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
    · exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.nil _ _
    · exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by omega) (by omega)
        (spqrBoundedEvs_ptsLoopEvents pb.pts (by omega))
    · exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by omega) (by omega)
        (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append (spqrBoundedEvs_replicate_alloc2 16)
          (spqrBoundedEvs_polysLoopEvents pb.polys (by omega)))
  exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by omega) (by omega)
    (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append hba (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.of_freeOnly hf))

private theorem spqrBoundedEvs_ekAllocEvents (F : ShaCompress)
    (u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.EkSentCt1Received)
    (hmax : optRaw rawAuth u.auth ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs 2 (optRaw rawAuth u.auth) (ekSentCt1ReceivedFromPbAllocEvents F u) := by
  unfold ekSentCt1ReceivedFromPbAllocEvents
  cases ekSentCt1ReceivedFromPb (spqrAuthApi F) u with
  | error _ => exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.nil _ _
  | ok _ =>
    cases hauth : u.auth with
    | none => exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.nil _ _
    | some auth =>
      rw [hauth] at hmax
      dsimp only [optRaw, rawAuth] at hmax ⊢
      rw [authFromPbAllocEvents_eq_authFromPbEvents, authFromPbEvents]
      have hb_r := spqrBoundedEvs_authKeyCloneEvents (bs := auth.rootKey) (by omega)
      have hb_m := spqrBoundedEvs_authKeyCloneEvents (bs := auth.macKey) (by omega)
      exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by decide) (by omega) (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append hb_r hb_m)

private theorem rawAuth_le_ct1Received_encodeRaw
    (u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.EkSentCt1Received) (optEnc : Option PolynomialEncoder) :
    optRaw rawAuth u.auth ≤
      (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw
        { innerState := some (.ct1Received { uc := some u, sendingEk := optEnc }) }).length := by
  have h0 := length_le_encodeMessage CryptoVerification.LibsignalSpqrV1.V1State.Chunked.Ct1Received.encodeRaw 4#32
    { uc := some u, sendingEk := optEnc }
  have h1 := length_le_encodeOptMessage CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.EkSentCt1Received.encodeRaw
    rawUcEkSentCt1Received rawUcEkSentCt1Received_le_encodeRaw 1#32 (some u)
  dsimp only [CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw, CryptoVerification.LibsignalSpqrV1.V1State.InnerState.encode,
    CryptoVerification.LibsignalSpqrV1.V1State.Chunked.Ct1Received.encodeRaw, rawUcEkSentCt1Received, optRaw] at h0 h1 ⊢
  rw [List.length_append] at h0
  omega

private theorem rawAuth_and_enc_le_ct1Received_encodeRaw
    (u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.EkSentCt1Received) (pbEnc : PolynomialEncoder) :
    optRaw rawAuth u.auth +
      (pbEnc.pts.map List.length).sum + (pbEnc.polys.map List.length).sum ≤
      (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw
        { innerState := some (.ct1Received { uc := some u, sendingEk := some pbEnc }) }).length := by
  have h0 := length_le_encodeMessage CryptoVerification.LibsignalSpqrV1.V1State.Chunked.Ct1Received.encodeRaw 4#32
    { uc := some u, sendingEk := some pbEnc }
  have h1 := length_le_encodeOptMessage CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.EkSentCt1Received.encodeRaw
    rawUcEkSentCt1Received rawUcEkSentCt1Received_le_encodeRaw 1#32 (some u)
  have h2 := length_le_encodeMessage CryptoVerification.LibsignalSpqrV1.PolynomialEncoder.encodeRaw 2#32 pbEnc
  have hp1 := sum_length_le_encodeRepeatedBytes 2#32 pbEnc.pts
  have hp2 := sum_length_le_encodeRepeatedBytes 3#32 pbEnc.polys
  dsimp only [CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw, CryptoVerification.LibsignalSpqrV1.V1State.InnerState.encode,
    CryptoVerification.LibsignalSpqrV1.V1State.Chunked.Ct1Received.encodeRaw,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
    CryptoVerification.LibsignalSpqrV1.PolynomialEncoder.encodeRaw, rawUcEkSentCt1Received, optRaw] at h0 h1 h2 ⊢
  simp only [List.length_append] at h0 h2
  omega

theorem ct1ReceivedEnv_sub_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {F : ShaCompress}
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.Ct1Received)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.ct1Received s) }))
    {evs : List AllocEvent} (hevs : Ct1ReceivedFromPbEnv F s evs) :
    StatesFromPbEnv { innerState := some (.ct1Received s) } evs := by
  let pb : V1State := { innerState := some (.ct1Received s) }
  change SpqrBoundedEvs 128 (4 * (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw pb).length + 4096) evs
  cases s with | mk optUc optEnc =>
  cases optUc with
  | none =>
    exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by decide) (by omega) (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.of_freeOnly hevs)
  | some u =>
    dsimp only [Ct1ReceivedFromPbEnv] at hevs
    cases huc : ekSentCt1ReceivedFromPb (spqrAuthApi F) u with
    | error _ =>
      rw [huc] at hevs
      exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by decide) (by omega) (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.of_freeOnly hevs)
    | ok _ =>
      rw [huc] at hevs
      let m := min (2 * (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw pb).length + 2) MallocngMaxAllocSize
      have hm_env : StatesFromPbEnv pb [.alloc m] := by
        refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
        simp only [List.mem_singleton] at hev
        subst hev
        exact ⟨Nat.min_le_right _ _,
          Nat.le_trans (Nat.min_le_left _ _) (by omega),
          (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
      have hm_fit : FitsEvents M lim st [.alloc m] := hfits [.alloc m] hm_env
      rcases hm_fit with ⟨⟨_, _, _, hva⟩, _⟩
      have hm_req : m ≤ M.stepReserve (.alloc m) st := M.req_le_stepReserve (.alloc m) st
      have hm_max : 2 * (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw pb).length + 2 ≤ MallocngMaxAllocSize := by
        dsimp only [m, MMAP_MIN_ADDR, PAGE_SIZE, MallocngMaxAllocSize] at hva hm_req ⊢
        omega
      cases optEnc with
      | none =>
        rcases hevs with ⟨evs_free, hfree, rfl⟩
        have hlen := rawAuth_le_ct1Received_encodeRaw u none
        have hb_ek := spqrBoundedEvs_ekAllocEvents F u (by dsimp [pb] at hm_max; omega)
        have hb_all := LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append hb_ek (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.of_freeOnly hfree)
        exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by decide) (by dsimp [pb]; omega) hb_all
      | some pbEnc =>
        rcases hevs with ⟨evs_uf, evs_enc, hfree_uf, henc, rfl⟩
        have hlen := rawAuth_and_enc_le_ct1Received_encodeRaw u pbEnc
        have hpb_pts : (pbToProtoPolyEncoder pbEnc).pts = pbEnc.pts := rfl
        have hpb_pol : (pbToProtoPolyEncoder pbEnc).polys = pbEnc.polys := rfl
        have hb_ek := spqrBoundedEvs_ekAllocEvents F u (by dsimp [pb] at hm_max; omega)
        have hb_enc := spqrBoundedEvs_encoderFromPbEnv
          (pb := pbToProtoPolyEncoder pbEnc)
          (by rw [hpb_pts, hpb_pol]; dsimp [pb] at hm_max; omega) henc
        rw [hpb_pts, hpb_pol] at hb_enc
        have hb_1 := LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append hb_ek (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.of_freeOnly hfree_uf)
        have hb_all := LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append hb_1 hb_enc
        exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by decide) (by dsimp [pb]; omega) hb_all

theorem fitsEnv_alloc_of_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {F : ShaCompress}
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.Ct1Received)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.ct1Received s) })) :
    FitsEnv M lim st (Ct1ReceivedFromPbAllocEnv F s) :=
  fitsEnv_alloc_of_ct1ReceivedEnv fun evs hevs =>
    hfits evs (ct1ReceivedEnv_sub_statesFromPbEnv s hfits hevs)

/-! ## Post-`EkSentCt1Received.from_pb` Continuation (`+860 -> s0.x30`, `SepWP` & `SepWPp`) -/

set_option maxHeartbeats 1200000 in
/-- Total-correctness (`SepWP`) post-`EkSentCt1Received::from_pb` continuation at `+860`
    (`lsmpl.base 333 + 860`) to `s0.x30` under `RustCliAllocBudget M`. -/
theorem v3_ct1Received_post_uc_860_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (hEnc : EncoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (out pbA : BitVec 64)
    (u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.EkSentCt1Received)
    (optEnc : Option PolynomialEncoder)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (hpts : ∀ pbEnc, optEnc = some pbEnc → ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hfits : Ct1ReceivedTailFits M lim st F u optEnc)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 860#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx25_1 : s1.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
        ekSentCt1ReceivedResultAt A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64)
          (ekSentCt1ReceivedFromPb (spqrAuthApi F) u) ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA 112 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (optEnc.map pbToProtoPolyEncoder)
          w0 w8 w16 w24 w32 w40 w48 ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          Ct1ReceivedTailEnv F u optEnc evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (CryptoVerification.LibsignalSpqrV1.States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ct1Received { uc := some u, sendingEk := optEnc }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  cases huc : ekSentCt1ReceivedFromPb (spqrAuthApi F) u with
  | error e =>
    have he := v3cr_ekSentCt1Received_from_pb_err_eq u e huc
    subst he
    rw [v3cr_states_from_pb_ct1Received_uc_err_eq u optEnc huc]
    have herr := v3cr_ekResult_err_unpack A.repAlloc (F := F)
      ((s0.sp - 2400#64) + 1888#64) (.err .stateDecode)
    simp only [v3cr_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at herr
    have hpack_enc := v3cr_optProtoPolyEncoderAt_pack A.repAlloc ((s0.sp - 2400#64) + 1496#64)
      (optEnc.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
    have hpb224 := v3_collapse_pbA_112_224 pbA w0 w8 w16 w24 w32 w40 w48
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      ekSentCt1ReceivedResultAt A.repAlloc (F := F)
        ((s0.sp - 2400#64) + 1888#64) (.error (.err .stateDecode)) ∗
      (v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A.repAlloc (optEnc.map pbToProtoPolyEncoder)
         w0 w8 w16 w24 w32 w40 w48) ∗
      (memRegion pbA 112 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 168#64) 56) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 1496 ∗
       memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗ memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1) by sep_ac_rfl))
      (sepConj_mono herr (sepConj_mono hpack_enc (sepConj_mono_left hpb224)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun w1896 => SepWP.exists_elim fun w1904 =>
      SepWP.exists_elim fun w1912 => ?_
    refine SepWP.pure_elim fun hw1896 => ?_
    have h860 := v3cr_post_uc_860_err_placed_budget A lim st (ext := ext) s1
      (s0.sp - 2400#64) out w1896 w1904 w1912
      (memRegion ((s0.sp - 2400#64) + 1920#64) 72 ∗
       optProtoPolynomialEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1496#64)
         (optEnc.map pbToProtoPolyEncoder) ∗
       memRegion pbA optProtoInnerStateSize ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 1496 ∗ memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
       memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt)
      hfsp_align hpc1 hrun1 hsp1 hx19_1
    refine seq_clean_lscl_st hcl1
      (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) h860) ?_
    intro s2 hpc2 hrun2 hcl2 ⟨_hvm2, hsp2, hx19_2, hx22_2, htr2⟩
    have h752 := v3_collapse_1552_752_err (s0.sp - 2400#64) w1896 w1904 w1912
    have hpre2 :
        (((s0.sp - 2400#64) + 1888#64) ↦₆₄ noneCap) ∗ (((s0.sp - 2400#64) + 1896#64) ↦₆₄ w1896) ∗
        (((s0.sp - 2400#64) + 1904#64) ↦₆₄ w1904) ∗ (((s0.sp - 2400#64) + 1912#64) ↦₆₄ w1912) ∗
        A.pool lim st s2 ∗
        (memRegion ((s0.sp - 2400#64) + 1920#64) 72 ∗
         optProtoPolynomialEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1496#64)
           (optEnc.map pbToProtoPolyEncoder) ∗
         memRegion pbA optProtoInnerStateSize ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 1496 ∗ memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
         memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt) ⊢
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        optProtoPolynomialEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1496#64)
          (optEnc.map pbToProtoPolyEncoder) ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s2 ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) := by
      refine Entails.trans (Entails.of_eq (show _ =
        (memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
         (((s0.sp - 2400#64) + 1888#64) ↦₆₄ noneCap) ∗ (((s0.sp - 2400#64) + 1896#64) ↦₆₄ w1896) ∗
         (((s0.sp - 2400#64) + 1904#64) ↦₆₄ w1904) ∗ (((s0.sp - 2400#64) + 1912#64) ↦₆₄ w1912) ∗
         memRegion ((s0.sp - 2400#64) + 1920#64) 72 ∗ memRegion ((s0.sp - 2400#64) + 1992#64) 312) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 1496 ∗
         optProtoPolynomialEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1496#64)
           (optEnc.map pbToProtoPolyEncoder) ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s2 ∗
         (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left h752) (Entails.of_eq (by sep_ac_rfl))
    have hx22_byte : (s2.readReg64 .x22).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx22_2, hw1896]; rfl
    have h4176 := Variant3bPlacedBudget.v3cr_states_from_pb_err_4176_placed (F := F) hA st s0 s2 hcl2 out .stateDecode optEnc
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_byte (htr2.trans htr1)
    refine SepWP.weaken_pre hpre2 (SepWP.mono h4176 ?_)
    intro sf Pf _ _ ⟨evs, hevs, hPf, hsp_f, hcs_f, htr_f⟩
    refine ⟨⟨evs, ?_, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩, hsp_f, hcs_f, htr_f⟩
    dsimp only [Ct1ReceivedTailEnv]
    rw [huc]
    exact hevs
  | ok ucSt =>
    dsimp only [ekSentCt1ReceivedResultAt]
    rw [v3_ekSentCt1ReceivedAt_eq_unchunked]
    have hopen := v3cr_unchunkedEkSentCt1ReceivedAt_open A.repAlloc (F := F)
      ((s0.sp - 2400#64) + 1888#64) ucSt
    refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hopen))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun ca1 => SepWP.exists_elim fun pa1 => SepWP.exists_elim fun la1 =>
      SepWP.exists_elim fun ca2 => SepWP.exists_elim fun pa2 => SepWP.exists_elim fun la2 =>
      SepWP.exists_elim fun ca3 => SepWP.exists_elim fun pa3 => SepWP.exists_elim fun la3 =>
      SepWP.exists_elim fun ca4 => SepWP.exists_elim fun pa4 => SepWP.exists_elim fun la4 =>
      SepWP.exists_elim fun uc_ep => ?_
    have hca1_ext := v3cr_unchunkedHeap_ca1_lt A.repAlloc (F := F) ucSt
      ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    have hw0_ext := v1_optProtoPolyEncoderHeap_extract_w0 A.repAlloc
      (optEnc.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
        ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
      v1_optProtoPolyEncoderHeap A.repAlloc (optEnc.map pbToProtoPolyEncoder)
        w0 w8 w16 w24 w32 w40 w48 ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 1496 ∗
       v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
       v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
       memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       memRegion pbA 112 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 168#64) 56 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1) by sep_ac_rfl))
      (sepConj_mono hca1_ext (sepConj_mono_left hw0_ext))) ?_
    simp only [sepConj_assoc]
    refine SepWP.pure_elim fun hca1_lt => ?_
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜match optEnc.map pbToProtoPolyEncoder with | none => w0 = noneCap | some _ => w0.toNat < 2 ^ 63⌝ ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 1496 ∗
       v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
       v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
       memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
       v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
         ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
       v1_optProtoPolyEncoderHeap A.repAlloc (optEnc.map pbToProtoPolyEncoder)
         w0 w8 w16 w24 w32 w40 w48 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       memRegion pbA 112 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 168#64) 56 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1) by sep_ac_rfl)) ?_
    refine SepWP.pure_elim fun hw0_prop => ?_
    cases optEnc with
    | none =>
      dsimp only [Option.map_none] at hw0_prop
      subst hw0_prop
      rw [v3cr_states_from_pb_ct1Received_sendingEk_none_eq u ucSt huc]
      have h1496 := v3_split_1496_none (s0.sp - 2400#64)
      have hdealloc := v3cr_unchunkedHeap_entails_dealloc A.repAlloc (F := F) ucSt
        ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
      have hpb224 := v3_collapse_pbA_112_224 pbA noneCap w8 w16 w24 w32 w40 w48
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        memRegion (s0.sp - 2400#64) 1496 ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        (memRegion pbA 112 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 112#64) noneCap w8 w16 w24 w32 w40 w48 ∗
         memRegion (pbA + 168#64) 56) ∗
        v1_optProtoPolyEncoderHeap A.repAlloc none noneCap w8 w16 w24 w32 w40 w48 ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) noneCap w8 w16 w24 w32 w40 w48 ∗
         memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
         v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
         memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1) by sep_ac_rfl))
        (sepConj_mono h1496 (sepConj_mono hdealloc (sepConj_mono_left hpb224)))) ?_
      dsimp only [v1_optProtoPolyEncoderHeap]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWP.exists_elim fun v224 => SepWP.exists_elim fun v176 => ?_
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        ⌜True⌝ ∗
        ((((s0.sp - 2400#64) + 176#64) ↦₆₄ v176) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ v224) ∗
         v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) noneCap w8 w16 w24 w32 w40 w48 ∗
         v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
         A.pool lim st s1 ∗
         (memRegion (s0.sp - 2400#64) 176 ∗ memRegion ((s0.sp - 2400#64) + 184#64) 40 ∗
          memRegion ((s0.sp - 2400#64) + 232#64) 1264 ∗
          vecCapPtrDealloc A.repAlloc ca1 pa1 ∗ vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
          vecCapPtrDealloc A.repAlloc ca3 pa3 ∗ vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
          memRegion pbA optProtoInnerStateSize ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗ memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          statesFromPbJumpTablePlacedAt)) by sep_ac_rfl)) ?_
      refine SepWP.pure_elim fun _ => ?_
      dsimp only [v1_optProtoPolyEncoderWordsAt]
      simp only [sepConj_assoc]
      have h860 := v3cr_post_uc_860_ok_none_placed_budget A lim st (ext := ext) s1
        (s0.sp - 2400#64) out
        ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep v176 v224
        ((((s0.sp - 2400#64) + 1496#64 + 8#64) ↦₆₄ w8) ∗
         (((s0.sp - 2400#64) + 1496#64 + 16#64) ↦₆₄ w16) ∗
         (((s0.sp - 2400#64) + 1496#64 + 24#64) ↦₆₄ w24) ∗
         (((s0.sp - 2400#64) + 1496#64 + 32#64) ↦₆₄ w32) ∗
         (((s0.sp - 2400#64) + 1496#64 + 40#64) ↦₆₄ w40) ∗
         (((s0.sp - 2400#64) + 1496#64 + 48#64) ↦₆₄ w48) ∗
         memRegion (s0.sp - 2400#64) 176 ∗ memRegion ((s0.sp - 2400#64) + 184#64) 40 ∗
         memRegion ((s0.sp - 2400#64) + 232#64) 1264 ∗
         vecCapPtrDealloc A.repAlloc ca1 pa1 ∗ vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
         vecCapPtrDealloc A.repAlloc ca3 pa3 ∗ vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
         memRegion pbA optProtoInnerStateSize ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗ memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         statesFromPbJumpTablePlacedAt)
        hfsp_align hca1_lt hpc1 hrun1 hsp1 hx19_1
      refine seq_clean_lscl_st hcl1
        (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) h860) ?_
      intro s2 hpc2 hrun2 _hcl2 ⟨_hvm2, hsp2, hx0_2, hx1_2, hx19_2, hx21_2, hx22_2, hx26_2, hx28_2, htr2⟩
      have h2072 := v3_collapse_232_2072_none (s0.sp - 2400#64)
        noneCap w8 w16 w24 w32 w40 w48 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
      dsimp only [v1_optProtoPolyEncoderWordsAt] at h2072
      have hpre2 :
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          (((s0.sp - 2400#64) + 1496#64) ↦₆₄ noneCap) ∗
          v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
          A.pool lim st s2 ∗
          ((((s0.sp - 2400#64) + 1496#64 + 8#64) ↦₆₄ w8) ∗
           (((s0.sp - 2400#64) + 1496#64 + 16#64) ↦₆₄ w16) ∗
           (((s0.sp - 2400#64) + 1496#64 + 24#64) ↦₆₄ w24) ∗
           (((s0.sp - 2400#64) + 1496#64 + 32#64) ↦₆₄ w32) ∗
           (((s0.sp - 2400#64) + 1496#64 + 40#64) ↦₆₄ w40) ∗
           (((s0.sp - 2400#64) + 1496#64 + 48#64) ↦₆₄ w48) ∗
           memRegion (s0.sp - 2400#64) 176 ∗ memRegion ((s0.sp - 2400#64) + 184#64) 40 ∗
           memRegion ((s0.sp - 2400#64) + 232#64) 1264 ∗
           vecCapPtrDealloc A.repAlloc ca1 pa1 ∗ vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
           vecCapPtrDealloc A.repAlloc ca3 pa3 ∗ vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
           memRegion pbA optProtoInnerStateSize ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗ memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           statesFromPbJumpTablePlacedAt) ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 176 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          memRegion ((s0.sp - 2400#64) + 184#64) 40 ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          memRegion ((s0.sp - 2400#64) + 232#64) 2072 ∗
          vecCapPtrDealloc A.repAlloc ca1 pa1 ∗ vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
          vecCapPtrDealloc A.repAlloc ca3 pa3 ∗ vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s2 ∗ statesFromPbJumpTablePlacedAt := by
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion ((s0.sp - 2400#64) + 232#64) 1264 ∗
           ((((s0.sp - 2400#64) + 1496#64) ↦₆₄ noneCap) ∗
            (((s0.sp - 2400#64) + 1496#64 + 8#64) ↦₆₄ w8) ∗
            (((s0.sp - 2400#64) + 1496#64 + 16#64) ↦₆₄ w16) ∗
            (((s0.sp - 2400#64) + 1496#64 + 24#64) ↦₆₄ w24) ∗
            (((s0.sp - 2400#64) + 1496#64 + 32#64) ↦₆₄ w32) ∗
            (((s0.sp - 2400#64) + 1496#64 + 40#64) ↦₆₄ w40) ∗
            (((s0.sp - 2400#64) + 1496#64 + 48#64) ↦₆₄ w48)) ∗
           memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
           v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
           memRegion ((s0.sp - 2400#64) + 1992#64) 312) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 176 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
           memRegion ((s0.sp - 2400#64) + 184#64) 40 ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
           vecCapPtrDealloc A.repAlloc ca1 pa1 ∗ vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
           vecCapPtrDealloc A.repAlloc ca3 pa3 ∗ vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s2 ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left h2072) (Entails.of_eq (by sep_ac_rfl))
      have h4884 := Variant3dPlacedBudgetAux.v3_ct1Received_err_4884_to_exit_placed (F := F) hA st s0 s2 out pbA
        ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 statesFromPbJumpTablePlacedAt
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx1_2 hx22_2 hx0_2 hx28_2 hx26_2 hx21_2 (htr2.trans htr1)
      refine SepWP.weaken_pre hpre2 (SepWP.mono h4884 ?_)
      intro sf Pf _ _ ⟨evs, hevs, hPf, hsp_f, hcs_f, htr_f⟩
      refine ⟨⟨evs, ?_, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩, hsp_f, hcs_f, htr_f⟩
      dsimp only [Ct1ReceivedTailEnv]
      rw [huc]
      exact hevs
    | some pbEnc =>
      dsimp only [Option.map_some] at hw0_prop ⊢
      have hfits_enc : FitsEnv M lim st (EncoderFromPbAllocEnv (pbToProtoPolyEncoder pbEnc)) := by
        dsimp only [Ct1ReceivedTailFits] at hfits
        rw [huc] at hfits
        exact hfits
      have h1496 := v3_split_1496_some (s0.sp - 2400#64)
      have h312 : memRegion ((s0.sp - 2400#64) + 1992#64) 312 =
          memRegion ((s0.sp - 2400#64) + 1992#64) 296 ∗
          memRegion ((s0.sp - 2400#64) + 2288#64) 16 :=
        ProofLib.memRegion_split' (b := (s0.sp - 2400#64) + 1992#64) (n := 296) (k := 16)
          (b' := (s0.sp - 2400#64) + 2288#64) rfl (by bv_omega) (by decide)
      rw [h312]
      refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left h1496)) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWP.exists_elim fun e0 => SepWP.exists_elim fun e8 =>
        SepWP.exists_elim fun e16 => SepWP.exists_elim fun e24 =>
        SepWP.exists_elim fun e32 => SepWP.exists_elim fun e40 =>
        SepWP.exists_elim fun e48 => SepWP.exists_elim fun v224 =>
        SepWP.exists_elim fun v200 => SepWP.exists_elim fun v192 =>
        SepWP.exists_elim fun v184 => SepWP.exists_elim fun v176 =>
        SepWP.exists_elim fun v96 => SepWP.exists_elim fun v64 => ?_
      have h1496_w0 :
          v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) w0 w8 w16 w24 w32 w40 w48 =
          (((s0.sp - 2400#64) + 1496#64) ↦₆₄ w0) ∗
          ((((s0.sp - 2400#64) + 1496#64 + 8#64) ↦₆₄ w8) ∗
           (((s0.sp - 2400#64) + 1496#64 + 16#64) ↦₆₄ w16) ∗
           (((s0.sp - 2400#64) + 1496#64 + 24#64) ↦₆₄ w24) ∗
           (((s0.sp - 2400#64) + 1496#64 + 32#64) ↦₆₄ w32) ∗
           (((s0.sp - 2400#64) + 1496#64 + 40#64) ↦₆₄ w40) ∗
           (((s0.sp - 2400#64) + 1496#64 + 48#64) ↦₆₄ w48)) := rfl
      rw [h1496_w0]
      have h860 := v3cr_post_uc_860_ok_some_placed_budget A lim st (ext := ext) s1
        (s0.sp - 2400#64) out pbA
        ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep w0 v176 v224
        ((((s0.sp - 2400#64) + 1496#64 + 8#64) ↦₆₄ w8) ∗
         (((s0.sp - 2400#64) + 1496#64 + 16#64) ↦₆₄ w16) ∗
         (((s0.sp - 2400#64) + 1496#64 + 24#64) ↦₆₄ w24) ∗
         (((s0.sp - 2400#64) + 1496#64 + 32#64) ↦₆₄ w32) ∗
         (((s0.sp - 2400#64) + 1496#64 + 40#64) ↦₆₄ w40) ∗
         (((s0.sp - 2400#64) + 1496#64 + 48#64) ↦₆₄ w48) ∗
         memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗
         memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗ (((s0.sp - 2400#64) + 96#64) ↦₆₄ v96) ∗
         memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
         (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ v192) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
         memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
         v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) e0 e8 e16 e24 e32 e40 e48 ∗
         memRegion ((s0.sp - 2400#64) + 296#64) 1096 ∗ memRegion ((s0.sp - 2400#64) + 1392#64) 104 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
         memRegion ((s0.sp - 2400#64) + 1992#64) 296 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
         v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
           ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
         v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc))
           w0 w8 w16 w24 w32 w40 w48 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA 112 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion (pbA + 168#64) 56 ∗ statesFromPbJumpTablePlacedAt)
        hfsp_align hca1_lt hw0_prop hpc1 hrun1 hsp1 hx19_1 hx23_1 hx25_1 hx27_1
      refine seq_clean_lscl_st hcl1
        (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) h860) ?_
      intro s2 hpc2 hrun2 hcl2 ⟨_hvm2, hsp2, hx0_2, hx1_2, hx8_2, hx19_2, hx21_2, hx22_2,
        hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, htr2⟩
      have h924 := Variant3dPlacedBudget.v3_ct1Received_some_enc_924_placed_sepWP (F := F) hA hEnc st s0 s2 hcl2 out pbA u ucSt pbEnc
        ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
        w0 w8 w16 w24 w32 w40 w48 e0 e8 e16 e24 e32 e40 e48 v64 v96 v184 v192 v200
        statesFromPbJumpTablePlacedAt hfits_enc huc (hpts pbEnc rfl) hsp0_align hpc2 hrun2 hsp2
        hx0_2 hx1_2 hx8_2 hx19_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
        (htr2.trans htr1)
      refine SepWP.weaken_pre (Entails.of_eq (by rw [h1496_w0]; sep_ac_rfl))
        (SepWP.mono h924 fun sf Pf _ _ ⟨evs, henv, hPf, hsp_f, hcs_f, htr_f⟩ => ?_)
      refine ⟨⟨evs, ?_, hPf⟩, hsp_f, hcs_f, htr_f⟩
      dsimp only [Ct1ReceivedTailEnv]
      rw [huc]
      exact henv

theorem v3_ct1Received_post_uc_860_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (hEnc : EncoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (out pbA : BitVec 64)
    (u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.EkSentCt1Received)
    (optEnc : Option PolynomialEncoder)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (onPanic : State → SepProp → Prop)
    (hpts : ∀ pbEnc, optEnc = some pbEnc → ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hfits : Ct1ReceivedTailFits M lim st F u optEnc)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 860#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx25_1 : s1.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
        ekSentCt1ReceivedResultAt A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64)
          (ekSentCt1ReceivedFromPb (spqrAuthApi F) u) ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA 112 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (optEnc.map pbToProtoPolyEncoder)
          w0 w8 w16 w24 w32 w40 w48 ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          Ct1ReceivedTailEnv F u optEnc evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (CryptoVerification.LibsignalSpqrV1.States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ct1Received { uc := some u, sendingEk := optEnc }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      onPanic :=
  SepWPp.of_sepWP_ret
    (v3_ct1Received_post_uc_860_placed_sepWP hA hEnc st s0 s1 hcl1 out pbA u optEnc
      w0 w8 w16 w24 w32 w40 w48 hpts hfits hsp0_align hpc1 hrun1 hsp1
      hx19_1 hx23_1 hx25_1 hx27_1 htr1)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3PlacedBudgetAux
