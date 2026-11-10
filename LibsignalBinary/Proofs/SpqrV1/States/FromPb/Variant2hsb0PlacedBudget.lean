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
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsaPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb0
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 2 (`HeaderSent`) — Part B0

Relocatable Block-`333` `FreeOnlyEvs` error epilogues (`+4392`, `+4396`), bad-`ptsNeeded`
cleanup (`+604..+688`), and `Unchunked::EkSent` validation error cleanup (`+4660..+4748`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb0PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_333 blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_333 ls_blockPlacement_base lsmpl lsρ withMemEq)
open CryptoVerification.LibsignalSpqrV1
  (Error ProtoAuthenticator ProtoPolynomialDecoder ProtoPolynomialEncoder V1State)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop
  (DropProtoPolyEncoderGhost cap_add_one_beq_zero_false chunkedStatesSize dropStack48
   vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly (protoPolynomialEncoderAt protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved collapse_step0 collapse_top resultChunkedStatesAt spqrErrorByte
   stackAt_encoderFromPb_split_allocHook statesFromPbSavedCells statesFromPbStack
   v1_optProtoAuthHeap v1_optProtoPolyEncoderAt_pack_some v1_optProtoPolyEncoderHeap
   v1_optProtoPolyEncoderHeap_extract_w0 v1_optProtoPolyEncoderWordsAt
   v1_optProtoPolyEncoderWordsAt_entails_56 v1_stackAt_encoder_split_dropStack48
   v2hs_memRegion_976_56_to_1032 v2hs_optProtoAuthHeap_some_dealloc
   v2hs_optProtoDecoderHeap v2hs_optProtoDecoderWordsAt v2hs_optProtoUcHeap
   v2hs_optProtoUcHeap_some_none_dealloc v2hs_optProtoUcHeap_some_some_dealloc
   v2hs_ucWordsAt v2hs_ucWordsAt_entails_80)
open CryptoVerification.SpqrV1.Unchunked (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs seq_clean_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (FromPbAllocHooksBudget seq_clean_lscl_st v1_deallocFreeOnly_ok_at_statesFromPb_placed
   v1_drop_glue_proto_poly_encoder_mem_ok_at_statesFromPb_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

private theorem blk333_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_333.text = true := by
  decide +kernel

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

private theorem entails_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (hent : ∀ sc : State, sc = s → P ⊢ P_mid sc)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) :=
  SepWP.weaken_pre (hent s rfl) h

/-! ## `+4396 -> s0.x30` and `+4392 -> s0.x30` Shared Epilogues -/

/-- Budget-threaded relocatable shared error epilogue from `+4396 -> s0.x30`:
    drops `sendingHdr` (`optEnc` at `fsp + 976..1032`) via Block `271` and `receivingCt1`
    (`optDec` at `fsp + 1032..1072`) via `+4420 -> s0.x30` under `FreeOnlyEvs`, writes
    `Err(err)` to `out`, restores callee-saved registers and stack, and returns. -/
theorem v2hs_epilogue_4396_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (out : BitVec 64) (err : Error)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4396#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = (spqrErrorByte err).zeroExtend 64) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 976 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  cases optEnc with
  | none =>
    dsimp only [v1_optProtoPolyEncoderHeap]
    have hpull :
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 976 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
          ⌜w0 = noneCap⌝ ∗
          v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s ∗ Rest) =
        (⌜w0 = noneCap⌝ ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            memRegion (s0.sp - 2400#64) 976 ∗
            v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
            v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
            statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s ∗ Rest)) := by
      sep_ac_rfl
    rw [hpull]
    apply SepWP.pure_elim; intro hw0; subst hw0
    refine seq_clean_st (mid := lsmpl.base 333 + 4420#64)
      (P_mid := fun sm =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1032 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st sm ∗ Rest)
      (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d_w0 ∧
        sm.readReg64 .x23 = (spqrErrorByte err).zeroExtend 64 ∧ TraceCalleeSaved sm s0)
      ?_ ?_
    · have h56 := v1_optProtoPolyEncoderWordsAt_entails_56
        (s0.sp - 2400#64 + 976#64) noneCap w8 w16 w24 w32 w40 w48
      have h1032 := Entails.trans (sepConj_mono_right h56)
        (v2hs_memRegion_976_56_to_1032 (s0.sp - 2400#64))
      dsimp only [v1_optProtoPolyEncoderWordsAt, noneCap, BitVec.ofNat_eq_ofNat] at h1032 hpc ⊢
      rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
      change s.pc = (blkPl_333).base + 4396#64 at hpc
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4420#64) s _ _
      wp_steps_sync_333 ((blkPl_333).base + 4420#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc]
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 976 ∗
           (((s0.sp - 2400#64 + 976#64) ↦₆₄ 0xffffffffffffffff#64) ∗
            ((s0.sp - 2400#64 + 976#64 + 8#64) ↦₆₄ w8) ∗
            ((s0.sp - 2400#64 + 976#64 + 16#64) ↦₆₄ w16) ∗
            ((s0.sp - 2400#64 + 976#64 + 24#64) ↦₆₄ w24) ∗
            ((s0.sp - 2400#64 + 976#64 + 32#64) ↦₆₄ w32) ∗
            ((s0.sp - 2400#64 + 976#64 + 40#64) ↦₆₄ w40) ∗
            ((s0.sp - 2400#64 + 976#64 + 48#64) ↦₆₄ w48))) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
           v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
           memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           A.pool lim st sc ∗ Rest) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left h1032) (Entails.of_eq (by sep_ac_rfl))
      · wp_done
    · intro sm hpcm hrunm ⟨hspm, hx19m, hx22m, hx23m, htrm⟩
      exact Variant2hsaPlacedBudget.v2hs_epilogue_4420_ret_placed (F := F) hA.toPlacedBudget
        st s0 sm out err optDec d_w0 d_w8 d_w16 d_w24 d_w32 Rest
        hsp0_align hpcm hrunm hspm hx19m hx22m hx23m htrm
  | some pbEnc =>
    have hex := v1_optProtoPolyEncoderHeap_extract_w0 A.repAlloc (some pbEnc) w0 w8 w16 w24 w32 w40 w48
    dsimp only at hex
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hex)))) ?_
    have hpull :
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 976 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
          (⌜w0.toNat < 2 ^ 63⌝ ∗
            v1_optProtoPolyEncoderHeap A.repAlloc (some pbEnc) w0 w8 w16 w24 w32 w40 w48) ∗
          v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s ∗ Rest) =
        (⌜w0.toNat < 2 ^ 63⌝ ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            memRegion (s0.sp - 2400#64) 976 ∗
            v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
            v1_optProtoPolyEncoderHeap A.repAlloc (some pbEnc) w0 w8 w16 w24 w32 w40 w48 ∗
            v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
            statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s ∗ Rest)) := by
      sep_ac_rfl
    rw [hpull]
    apply SepWP.pure_elim; intro hw0_lt
    have hcmn_f := cap_add_one_beq_zero_false hw0_lt
    have hpack := v1_optProtoPolyEncoderAt_pack_some A.repAlloc (s0.sp - 2400#64 + 976#64) pbEnc
      w0 w8 w16 w24 w32 w40 w48
    have h1424 : s0.sp - 2400#64 + 976#64 = s0.sp - 1424#64 := by bv_omega
    refine seq_clean_lscl_st hcl
      (mid := lsmpl.base 271)
      (P_mid := fun sm =>
        protoPolynomialEncoderAt A.repAlloc (s0.sp - 1424#64) pbEnc ∗
        A.pool lim st sm ∗
        stackAt (s0.sp - 2400#64) dropStack48 ∗
        (memRegion (s0.sp - 2400#64 - 5152#64) 1008 ∗
          memRegion (s0.sp - 2400#64) 976 ∗
          v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x0 = s0.sp - 1424#64 ∧
        sm.readReg64 .lr = (blkPl_333).base + 4420#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d_w0 ∧
        sm.readReg64 .x23 = (spqrErrorByte err).zeroExtend 64 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · dsimp only [v1_optProtoPolyEncoderWordsAt, BitVec.ofNat_eq_ofNat] at hpc ⊢
      rw [← ls_blockPlacement_base (i := 333)] at hpc
      change s.pc = (blkPl_333).base + 4396#64 at hpc
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsmpl.base 271) s _ _
      wp_steps_sync_333 (lsmpl.base 271)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc, v1_stackAt_encoder_split_dropStack48 (s0.sp - 2400#64), ← h1424]
        refine Entails.trans (Entails.of_eq (show _ =
          (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A.repAlloc (some pbEnc) w0 w8 w16 w24 w32 w40 w48) ∗
          (A.pool lim st sc ∗ stackAt (s0.sp - 2400#64) dropStack48 ∗
           (memRegion (s0.sp - 2400#64 - 5152#64) 1008 ∗
            memRegion (s0.sp - 2400#64) 976 ∗
            v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
            statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)) by
          dsimp only [v1_optProtoPolyEncoderWordsAt]; sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hpack) (Entails.of_eq (by sep_ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hlr_2, hx19_2, hx22_2, hx23_2, htr2⟩
      have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hfsp_align
      have hdrop := v1_drop_glue_proto_poly_encoder_mem_ok_at_statesFromPb_placed hA hcl2
      simp only [withMemEq, dropProtoPolyEncoderSpec] at hdrop
      refine seq_clean_evs (mid := lsmpl.base 333 + 4420#64)
        (P_evs := fun evs1 sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 1032 ∗
          v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          A.pool lim (M.stepEvents evs1 st) sm ∗ Rest)
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = d_w0 ∧
          sm.readReg64 .x23 = (spqrErrorByte err).zeroExtend 64 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · rw [← ls_blockPlacement_base (i := 333)]
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4420#64) s2 _ _
        rw [show stackAt (s0.sp - 2400#64) dropStack48 = stackAt s2.sp dropStack48 from hsp2 ▸ rfl]
        wp_call hdrop ((⟨s0.sp - 1424#64, pbEnc⟩ : DropProtoPolyEncoderGhost), st)
        rw [hlr_2] at *
        have hevs_w : FreeOnlyEvs w := ‹_›
        have hacp_w : AllocCallPreserved s2 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have hsp_sf : sf.sp = s0.sp - 2400#64 := (‹sf.sp = s2.sp›).trans hsp2
        have hx19_sf : sf.readReg64 .x19 = out :=
          (‹sf.readReg64 (Reg.gpr 19#5) = s2.readReg64 (Reg.gpr 19#5)›).trans hx19_2
        have hx22_sf : sf.readReg64 .x22 = d_w0 :=
          (‹sf.readReg64 (Reg.gpr 22#5) = s2.readReg64 (Reg.gpr 22#5)›).trans hx22_2
        have hx23_sf : sf.readReg64 .x23 = (spqrErrorByte err).zeroExtend 64 :=
          (‹sf.readReg64 (Reg.gpr 23#5) = s2.readReg64 (Reg.gpr 23#5)›).trans hx23_2
        have htr_sf : sf.trace = s0.trace := hacp_w.2.1.trans htr2.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          (‹calleeSavedVRegs sf = calleeSavedVRegs s2›).trans htr2.2
        refine SepWP.done (by assumption) (by assumption)
          ⟨w, hevs_w, ?_, hsp_sf, hx19_sf, hx22_sf, hx23_sf, htr_sf, hvregs_sf⟩
        rw [hsp2, v1_stackAt_encoder_split_dropStack48 (s0.sp - 2400#64), ← h1424]
        dsimp only [protoPolynomialEncoderSize]
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 976 ∗ memRegion (s0.sp - 2400#64 + 976#64) 56) ∗
          (memRegion (s0.sp - 2400#64 - 5152#64) 1008 ∗
            stackAt (s0.sp - 2400#64) dropStack48 ∗
            v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
            statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
            A.pool lim (M.stepEvents w st) sf ∗ Rest) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left (v2hs_memRegion_976_56_to_1032 (s0.sp - 2400#64)))
          (Entails.of_eq (by sep_ac_rfl))
      · intro evs1 s3 hevs1 hpc3 hrun3 ⟨hsp3, hx19_3, hx22_3, hx23_3, htr3⟩
        have h4420 := Variant2hsaPlacedBudget.v2hs_epilogue_4420_ret_placed (F := F)
          hA.toPlacedBudget (M.stepEvents evs1 st)
          s0 s3 out err optDec d_w0 d_w8 d_w16 d_w24 d_w32 Rest
          hsp0_align hpc3 hrun3 hsp3 hx19_3 hx22_3 hx23_3 htr3
        refine SepWP.mono h4420 fun sf Pf _ _ ⟨evs2, hevs2, hPf, hspf, hcsf, htrf⟩ => ?_
        refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hspf, hcsf, htrf⟩
        simpa only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append] using hPf

/-- Budget-threaded relocatable `Err(StateDecode)` epilogue from `+4392 -> s0.x30`:
    sets `w23 = spqrErrorByte .stateDecode` (`0#64`) and enters `+4396`. -/
theorem v2hs_epilogue_4392_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4392#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 976 ∗
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
  refine seq_clean_lscl_st hcl (mid := lsmpl.base 333 + 4396#64)
    (P_mid := fun sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 976 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st sm ∗ Rest)
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d_w0 ∧
      sm.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64 ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
    change s.pc = (blkPl_333).base + 4392#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4396#64) s _ _
    wp_steps_sync_333 ((blkPl_333).base + 4396#64)
    simp only [State.setMem_setMem]
    wp_done
  · intro sm hpcm hrunm hclm ⟨hspm, hx19m, hx22m, hx23m, htrm⟩
    exact v2hs_epilogue_4396_ret_placed (F := F) hA st s0 sm out .stateDecode
      optEnc w0 w8 w16 w24 w32 w40 w48 optDec d_w0 d_w8 d_w16 d_w24 d_w32 Rest
      hclm hsp0_align hpcm hrunm hspm hx19m hx22m hx23m htrm

/-! ## Bad `ptsNeeded` Cleanup (`+604..+688 -> +4396 -> s0.x30`) -/

theorem v2hs_err_uc_628_to_644_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out u8 u40 u32 d_w0 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 628#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = u32) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = u8) (hx22 : s.readReg64 .x22 = d_w0) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 644#64) s
      (((fsp + 928#64) ↦₆₄ u40) ∗ vecCapPtrDealloc A.repAlloc u32 u40 ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ ((fsp + 928#64) ↦₆₄ u40) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = u8 ∧
          sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0) := by
  have hdealloc_fo := v1_deallocFreeOnly_ok_at_statesFromPb_placed hA
  rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
  change s.pc = (blkPl_333).base + 628#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 644#64) s _ _
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  by_cases hcap : (u32 == 0#64) = true
  · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 644#64)
    simp only [State.setMem_setMem]
    wp_done
  · have hcap_f : (u32 == 0#64) = false := Bool.eq_false_iff.mpr hcap
    simp only [hcap_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    apply sepWP_evs_dealloc u32.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (u40, u32.toNat, 1, st)
    have hacp : AllocCallPreserved s sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_f : sf.sp = fsp := (‹sf.sp = s.sp›).trans hsp
    have hx19_f : sf.readReg64 .x19 = out :=
      (‹sf.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5)›).trans hx19
    have hx20_f : sf.readReg64 .x20 = u8 :=
      (‹sf.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5)›).trans hx20
    have hx22_f : sf.readReg64 .x22 = d_w0 :=
      (‹sf.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5)›).trans hx22
    have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      (‹calleeSavedVRegs sf = calleeSavedVRegs s›).trans htr.2
    exact SepWP.done (by assumption) (by assumption)
      ⟨Entails.of_eq (by rw [hsp]; sep_ac_rfl), hsp_f, hx19_f, hx20_f, hx22_f, htr_sf, hvregs_sf⟩

theorem v2hs_err_uc_644_to_664_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out u8 u56 u64 d_w0 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 644#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = u8) (hx22 : s.readReg64 .x22 = d_w0) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 664#64) s
      (((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗
        vecCapPtrDealloc A.repAlloc u56 u64 ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ ((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = u8 ∧
          sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0) := by
  have hdealloc_fo := v1_deallocFreeOnly_ok_at_statesFromPb_placed hA
  rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
  change s.pc = (blkPl_333).base + 644#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 664#64) s _ _
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  by_cases hcap : (u56 == 0#64) = true
  · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 664#64)
    simp only [State.setMem_setMem]
    wp_done
  · have hcap_f : (u56 == 0#64) = false := Bool.eq_false_iff.mpr hcap
    simp only [hcap_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    apply sepWP_evs_dealloc u56.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (u64, u56.toNat, 1, st)
    have hacp : AllocCallPreserved s sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_f : sf.sp = fsp := (‹sf.sp = s.sp›).trans hsp
    have hx19_f : sf.readReg64 .x19 = out :=
      (‹sf.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5)›).trans hx19
    have hx20_f : sf.readReg64 .x20 = u8 :=
      (‹sf.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5)›).trans hx20
    have hx22_f : sf.readReg64 .x22 = d_w0 :=
      (‹sf.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5)›).trans hx22
    have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      (‹calleeSavedVRegs sf = calleeSavedVRegs s›).trans htr.2
    exact SepWP.done (by assumption) (by assumption)
      ⟨Entails.of_eq (by rw [hsp]; sep_ac_rfl), hsp_f, hx19_f, hx20_f, hx22_f, htr_sf, hvregs_sf⟩

theorem v2hs_err_uc_664_to_4396_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out u8 u16 d_w0 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 664#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = u8) (hx22 : s.readReg64 .x22 = d_w0) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4396#64) s
      (((fsp + 904#64) ↦₆₄ u16) ∗ vecCapPtrDealloc A.repAlloc u8 u16 ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ ((fsp + 904#64) ↦₆₄ u16) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = d_w0 ∧
          sm.readReg64 .x23 = (spqrErrorByte .msgDecode).zeroExtend 64 ∧ TraceCalleeSaved sm s0) := by
  have hdealloc_fo := v1_deallocFreeOnly_ok_at_statesFromPb_placed hA
  rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
  change s.pc = (blkPl_333).base + 664#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4396#64) s _ _
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  by_cases hcap : (u8 == 0#64) = true
  · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 4396#64)
    simp only [State.setMem_setMem]
    wp_done
  · have hcap_f : (u8 == 0#64) = false := Bool.eq_false_iff.mpr hcap
    simp only [hcap_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    apply sepWP_evs_dealloc u8.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (u16, u8.toNat, 1, st)
    have hacp : AllocCallPreserved s sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      (‹calleeSavedVRegs sf = calleeSavedVRegs s›).trans htr.2
    wp_steps_sync_333 ((blkPl_333).base + 4396#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by rw [hsp]; sep_ac_rfl) ?_
    wp_done

theorem v2hs_err_uc_604_to_4396_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out d_w0 : BitVec 64)
    (optUc : Option V1State.Unchunked.EkSent)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 604#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4396#64) s
      (v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v2hs_optProtoUcHeap A.repAlloc optUc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion (fsp + 896#64) 80 ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = d_w0 ∧
          sm.readReg64 .x23 = (spqrErrorByte .msgDecode).zeroExtend 64 ∧ TraceCalleeSaved sm s0) := by
  cases optUc with
  | none =>
    dsimp only [v2hs_optProtoUcHeap]
    have hpull :
        (v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
          ⌜u8 = noneCap⌝ ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) =
        (⌜u8 = noneCap⌝ ∗
          (v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
            A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)) := by
      sep_ac_rfl
    rw [hpull]
    apply SepWP.pure_elim; intro hu8; subst hu8
    have h80 := v2hs_ucWordsAt_entails_80
      (fsp + 896#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80
    dsimp only [v2hs_ucWordsAt, noneCap, BitVec.ofNat_eq_ofNat] at h80 hpc ⊢
    rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
    change s.pc = (blkPl_333).base + 604#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4396#64) s _ _
    apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 4396#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      simp only [arm64_norm] at h80 ⊢
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 896#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((fsp + 904#64) ↦₆₄ u16) ∗
         ((fsp + 912#64) ↦₆₄ u24) ∗ ((fsp + 920#64) ↦₆₄ u32) ∗
         ((fsp + 928#64) ↦₆₄ u40) ∗ ((fsp + 936#64) ↦₆₄ u48) ∗
         ((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗
         ((fsp + 960#64) ↦₆₄ u72) ∗ ((fsp + 968#64) ↦₆₄ u80)) ∗
        (A.pool lim st sc ∗ stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left h80) (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  | some uc =>
    dsimp only [v2hs_optProtoUcHeap]
    have h80 := v2hs_ucWordsAt_entails_80 (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
    cases hauth : uc.auth with
    | none =>
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_left
          (v2hs_optProtoUcHeap_some_none_dealloc A.repAlloc uc.dk
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 uc.epoch))) ?_
      have hpull :
          (v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
            (⌜u8.toNat < 2 ^ 63 ∧ u32 = noneCap⌝ ∗ vecCapPtrDealloc A.repAlloc u8 u16) ∗
            A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) =
          (⌜u8.toNat < 2 ^ 63 ∧ u32 = noneCap⌝ ∗
            (v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
              vecCapPtrDealloc A.repAlloc u8 u16 ∗
              A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)) := by
        sep_ac_rfl
      rw [hpull]
      apply SepWP.pure_elim; rintro ⟨hu8_lt, hu32⟩; subst hu32
      have hu8_ne := cap_add_one_beq_zero_false hu8_lt
      have h80' := v2hs_ucWordsAt_entails_80
        (fsp + 896#64) u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80
      let RestWords664 : SepProp :=
        ((fsp + 896#64) ↦₆₄ u8) ∗ ((fsp + 912#64) ↦₆₄ u24) ∗
        ((fsp + 920#64) ↦₆₄ noneCap) ∗ ((fsp + 928#64) ↦₆₄ u40) ∗ ((fsp + 936#64) ↦₆₄ u48) ∗
        ((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗ ((fsp + 960#64) ↦₆₄ u72) ∗
        ((fsp + 968#64) ↦₆₄ u80) ∗ Frame
      refine seq_clean_st (mid := lsmpl.base 333 + 664#64)
        (P_mid := fun sm =>
          ((fsp + 904#64) ↦₆₄ u16) ∗ vecCapPtrDealloc A.repAlloc u8 u16 ∗
          A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ RestWords664)
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = u8 ∧
          sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0)
        ?_ ?_
      · dsimp +zetaDelta only [v2hs_ucWordsAt, RestWords664, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
        rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
        change s.pc = (blkPl_333).base + 604#64 at hpc
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 664#64) s _ _
        wp_steps_sync_333 ((blkPl_333).base + 664#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx20_1, hx22_1, htr1⟩
        have h664 := v2hs_err_uc_664_to_4396_placed hA st s0 s1 fsp out u8 u16 d_w0 RestWords664
          hfsp_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx22_1 htr1
        refine SepWP.mono h664 fun sm Pm _ _ ⟨evs, hevs, hPm, hspm, hx19m, hx22m, hx23m, htrm⟩ => ?_
        refine ⟨evs, hevs, Entails.trans hPm ?_, hspm, hx19m, hx22m, hx23m, htrm⟩
        dsimp +zetaDelta only [v2hs_ucWordsAt, RestWords664] at h80' ⊢
        simp only [arm64_norm] at h80' ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (((fsp + 896#64) ↦₆₄ u8) ∗ ((fsp + 904#64) ↦₆₄ u16) ∗ ((fsp + 912#64) ↦₆₄ u24) ∗
           ((fsp + 920#64) ↦₆₄ noneCap) ∗ ((fsp + 928#64) ↦₆₄ u40) ∗ ((fsp + 936#64) ↦₆₄ u48) ∗
           ((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗ ((fsp + 960#64) ↦₆₄ u72) ∗
           ((fsp + 968#64) ↦₆₄ u80)) ∗
          (A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left h80') (Entails.of_eq (by sep_ac_rfl))
    | some auth =>
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_left
          (v2hs_optProtoUcHeap_some_some_dealloc A.repAlloc uc.dk auth
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 uc.epoch))) ?_
      have hpull :
          (v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
            (⌜u8.toNat < 2 ^ 63 ∧ u32.toNat < 2 ^ 63⌝ ∗
              vecCapPtrDealloc A.repAlloc u8 u16 ∗
              vecCapPtrDealloc A.repAlloc u32 u40 ∗
              vecCapPtrDealloc A.repAlloc u56 u64) ∗
            A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) =
          (⌜u8.toNat < 2 ^ 63 ∧ u32.toNat < 2 ^ 63⌝ ∗
            (v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
              vecCapPtrDealloc A.repAlloc u8 u16 ∗
              vecCapPtrDealloc A.repAlloc u32 u40 ∗
              vecCapPtrDealloc A.repAlloc u56 u64 ∗
              A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)) := by
        sep_ac_rfl
      rw [hpull]
      apply SepWP.pure_elim; rintro ⟨hu8_lt, hu32_lt⟩
      have hu8_ne := cap_add_one_beq_zero_false hu8_lt
      have hu32_ne := cap_add_one_beq_zero_false hu32_lt
      let RestWords628 : SepProp :=
        ((fsp + 896#64) ↦₆₄ u8) ∗ ((fsp + 904#64) ↦₆₄ u16) ∗ ((fsp + 912#64) ↦₆₄ u24) ∗
        ((fsp + 920#64) ↦₆₄ u32) ∗ ((fsp + 936#64) ↦₆₄ u48) ∗
        ((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗ ((fsp + 960#64) ↦₆₄ u72) ∗
        ((fsp + 968#64) ↦₆₄ u80) ∗
        vecCapPtrDealloc A.repAlloc u56 u64 ∗ vecCapPtrDealloc A.repAlloc u8 u16 ∗ Frame
      refine seq_clean_st (mid := lsmpl.base 333 + 628#64)
        (P_mid := fun sm =>
          ((fsp + 928#64) ↦₆₄ u40) ∗ vecCapPtrDealloc A.repAlloc u32 u40 ∗
          A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ RestWords628)
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x1 = u32 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = u8 ∧ sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0)
        ?_ ?_
      · dsimp +zetaDelta only [v2hs_ucWordsAt, RestWords628, BitVec.ofNat_eq_ofNat] at hpc ⊢
        rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
        change s.pc = (blkPl_333).base + 604#64 at hpc
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 628#64) s _ _
        wp_steps_sync_333 ((blkPl_333).base + 628#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · intro s1 hpc1 hrun1 ⟨hsp1, hx1_1, hx19_1, hx20_1, hx22_1, htr1⟩
        refine seq_clean_evs (mid := lsmpl.base 333 + 644#64)
          (P_evs := fun evs1 sm =>
            ((fsp + 928#64) ↦₆₄ u40) ∗
            A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ RestWords628)
          (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧
            sm.readReg64 .x20 = u8 ∧ sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0)
          (v2hs_err_uc_628_to_644_placed hA st s0 s1 fsp out u8 u40 u32 d_w0 RestWords628
            hfsp_align hpc1 hrun1 hsp1 hx1_1 hx19_1 hx20_1 hx22_1 htr1) ?_
        intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, hx22_2, htr2⟩
        let RestWords644 : SepProp :=
          ((fsp + 896#64) ↦₆₄ u8) ∗ ((fsp + 904#64) ↦₆₄ u16) ∗ ((fsp + 912#64) ↦₆₄ u24) ∗
          ((fsp + 920#64) ↦₆₄ u32) ∗ ((fsp + 928#64) ↦₆₄ u40) ∗ ((fsp + 936#64) ↦₆₄ u48) ∗
          ((fsp + 960#64) ↦₆₄ u72) ∗ ((fsp + 968#64) ↦₆₄ u80) ∗
          vecCapPtrDealloc A.repAlloc u8 u16 ∗ Frame
        have hre644 :
            (((fsp + 928#64) ↦₆₄ u40) ∗
              A.pool lim (M.stepEvents evs1 st) s2 ∗ stackAt fsp allocHookStack ∗ RestWords628) =
            (((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗
              vecCapPtrDealloc A.repAlloc u56 u64 ∗
              A.pool lim (M.stepEvents evs1 st) s2 ∗ stackAt fsp allocHookStack ∗ RestWords644) := by
          dsimp +zetaDelta only [RestWords628, RestWords644]; sep_ac_rfl
        refine SepWP.weaken_pre (Entails.of_eq hre644) ?_
        refine seq_clean_evs (mid := lsmpl.base 333 + 664#64)
          (P_evs := fun evs2 sm =>
            ((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗
            A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) sm ∗
            stackAt fsp allocHookStack ∗ RestWords644)
          (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧
            sm.readReg64 .x20 = u8 ∧ sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0)
          (v2hs_err_uc_644_to_664_placed hA (M.stepEvents evs1 st) s0 s2 fsp out u8 u56 u64 d_w0
            RestWords644 hfsp_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx22_2 htr2) ?_
        intro evs2 s3 hevs2 hpc3 hrun3 ⟨hsp3, hx19_3, hx20_3, hx22_3, htr3⟩
        let RestWords664 : SepProp :=
          ((fsp + 896#64) ↦₆₄ u8) ∗ ((fsp + 912#64) ↦₆₄ u24) ∗
          ((fsp + 920#64) ↦₆₄ u32) ∗ ((fsp + 928#64) ↦₆₄ u40) ∗ ((fsp + 936#64) ↦₆₄ u48) ∗
          ((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗ ((fsp + 960#64) ↦₆₄ u72) ∗
          ((fsp + 968#64) ↦₆₄ u80) ∗ Frame
        have hre664 :
            (((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗
              A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s3 ∗
              stackAt fsp allocHookStack ∗ RestWords644) =
            (((fsp + 904#64) ↦₆₄ u16) ∗ vecCapPtrDealloc A.repAlloc u8 u16 ∗
              A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s3 ∗
              stackAt fsp allocHookStack ∗ RestWords664) := by
          dsimp +zetaDelta only [RestWords644, RestWords664]; sep_ac_rfl
        refine SepWP.weaken_pre (Entails.of_eq hre664) ?_
        have h664 := v2hs_err_uc_664_to_4396_placed hA (M.stepEvents evs2 (M.stepEvents evs1 st))
          s0 s3 fsp out u8 u16 d_w0 RestWords664
          hfsp_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx22_3 htr3
        refine SepWP.mono h664 fun sm Pm _ _ ⟨evs3, hevs3, hPm, hspm, hx19m, hx22m, hx23m, htrm⟩ => ?_
        refine ⟨(evs1 ++ evs2) ++ evs3, (hevs1.append hevs2).append hevs3, ?_,
          hspm, hx19m, hx22m, hx23m, htrm⟩
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        refine Entails.trans hPm ?_
        dsimp +zetaDelta only [v2hs_ucWordsAt, RestWords664] at h80 ⊢
        simp only [arm64_norm] at h80 ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (((fsp + 896#64) ↦₆₄ u8) ∗ ((fsp + 904#64) ↦₆₄ u16) ∗ ((fsp + 912#64) ↦₆₄ u24) ∗
           ((fsp + 920#64) ↦₆₄ u32) ∗ ((fsp + 928#64) ↦₆₄ u40) ∗ ((fsp + 936#64) ↦₆₄ u48) ∗
           ((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗ ((fsp + 960#64) ↦₆₄ u72) ∗
           ((fsp + 968#64) ↦₆₄ u80)) ∗
          (A.pool lim (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st))) sm ∗
            stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left h80) (Entails.of_eq (by sep_ac_rfl))

theorem v2hs_err_uc_604_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (out : BitVec 64)
    (optUc : Option V1State.Unchunked.EkSent)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 604#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 896 ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v2hs_optProtoUcHeap A.repAlloc optUc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .msgDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  rw [stackAt_encoderFromPb_split_allocHook fsp]
  let Frame604 : SepProp :=
    memRegion (fsp - 5152#64) 1056 ∗ memRegion fsp 896 ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hpre604 :
      ((memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack) ∗
        memRegion fsp 896 ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v2hs_optProtoUcHeap A.repAlloc optUc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s ∗ Rest) =
      (v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v2hs_optProtoUcHeap A.repAlloc optUc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame604) := by
    dsimp +zetaDelta only [Frame604, fsp]; sep_ac_rfl
  refine SepWP.weaken_pre (Entails.of_eq hpre604) ?_
  refine Variant2aPlacedBudget.seq_clean_evs_lscl hcl (mid := lsmpl.base 333 + 4396#64)
    (P_evs := fun evs1 sm =>
      memRegion (fsp + 896#64) 80 ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame604)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = d_w0 ∧
      sm.readReg64 .x23 = (spqrErrorByte .msgDecode).zeroExtend 64 ∧ TraceCalleeSaved sm s0)
    (v2hs_err_uc_604_to_4396_placed hA st s0 s fsp out d_w0 optUc
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 Frame604
      hfsp_align hpc hrun hsp hx19 hx22 htr) ?_
  intro evs1 sm hevs1 hpcm hrunm hclm ⟨hspm, hx19m, hx22m, hx23m, htrm⟩
  have h976 : memRegion fsp 896 ∗ memRegion (fsp + 896#64) 80 ⊢ memRegion fsp 976 :=
    collapse_top <| collapse_step0 (Entails.refl _) <| Entails.refl _
  have hpost604 :
      (memRegion (fsp + 896#64) 80 ∗
        A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame604) ⊢
      stackAt fsp encoderFromPbStack ∗
        memRegion fsp 976 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        A.pool lim (M.stepEvents evs1 st) sm ∗ Rest := by
    have hre :
        (memRegion (fsp + 896#64) 80 ∗
          A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame604) =
        (memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack) ∗
        (memRegion fsp 896 ∗ memRegion (fsp + 896#64) 80) ∗
        (v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
         v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A.repAlloc optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (fsp + 1072#64) 1232 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         A.pool lim (M.stepEvents evs1 st) sm ∗ Rest) := by
      dsimp +zetaDelta only [Frame604, fsp]; sep_ac_rfl
    rw [← stackAt_encoderFromPb_split_allocHook fsp] at hre
    refine Entails.trans (Entails.of_eq hre) ?_
    exact Entails.trans (sepConj_mono_right (sepConj_mono_left h976)) (Entails.of_eq (by sep_ac_rfl))
  refine SepWP.weaken_pre hpost604 ?_
  have hret := v2hs_epilogue_4396_ret_placed (F := F) hA (M.stepEvents evs1 st) s0 sm out .msgDecode
    optEnc w0 w8 w16 w24 w32 w40 w48 optDec d_w0 d_w8 d_w16 d_w24 d_w32 Rest
    hclm hsp0_align hpcm hrunm hspm hx19m hx22m hx23m htrm
  refine SepWP.mono hret fun sf Pf _ _ ⟨evs2, hevs2, hPf, hspf, hcsf, htrf⟩ => ?_
  refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hspf, hcsf, htrf⟩
  simpa only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append] using hPf

/-! ## `Unchunked::EkSent` Validation Error Cleanup (`+4660..+4748 -> +6852/+8916 -> +4396`) -/

theorem v2hs_err_dk_8916_to_4396_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out u8 u16 d_w0 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hu8_ne : (u8 == 0#64) = false)
    (hpc : s.pc = lsmpl.base 333 + 8916#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64)
    (hx24 : s.readReg64 .x24 = u8) (hx25 : s.readReg64 .x25 = u16) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4396#64) s
      (((fsp + 200#64) ↦₆₄ noneCap) ∗ vecCapPtrDealloc A.repAlloc u8 u16 ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ ((fsp + 200#64) ↦₆₄ noneCap) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = d_w0 ∧
          sm.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64 ∧ TraceCalleeSaved sm s0) := by
  have hdealloc_fo := v1_deallocFreeOnly_ok_at_statesFromPb_placed hA
  rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
  change s.pc = (blkPl_333).base + 8916#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4396#64) s _ _
  dsimp only [vecCapPtrDealloc, noneCap, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  simp only [hu8_ne, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
  apply sepWP_evs_dealloc u8.toNat 1
  wp_steps_sync_333 (lsρ spqrRustDeallocSym)
  simp only [State.setMem_setMem]
  wp_call hdealloc_fo (u16, u8.toNat, 1, st)
  have hacp : AllocCallPreserved s sf := by
    simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
  have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr.1
  have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
    (‹calleeSavedVRegs sf = calleeSavedVRegs s›).trans htr.2
  wp_steps_sync_333 ((blkPl_333).base + 4396#64)
  simp only [State.setMem_setMem]
  refine align_pre_st (by rw [hsp]; sep_ac_rfl) ?_
  wp_done

theorem v2hs_err_uc_4720_to_4396_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out u8 u16 w176 w200 d_w0 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4720#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx9 : s.readReg64 .x9 = u16) (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = d_w0) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4396#64) s
      (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = d_w0 ∧
          sm.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64 ∧ TraceCalleeSaved sm s0) := by
  by_cases hcap : (u8 == 0#64) = true
  · dsimp only [vecCapPtrDealloc]
    simp only [hcap, ↓reduceIte, emp_sepConj]
    rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
    change s.pc = (blkPl_333).base + 4720#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4396#64) s _ _
    apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 4396#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      have h176 := pointsTo64_entails_memRegion (fsp + 176#64) w176
      have h200 := pointsTo64_entails_memRegion (fsp + 200#64) w200
      refine Entails.trans (Entails.of_eq (show _ =
        ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
        (((fsp + 152#64) ↦₆₄ u8) ∗ A.pool lim st sc ∗ stackAt fsp allocHookStack ∗ Frame) by
        sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono h176 (sepConj_mono_left h200))
        (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  · have hcap_f : (u8 == 0#64) = false := Bool.eq_false_iff.mpr hcap
    refine seq_clean_st (mid := lsmpl.base 333 + 8916#64)
      (P_mid := fun sm =>
        ((fsp + 200#64) ↦₆₄ noneCap) ∗ vecCapPtrDealloc A.repAlloc u8 u16 ∗
        A.pool lim st sm ∗ stackAt fsp allocHookStack ∗
        (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗ Frame))
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = d_w0 ∧
        sm.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64 ∧
        sm.readReg64 .x24 = u8 ∧ sm.readReg64 .x25 = u16 ∧ TraceCalleeSaved sm s0)
      ?_ ?_
    · dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
      rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
      change s.pc = (blkPl_333).base + 4720#64 at hpc
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 8916#64) s _ _
      wp_steps_sync_333 ((blkPl_333).base + 8916#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx22_1, hx23_1, hx24_1, hx25_1, htr1⟩
      have h8916 := v2hs_err_dk_8916_to_4396_placed hA st s0 s1 fsp out u8 u16 d_w0
        (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗ Frame)
        hfsp_align hcap_f hpc1 hrun1 hsp1 hx19_1 hx22_1 hx23_1 hx24_1 hx25_1 htr1
      refine SepWP.mono h8916 fun sm Pm _ _ ⟨evs, hevs, hPm, hspm, hx19m, hx22m, hx23m, htrm⟩ => ?_
      refine ⟨evs, hevs, Entails.trans hPm ?_, hspm, hx19m, hx22m, hx23m, htrm⟩
      have h176 := pointsTo64_entails_memRegion (fsp + 176#64) u16
      have h200 := pointsTo64_entails_memRegion (fsp + 200#64) noneCap
      refine Entails.trans (Entails.of_eq (show _ =
        ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 200#64) ↦₆₄ noneCap) ∗
        (((fsp + 152#64) ↦₆₄ u8) ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono h176 (sepConj_mono_left h200))
        (Entails.of_eq (by sep_ac_rfl))

theorem v2hs_err_uc_4668_to_4692_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out u16 u32 u40 u56 u64 d_w0 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4668#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = u40) (hx9 : s.readReg64 .x9 = u16)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (hx24 : s.readReg64 .x24 = u56) (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4692#64) s
      (vecCapPtrDealloc A.repAlloc u32 u40 ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = fsp ∧ sm.readReg64 .x9 = u16 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = d_w0 ∧ sm.readReg64 .x24 = u56 ∧
          sm.readReg64 .x25 = u64 ∧ TraceCalleeSaved sm s0) := by
  have hdealloc_fo := v1_deallocFreeOnly_ok_at_statesFromPb_placed hA
  rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
  change s.pc = (blkPl_333).base + 4668#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4692#64) s _ _
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  by_cases hcap : (u32 == 0#64) = true
  · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 4692#64)
    simp only [State.setMem_setMem]
    wp_done
  · have hcap_f : (u32 == 0#64) = false := Bool.eq_false_iff.mpr hcap
    simp only [hcap_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    apply sepWP_evs_dealloc u32.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (u40, u32.toNat, 1, st)
    have hacp : AllocCallPreserved s sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      (‹calleeSavedVRegs sf = calleeSavedVRegs s›).trans htr.2
    wp_steps_sync_333 ((blkPl_333).base + 4692#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by rw [hsp]) ?_
    wp_done

theorem v2hs_err_uc_4692_to_4720_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out u16 u56 u64 d_w0 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4692#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx9 : s.readReg64 .x9 = u16) (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = d_w0) (hx24 : s.readReg64 .x24 = u56)
    (hx25 : s.readReg64 .x25 = u64) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4720#64) s
      (vecCapPtrDealloc A.repAlloc u56 u64 ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = fsp ∧ sm.readReg64 .x9 = u16 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0) := by
  have hdealloc_fo := v1_deallocFreeOnly_ok_at_statesFromPb_placed hA
  rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
  change s.pc = (blkPl_333).base + 4692#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4720#64) s _ _
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  by_cases hcap : (u56 == 0#64) = true
  · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 4720#64)
    simp only [State.setMem_setMem]
    wp_done
  · have hcap_f : (u56 == 0#64) = false := Bool.eq_false_iff.mpr hcap
    simp only [hcap_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    apply sepWP_evs_dealloc u56.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (u64, u56.toNat, 1, st)
    have hacp : AllocCallPreserved s sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      (‹calleeSavedVRegs sf = calleeSavedVRegs s›).trans htr.2
    wp_steps_sync_333 ((blkPl_333).base + 4720#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by rw [hsp]) ?_
    wp_done

theorem v2hs_err_uc_4660_to_4720_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out u16 u32 u40 u48 u56 u64 u72 d_w0 : BitVec 64)
    (optAuth : Option ProtoAuthenticator) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4660#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = u40) (hx9 : s.readReg64 .x9 = u16)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (hx24 : s.readReg64 .x24 = u56) (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4720#64) s
      (v1_optProtoAuthHeap A.repAlloc optAuth u32 u40 u48 u56 u64 u72 ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = fsp ∧ sm.readReg64 .x9 = u16 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0) := by
  cases optAuth with
  | none =>
    dsimp only [v1_optProtoAuthHeap]
    apply SepWP.pure_elim; intro hu32; subst hu32
    dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hx26 hpc ⊢
    rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
    change s.pc = (blkPl_333).base + 4660#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4720#64) s _ _
    apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 4720#64)
    simp only [State.setMem_setMem]
    wp_done
  | some auth =>
    refine SepWP.weaken_pre
      (sepConj_mono_left (v2hs_optProtoAuthHeap_some_dealloc A.repAlloc auth u32 u40 u48 u56 u64 u72)) ?_
    have hpull :
        ((⌜u32.toNat < 2 ^ 63⌝ ∗ vecCapPtrDealloc A.repAlloc u32 u40 ∗
            vecCapPtrDealloc A.repAlloc u56 u64) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) =
        (⌜u32.toNat < 2 ^ 63⌝ ∗
          (vecCapPtrDealloc A.repAlloc u32 u40 ∗ vecCapPtrDealloc A.repAlloc u56 u64 ∗
            A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)) := by
      sep_ac_rfl
    rw [hpull]
    apply SepWP.pure_elim; intro hu32_lt
    have hu32_ne := cap_add_one_beq_zero_false hu32_lt
    refine seq_clean_st (mid := lsmpl.base 333 + 4668#64)
      (P_mid := fun sm =>
        vecCapPtrDealloc A.repAlloc u32 u40 ∗ A.pool lim st sm ∗ stackAt fsp allocHookStack ∗
        (vecCapPtrDealloc A.repAlloc u56 u64 ∗ Frame))
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x0 = u40 ∧ sm.readReg64 .x9 = u16 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = d_w0 ∧
        sm.readReg64 .x24 = u56 ∧ sm.readReg64 .x25 = u64 ∧
        sm.readReg64 .x26 = u32 ∧ TraceCalleeSaved sm s0)
      ?_ ?_
    · rw [← ls_blockPlacement_base (i := 333)] at hpc ⊢
      change s.pc = (blkPl_333).base + 4660#64 at hpc
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4668#64) s _ _
      wp_steps_sync_333 ((blkPl_333).base + 4668#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx9_1, hx19_1, hx22_1, hx24_1, hx25_1, hx26_1, htr1⟩
      refine seq_clean_evs (mid := lsmpl.base 333 + 4692#64)
        (P_evs := fun evs1 sm =>
          A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗
          (vecCapPtrDealloc A.repAlloc u56 u64 ∗ Frame))
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x9 = u16 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = d_w0 ∧ sm.readReg64 .x24 = u56 ∧
          sm.readReg64 .x25 = u64 ∧ TraceCalleeSaved sm s0)
        (v2hs_err_uc_4668_to_4692_placed hA st s0 s1 fsp out u16 u32 u40 u56 u64 d_w0
          (vecCapPtrDealloc A.repAlloc u56 u64 ∗ Frame)
          hfsp_align hpc1 hrun1 hsp1 hx0_1 hx9_1 hx19_1 hx22_1 hx24_1 hx25_1 hx26_1 htr1) ?_
      intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx9_2, hx19_2, hx22_2, hx24_2, hx25_2, htr2⟩
      refine SepWP.weaken_pre (Entails.of_eq (show
        (A.pool lim (M.stepEvents evs1 st) s2 ∗ stackAt fsp allocHookStack ∗
          (vecCapPtrDealloc A.repAlloc u56 u64 ∗ Frame)) =
        (vecCapPtrDealloc A.repAlloc u56 u64 ∗
          A.pool lim (M.stepEvents evs1 st) s2 ∗ stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
      have h4692 := v2hs_err_uc_4692_to_4720_placed hA (M.stepEvents evs1 st)
        s0 s2 fsp out u16 u56 u64 d_w0 Frame
        hfsp_align hpc2 hrun2 hsp2 hx9_2 hx19_2 hx22_2 hx24_2 hx25_2 htr2
      refine SepWP.mono h4692 fun sm Pm _ _ ⟨evs2, hevs2, hPm, hspm, hx9m, hx19m, hx22m, htrm⟩ => ?_
      refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hspm, hx9m, hx19m, hx22m, htrm⟩
      simpa only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append] using hPm

theorem v2hs_err_uc_4660_to_4396_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State)
    (fsp out u8 u16 u32 u40 u48 u56 u64 u72 w176 w200 d_w0 : BitVec 64)
    (optAuth : Option ProtoAuthenticator) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4660#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = u40) (hx9 : s.readReg64 .x9 = u16)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (hx24 : s.readReg64 .x24 = u56) (hx25 : s.readReg64 .x25 = u64)
    (hx26 : s.readReg64 .x26 = u32) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4396#64) s
      (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗
        v1_optProtoAuthHeap A.repAlloc optAuth u32 u40 u48 u56 u64 u72 ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ ((fsp + 152#64) ↦₆₄ u8) ∗ memRegion (fsp + 176#64) 8 ∗ memRegion (fsp + 200#64) 8 ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = d_w0 ∧
          sm.readReg64 .x23 = (spqrErrorByte .stateDecode).zeroExtend 64 ∧ TraceCalleeSaved sm s0) := by
  let Frame4660 : SepProp :=
    ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
    vecCapPtrDealloc A.repAlloc u8 u16 ∗ Frame
  refine SepWP.weaken_pre (Entails.of_eq (show
    (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
      vecCapPtrDealloc A.repAlloc u8 u16 ∗
      v1_optProtoAuthHeap A.repAlloc optAuth u32 u40 u48 u56 u64 u72 ∗
      A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) =
    (v1_optProtoAuthHeap A.repAlloc optAuth u32 u40 u48 u56 u64 u72 ∗
      A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame4660) by
    dsimp +zetaDelta only [Frame4660]; sep_ac_rfl)) ?_
  refine seq_clean_evs (mid := lsmpl.base 333 + 4720#64)
    (P_evs := fun evs1 sm =>
      A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame4660)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x9 = u16 ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved sm s0)
    (v2hs_err_uc_4660_to_4720_placed hA st s0 s fsp out u16 u32 u40 u48 u56 u64 u72 d_w0
      optAuth Frame4660 hfsp_align hpc hrun hsp hx0 hx9 hx19 hx22 hx24 hx25 hx26 htr) ?_
  intro evs1 s1 hevs1 hpc1 hrun1 ⟨hsp1, hx9_1, hx19_1, hx22_1, htr1⟩
  refine SepWP.weaken_pre (Entails.of_eq (show
    (A.pool lim (M.stepEvents evs1 st) s1 ∗ stackAt fsp allocHookStack ∗ Frame4660) =
    (((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
      vecCapPtrDealloc A.repAlloc u8 u16 ∗
      A.pool lim (M.stepEvents evs1 st) s1 ∗ stackAt fsp allocHookStack ∗ Frame) by
      dsimp +zetaDelta only [Frame4660]; sep_ac_rfl)) ?_
  have h4720 := v2hs_err_uc_4720_to_4396_placed hA (M.stepEvents evs1 st)
    s0 s1 fsp out u8 u16 w176 w200 d_w0 Frame
    hfsp_align hpc1 hrun1 hsp1 hx9_1 hx19_1 hx22_1 htr1
  refine SepWP.mono h4720 fun sm Pm _ _ ⟨evs2, hevs2, hPm, hspm, hx19m, hx22m, hx23m, htrm⟩ => ?_
  refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hspm, hx19m, hx22m, hx23m, htrm⟩
  simpa only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append] using hPm

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb0PlacedBudget
