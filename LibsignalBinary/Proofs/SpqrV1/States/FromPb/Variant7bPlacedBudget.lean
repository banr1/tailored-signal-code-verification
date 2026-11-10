/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7b
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 7 (`Ct1Sampled`, Block `333`) — Part B

Relocatable budget-threaded `Option<ProtoPolynomialDecoder>` and `Option<ProtoPolynomialEncoder>`
cleanup blocks (`+4548`, `+4528`, `+5444`, `+11112`, `+11096 -> +4632`) under `FreeOnlyEvs`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_333 blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_333 ls_blockPlacement_base lsmpl withMemEq)
open CryptoVerification.LibsignalSpqrV1
  (PolyEncoder ProtoPolynomialDecoder ProtoPolynomialEncoder spqrAuthApi)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop
  (DropGluePolyEncoderGhost DropProtoPolyEncoderGhost DropUnchunkedCt1SentGhost
   cap_add_one_beq_zero_false dropGluePoly16Stack dropStack32 dropStack48
   none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
   optProtoPolyDecoder_none_entails_memRegion_40 optProtoPolyEncoder_none_entails_memRegion_56
   optProtoPolynomialEncoderAt_none' optProtoPolynomialEncoderAt_some'
   protoPolyDecoderTail_entails_memRegion_16 protoPolynomialEncoderAt_expose_cap
   protoPolynomialEncoderAt_unexpose_cap protoPolynomialEncoderRestAt
   unchunkedCt1SentAt unchunkedCt1SentSize)
open CryptoVerification.SpqrV1.Poly
  (boolByte optProtoPolynomialEncoderAt polyEncoderAt polyEncoderSize
   protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff protoPolynomialDecoderPadSize
   protoPolynomialDecoderPolysOff protoPolynomialDecoderPtsNeededOff
   protoPolynomialEncoderAt protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb (TraceCalleeSaved)
open CryptoVerification.SpqrV1.Unchunked (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
   RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoderBudget (dropGluePolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (dropUnchunkedCt1SentSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (FromPbAllocHooksPlacedBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st sepWP_evs_nil seq_clean_evs seq_clean_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (seq_clean_evs_lscl seq_clean_lscl_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4PlacedBudget (v4_ptsCap_add_one_ne_zero)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7aPlacedBudget
  (v7_proto_decoder_dealloc_4556_of_placedHooks
   v7_sub_ok_drop_poly_encoder_local2_mem_placed
   v7_sub_ok_drop_proto_poly_encoder_mem_placed
   v7_sub_ok_drop_unchunked_ct1_sent_local2_mem_placed)

/-! ## Re-exports of Pure Decomposition & Stack-Split Helpers from `Variant7b` -/

abbrev v7_optDecoderCapProp := CryptoVerification.SpqrV1.States.FromPb.v7_optDecoderCapProp
abbrev v7_optProtoPolyDecoderTail := CryptoVerification.SpqrV1.States.FromPb.v7_optProtoPolyDecoderTail

alias v7_optProtoPolyDecoder_expose_cap :=
  CryptoVerification.SpqrV1.States.FromPb.v7_optProtoPolyDecoder_expose_cap
alias v7_optProtoPolyDecoder_unexpose_some :=
  CryptoVerification.SpqrV1.States.FromPb.v7_optProtoPolyDecoder_unexpose_some
alias v7_cleanup_opt_decoder_some_pre :=
  CryptoVerification.SpqrV1.States.FromPb.v7_cleanup_opt_decoder_some_pre
alias v7_expose_some_protoPolyEncoder_pre :=
  CryptoVerification.SpqrV1.States.FromPb.v7_expose_some_protoPolyEncoder_pre
alias v7_stackAt_encoderFromPbStack_to_dropStack48 :=
  CryptoVerification.SpqrV1.States.FromPb.v7_stackAt_encoderFromPbStack_to_dropStack48
alias v7_stackAt_dropStack48_to_encoderFromPbStack :=
  CryptoVerification.SpqrV1.States.FromPb.v7_stackAt_dropStack48_to_encoderFromPbStack
alias v7_stackAt_encoderFromPbStack_to_dropStack32 :=
  CryptoVerification.SpqrV1.States.FromPb.v7_stackAt_encoderFromPbStack_to_dropStack32
alias v7_stackAt_dropStack32_to_encoderFromPbStack :=
  CryptoVerification.SpqrV1.States.FromPb.v7_stackAt_dropStack32_to_encoderFromPbStack

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

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

private theorem sepWP_with_evs {prog : Program} {target : BitVec 64} {s : State}
    (evs : List AllocEvent) (hevs : FreeOnlyEvs evs)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs evs sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs', FreeOnlyEvs evs' ∧ (Pm ⊢ P_evs evs' sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs, hevs, hp, hq⟩

/-! ## 1. `Option<ProtoPolynomialDecoder>` Decomposition & Cleanup at `+4548`, `+4528`, `+5444` -/

theorem v7_cleanup_opt_decoder_some_pre_pool (A : RustAlloc) (fsp pbA cap_dec : BitVec 64)
    (pb : ProtoPolynomialDecoder) (Pool Frame : SepProp) :
    stackAt fsp encoderFromPbStack ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some pb)) ∗
      Pool ∗ Frame ⊢
    ∃∗ ptsPtr : BitVec 64,
      ⌜pb.pts.length ≤ cap_dec.toNat ∧ cap_dec.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0⌝ ∗
      (stackAt fsp encoderFromPbStack ∗
       (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        (if cap_dec = 0 then emp
         else A.live ptsPtr (cap_dec.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
             ((cap_dec.toNat - pb.pts.length) * 24)) ∗
        memRegion (pbA + 208#64) 16) ∗
       Pool ∗ Frame) := by
  unfold v7_optProtoPolyDecoderTail CryptoVerification.SpqrV1.States.FromPb.v7_optProtoPolyDecoderTail
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ptsPtr
  refine Entails.sepExists_right ptsPtr ?_
  have htl := protoPolyDecoderTail_entails_memRegion_16 (pbA + 184#64)
    pb.ptsNeeded pb.polys pb.isComplete
  have h192 : (pbA + 184#64) + 8#64 = pbA + 192#64 := by bv_omega
  have h200 : (pbA + 184#64) + 16#64 = pbA + 200#64 := by bv_omega
  have h208 : (pbA + 184#64) + 24#64 = pbA + 208#64 := by bv_omega
  rw [h208] at htl
  rw [h192, h200]
  refine Entails.trans
    (Entails.of_eq (show _ =
      ⌜pb.pts.length ≤ cap_dec.toNat ∧ cap_dec.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0⌝ ∗
      (((((pbA + 184#64) + protoPolynomialDecoderPtsNeededOff) ↦₃₂ pb.ptsNeeded) ∗
        (((pbA + 184#64) + protoPolynomialDecoderPolysOff) ↦₃₂ pb.polys) ∗
        (((pbA + 184#64) + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte pb.isComplete) ∗
        memRegion ((pbA + 184#64) + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize) ∗
       (stackAt fsp encoderFromPbStack ∗
        ((pbA + 184#64) ↦₆₄ cap_dec) ∗
        ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        (if cap_dec = 0 then emp
         else A.live ptsPtr (cap_dec.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
             ((cap_dec.toNat - pb.pts.length) * 24)) ∗
        Pool ∗ Frame)) by sep_ac_rfl)) ?_
  apply Entails.pure_left; intro hp
  refine Entails.pure_right hp ?_
  exact Entails.trans (sepConj_mono_left htl) (Entails.of_eq (by sep_ac_rfl))

theorem v7_expose_some_protoPolyEncoder_pre_pool (A : RustAlloc) (fsp pbA : BitVec 64)
    (enc : ProtoPolynomialEncoder) (Mid Pool Frame : SepProp) :
    stackAt fsp encoderFromPbStack ∗
      protoPolynomialEncoderAt A (pbA + 128#64) enc ∗
      Mid ∗ Pool ∗ Frame ⊢
    ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
      ⌜cap.toNat < 2 ^ 63⌝ ∗
      (stackAt fsp encoderFromPbStack ∗
       ((pbA + 128#64) ↦₆₄ cap) ∗
       protoPolynomialEncoderRestAt A (pbA + 128#64) cap ptr enc ∗
       Mid ∗ Pool ∗ Frame) := by
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (protoPolynomialEncoderAt_expose_cap A (pbA + 128#64) enc))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro cap
  refine Entails.sepExists_right cap ?_
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ptr ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-- Budget-threaded placed cleanup of `Option<ProtoPolynomialDecoder>` at `+4548`
(`+4548 -> +4632`) under `FromPbAllocHooksPlacedBudget`: given `x22 = cap_dec`, `x27 = pbA`, and
`(pbA + 184#64 ↦₆₄ cap_dec) ∗ v7_optProtoPolyDecoderTail`, deallocates `optDec` if `some` under
`FreeOnlyEvs` and reaches `+4632` with `memRegion (pbA + 184#64) 40`. -/
theorem v7_cleanup_opt_decoder_4548_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec x28_val : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (st : M.σ) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4548#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  cases optDec with
  | none =>
    unfold v7_optDecoderCapProp CryptoVerification.SpqrV1.States.FromPb.v7_optDecoderCapProp at hcap_dec
    subst hcap_dec
    unfold v7_optProtoPolyDecoderTail CryptoVerification.SpqrV1.States.FromPb.v7_optProtoPolyDecoderTail
    dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hx22_1 ⊢
    rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 4548#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4632#64) s1 _ _
    apply sepWP_evs_nil
    simp only [AllocCostModel.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 4632#64)
    try simp only [State.setMem_setMem]
    refine entails_pre_st (fun _ hsc => ?_) ?_
    · subst hsc
      have hm := optProtoPolyDecoder_none_entails_memRegion_40 (pbA + 184#64)
      dsimp only [noneCap] at hm
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((pbA + 184#64) ↦₆₄ 18446744073709551615#64) ∗
           memRegion ((pbA + 184#64) + 8#64) 32) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool lim st _ ∗ Frame) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  | some pb =>
    refine SepWP.weaken_pre
      (v7_cleanup_opt_decoder_some_pre_pool A.repAlloc (s0.sp - 2400#64) pbA cap_dec pb
        (A.pool lim st s1) Frame) ?_
    apply ProofLib.SepWP.exists_left; intro ptsPtr
    apply ProofLib.SepWP.pure_elim; rintro ⟨hpts_le, hpts_cap_lt, _⟩
    dsimp only [RustCliAllocBudget.repAlloc_live]
    refine seq_clean_st
      (mid := lsmpl.base 333 + 4556#64)
      (P_mid := fun sm =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
         ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
         (if cap_dec = 0 then emp
          else A.live ptsPtr (cap_dec.toNat * 24) 8 ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
              ((cap_dec.toNat - pb.pts.length) * 24)) ∗
         memRegion (pbA + 208#64) 16) ∗
        A.pool lim st sm ∗
        Frame)
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · have hne := v4_ptsCap_add_one_ne_zero hpts_cap_lt
      rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 4548#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4556#64) s1 _ _
      wp_steps_sync_333 ((blkPl_333).base + 4556#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
      exact v7_proto_decoder_dealloc_4556_of_placedHooks hA s0 s2 out pbA cap_dec ptsPtr x28_val
        pb.pts st Frame hsp0_align hpts_le hpts_cap_lt hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2

/-- Budget-threaded placed cleanup of `Option<ProtoPolynomialDecoder>` at `+4548`
(`+4548 -> +4632`) under `FromPbAllocHooksBudget`. -/
theorem v7_cleanup_opt_decoder_4548_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec x28_val : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (st : M.σ) (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4548#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) :=
  v7_cleanup_opt_decoder_4548_of_placedHooks hA.toPlacedBudget
    s0 s1 out pbA cap_dec x28_val optDec st Frame
    hcap_dec hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx27_1 hx28_1 htr1

/-- Budget-threaded placed helper for `+4544 -> +4548` (`bl` Block `271`): calls
`drop_glue::<ProtoPolynomialEncoder>` with `x0 = pbA + 128#64` under `FreeOnlyEvs`. -/
theorem v7_call_drop_proto_poly_encoder_4544_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec x28_val : BitVec 64)
    (enc : ProtoPolynomialEncoder) (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4544#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx0_1 : s1.readReg64 .x0 = pbA + 128#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4548#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        protoPolynomialEncoderAt A.repAlloc (pbA + 128#64) enc ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 128#64) 56 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
  refine SepWP.weaken_pre
    (sepConj_mono_left (v7_stackAt_encoderFromPbStack_to_dropStack48 (s0.sp - 2400#64))) ?_
  rw [h7552]
  refine seq_clean_lscl_st hcl1
    (mid := lsmpl.base 271)
    (P_mid := fun sm =>
      protoPolynomialEncoderAt A.repAlloc (pbA + 128#64) enc ∗
      A.pool lim st sm ∗
      stackAt (s0.sp - 2400#64) dropStack48 ∗
      (memRegion (s0.sp - 7552#64) 1008 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x0 = pbA + 128#64 ∧
      sm.readReg64 .lr = (blkPl_333).base + 4548#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = x28_val ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · rw [← ls_blockPlacement_base (i := 333)] at hpc1
    change s1.pc = (blkPl_333).base + 4544#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 271) s1 _ _
    wp_steps_sync_333 (lsmpl.base 271)
    try simp only [State.setMem_setMem]
    refine align_pre_st (by sep_ac_rfl) ?_
    wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hlr_2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hfsp_align
    have hdrop := v7_sub_ok_drop_proto_poly_encoder_mem_placed hA hcl2
    simp only [withMemEq, dropProtoPolyEncoderSpec] at hdrop
    dsimp only [protoPolynomialEncoderSize, BitVec.ofNat_eq_ofNat] at hdrop ⊢
    rw [← ls_blockPlacement_base (i := 333)]
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4548#64) s2 _ _
    rw [show stackAt (s0.sp - 2400#64) dropStack48 = stackAt s2.sp dropStack48 from hsp2 ▸ rfl]
    wp_call hdrop ((⟨pbA + 128#64, enc⟩ : DropProtoPolyEncoderGhost), st)
    rw [hsp2]
    rw [hlr_2] at *
    have hevs_w : FreeOnlyEvs w := ‹_›
    have hacp_w : AllocCallPreserved s2 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s2.sp›.trans hsp2
    have htr_sf : sf.trace = s0.trace := hacp_w.2.1.trans htr2.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
    apply sepWP_with_evs w hevs_w
    refine entails_pre_st (fun _ hsc => ?_) ?_
    · subst hsc
      have hst := v7_stackAt_dropStack48_to_encoderFromPbStack (s0.sp - 2400#64)
      rw [h7552] at hst
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt (s0.sp - 2400#64) dropStack48 ∗ memRegion (s0.sp - 7552#64) 1008) ∗
          (memRegion (pbA + 128#64) 56 ∗ A.pool lim (M.stepEvents w st) _ ∗ Frame) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by sep_ac_rfl))
    · wp_done

/-- Budget-threaded placed cleanup at `+4528 -> +4632`:
drops `optEnc` at `pbA + 128#64` and `optDec` at `pbA + 184#64` under `FreeOnlyEvs`, preserving `x28`. -/
theorem v7_cleanup_4528_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec x28_val : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder)
    (optDec : Option ProtoPolynomialDecoder)
    (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4528#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) optEnc ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 128#64) 56 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 4548#64)
    (P_evs := fun evs1 sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗
      (memRegion (pbA + 128#64) 56 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = x28_val ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · cases optEnc with
    | none =>
      rw [optProtoPolynomialEncoderAt_none']
      dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 4528#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4548#64) s1 _ _
      apply sepWP_evs_nil
      simp only [AllocCostModel.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 4548#64)
      try simp only [State.setMem_setMem]
      refine entails_pre_st (fun _ hsc => ?_) ?_
      · subst hsc
        have hm := optProtoPolyEncoder_none_entails_memRegion_56 (pbA + 128#64)
        dsimp only [noneCap] at hm
        refine Entails.trans
          (Entails.of_eq (show _ =
            (((pbA + 128#64) ↦₆₄ 18446744073709551615#64) ∗
             memRegion ((pbA + 128#64) + 8#64) 48) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             (((pbA + 184#64) ↦₆₄ cap_dec) ∗
              v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
             A.pool lim st _ ∗ Frame) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by sep_ac_rfl))
      · wp_done
    | some enc =>
      rw [optProtoPolynomialEncoderAt_some']
      refine SepWP.weaken_pre
        (v7_expose_some_protoPolyEncoder_pre_pool A.repAlloc (s0.sp - 2400#64) pbA enc
          (((pbA + 184#64) ↦₆₄ cap_dec) ∗
           v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec)
          (A.pool lim st s1) Frame) ?_
      apply ProofLib.SepWP.exists_left; intro cap_enc
      apply ProofLib.SepWP.exists_left; intro ptr_enc
      apply ProofLib.SepWP.pure_elim; intro hcap_enc
      refine seq_clean_lscl_st hcl1
        (mid := lsmpl.base 333 + 4544#64)
        (P_mid := fun sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          protoPolynomialEncoderAt A.repAlloc (pbA + 128#64) enc ∗
          A.pool lim st sm ∗
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x0 = pbA + 128#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x27 = pbA ∧
          sm.readReg64 .x28 = x28_val ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · have hne := cap_add_one_beq_zero_false hcap_enc
        rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
        change s1.pc = (blkPl_333).base + 4528#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4544#64) s1 _ _
        wp_steps_sync_333 ((blkPl_333).base + 4544#64)
        try simp only [State.setMem_setMem]
        refine entails_pre_st (fun _ hsc => ?_) ?_
        · subst hsc
          have hunexp := protoPolynomialEncoderAt_unexpose_cap A.repAlloc (pbA + 128#64) cap_enc ptr_enc enc
          refine Entails.trans
            (Entails.of_eq (show _ =
              (((pbA + 128#64) ↦₆₄ cap_enc) ∗
               protoPolynomialEncoderRestAt A.repAlloc (pbA + 128#64) cap_enc ptr_enc enc) ∗
              (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               A.pool lim st _ ∗
               ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
                 v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame)) by sep_ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hunexp) (Entails.of_eq (by sep_ac_rfl))
        · wp_done
      · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
        have hcall := v7_call_drop_proto_poly_encoder_4544_placed hA s0 s2 out pbA cap_dec x28_val enc st
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame)
          hcl2 hsp0_align hpc2 hrun2 hsp2 hx0_2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
        exact SepWP.mono hcall fun _ _ _ _ ⟨evs1, hevs1, hPf, hrest⟩ =>
          ⟨evs1, hevs1, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hrest⟩
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
    have h4548 := v7_cleanup_opt_decoder_4548_placed hA s0 s2 out pbA cap_dec x28_val optDec
      (M.stepEvents evs1 st) (memRegion (pbA + 128#64) 56 ∗ Frame)
      hcap_dec hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
    refine SepWP.mono h4548 fun _ _ _ _ ⟨evs2, hevs2, hPf, hrest⟩ => ?_
    refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hrest⟩
    rw [AllocCostModel.stepEvents_append]
    exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))

/-- Budget-threaded placed cleanup at `+5444 -> +4632`:
executes `lsr x23, x28, #8`, drops `optEnc` at `pbA + 128#64` and `optDec` at `pbA + 184#64`
under `FreeOnlyEvs`, preserving `x28`. -/
theorem v7_cleanup_5444_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out pbA cap_dec x28_val : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder)
    (optDec : Option ProtoPolynomialDecoder)
    (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5444#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        optProtoPolynomialEncoderAt A.repAlloc (pbA + 128#64) optEnc ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 128#64) 56 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 4548#64)
    (P_evs := fun evs1 sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗
      (memRegion (pbA + 128#64) 56 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = x28_val ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · cases optEnc with
    | none =>
      rw [optProtoPolynomialEncoderAt_none']
      dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 5444#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4548#64) s1 _ _
      apply sepWP_evs_nil
      simp only [AllocCostModel.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 4548#64)
      try simp only [State.setMem_setMem]
      refine entails_pre_st (fun _ hsc => ?_) ?_
      · subst hsc
        have hm := optProtoPolyEncoder_none_entails_memRegion_56 (pbA + 128#64)
        dsimp only [noneCap] at hm
        refine Entails.trans
          (Entails.of_eq (show _ =
            (((pbA + 128#64) ↦₆₄ 18446744073709551615#64) ∗
             memRegion ((pbA + 128#64) + 8#64) 48) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             (((pbA + 184#64) ↦₆₄ cap_dec) ∗
              v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗
             A.pool lim st _ ∗ Frame) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by sep_ac_rfl))
      · wp_done
    | some enc =>
      rw [optProtoPolynomialEncoderAt_some']
      refine SepWP.weaken_pre
        (v7_expose_some_protoPolyEncoder_pre_pool A.repAlloc (s0.sp - 2400#64) pbA enc
          (((pbA + 184#64) ↦₆₄ cap_dec) ∗
           v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec)
          (A.pool lim st s1) Frame) ?_
      apply ProofLib.SepWP.exists_left; intro cap_enc
      apply ProofLib.SepWP.exists_left; intro ptr_enc
      apply ProofLib.SepWP.pure_elim; intro hcap_enc
      refine seq_clean_lscl_st hcl1
        (mid := lsmpl.base 333 + 4544#64)
        (P_mid := fun sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          protoPolynomialEncoderAt A.repAlloc (pbA + 128#64) enc ∗
          A.pool lim st sm ∗
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x0 = pbA + 128#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x27 = pbA ∧
          sm.readReg64 .x28 = x28_val ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · have hne := cap_add_one_beq_zero_false hcap_enc
        rw [← ls_blockPlacement_base (i := 333)] at hpc1 ⊢
        change s1.pc = (blkPl_333).base + 5444#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4544#64) s1 _ _
        wp_steps_sync_333 ((blkPl_333).base + 4544#64)
        try simp only [State.setMem_setMem]
        refine entails_pre_st (fun _ hsc => ?_) ?_
        · subst hsc
          have hunexp := protoPolynomialEncoderAt_unexpose_cap A.repAlloc (pbA + 128#64) cap_enc ptr_enc enc
          refine Entails.trans
            (Entails.of_eq (show _ =
              (((pbA + 128#64) ↦₆₄ cap_enc) ∗
               protoPolynomialEncoderRestAt A.repAlloc (pbA + 128#64) cap_enc ptr_enc enc) ∗
              (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               A.pool lim st _ ∗
               ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
                 v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame)) by sep_ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hunexp) (Entails.of_eq (by sep_ac_rfl))
        · wp_done
      · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
        have hcall := v7_call_drop_proto_poly_encoder_4544_placed hA s0 s2 out pbA cap_dec x28_val enc st
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            v7_optProtoPolyDecoderTail A.repAlloc (pbA + 184#64) cap_dec optDec) ∗ Frame)
          hcl2 hsp0_align hpc2 hrun2 hsp2 hx0_2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
        exact SepWP.mono hcall fun _ _ _ _ ⟨evs1, hevs1, hPf, hrest⟩ =>
          ⟨evs1, hevs1, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hrest⟩
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx27_2, hx28_2, htr2⟩
    have h4548 := v7_cleanup_opt_decoder_4548_placed hA s0 s2 out pbA cap_dec x28_val optDec
      (M.stepEvents evs1 st) (memRegion (pbA + 128#64) 56 ∗ Frame)
      hcap_dec hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx27_2 hx28_2 htr2
    refine SepWP.mono h4548 fun _ _ _ _ ⟨evs2, hevs2, hPf, hrest⟩ => ?_
    refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hrest⟩
    rw [AllocCostModel.stepEvents_append]
    exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))

/-! ## 2. Cleanup at `+11112 -> +4632` and `+11096 -> +4632` (`<PolyDecoder>::from_pb = Err`) -/

/-- `VmPreserved`-strengthened placed step `+11112 -> +4632` (`mov w28, wzr; b +4632`):
sets `x28 = 0#64` and jumps to `+4632`. -/
theorem v7_cleanup_11112_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (Rest : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 11112#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      Rest
      (fun sm Pm =>
        (Pm ⊢ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v7_cleanup_11112_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out Rest
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, hx28_m, htr_m⟩ =>
      ⟨hPm, hvm, hsp_m, hx19_m, hx28_m, htr_m⟩

theorem v7_cleanup_11112_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (Rest : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 11112#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (Rest ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢ Rest ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v7_cleanup_11112_placed (ext := ext) s0 s1 out (Rest ∗ A.pool lim st s1)
    hpc1 hrun1 hsp1 hx19_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- Budget-threaded placed cleanup at `+11096 -> +4632`:
drops `polyEncoderAt A.repAlloc (fsp + 1392) enc` (Block `272`),
drops `unchunkedCt1SentAt A.repAlloc (fsp + 1264) uc` (Block `279`),
sets `x28 = 0#64`, and jumps to `+4632` under `FreeOnlyEvs`. -/
theorem v7_cleanup_11096_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (out : BitVec 64)
    (enc : PolyEncoder) (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (st : M.σ) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11096#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        polyEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) enc ∗
        unchunkedCt1SentAt A.repAlloc ((s0.sp - 2400#64) + 1264#64) uc ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
          memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 11112#64)
    (P_evs := fun evs1 sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
      memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗
      Frame)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · refine SepWP.weaken_pre
      (sepConj_mono_left (v7_stackAt_encoderFromPbStack_to_dropStack32 (s0.sp - 2400#64))) ?_
    have h1392 : (s0.sp - 2400#64) + 1392#64 = s0.sp - 1008#64 := by bv_omega
    have h1264 : (s0.sp - 2400#64) + 1264#64 = s0.sp - 1136#64 := by bv_omega
    have h7552 : (s0.sp - 2400#64) - 5152#64 = s0.sp - 7552#64 := by bv_omega
    rw [h1392, h1264, h7552]
    refine seq_clean_evs_lscl hcl1
      (mid := lsmpl.base 333 + 11104#64)
      (P_evs := fun evs_a sm =>
        (stackAt (s0.sp - 2400#64) dropStack32 ∗ memRegion (s0.sp - 7552#64) 1024) ∗
        memRegion (s0.sp - 1008#64) 400 ∗
        unchunkedCt1SentAt A.repAlloc (s0.sp - 1136#64) uc ∗
        A.pool lim (M.stepEvents evs_a st) sm ∗
        Frame)
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · refine seq_clean_lscl_st hcl1
        (mid := lsmpl.base 272)
        (P_mid := fun sm =>
          polyEncoderAt A.repAlloc (s0.sp - 1008#64) enc ∗
          A.pool lim st sm ∗
          stackAt (s0.sp - 2400#64) dropStack32 ∗
          (memRegion (s0.sp - 7552#64) 1024 ∗
           unchunkedCt1SentAt A.repAlloc (s0.sp - 1136#64) uc ∗
           Frame))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x0 = s0.sp - 1008#64 ∧
          sm.readReg64 .lr = (blkPl_333).base + 11104#64 ∧
          sm.readReg64 .x19 = out ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · rw [← ls_blockPlacement_base (i := 333)] at hpc1
        change s1.pc = (blkPl_333).base + 11096#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          (lsmpl.base 272) s1 _ _
        wp_steps_sync_333 (lsmpl.base 272)
        try simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hlr_2, hx19_2, htr2⟩
        have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hfsp_align
        have hdrop_enc := v7_sub_ok_drop_poly_encoder_local2_mem_placed hA hcl2
        simp only [withMemEq, dropGluePolyEncoderSpec, dropGluePoly16Stack] at hdrop_enc
        dsimp only [polyEncoderSize, BitVec.ofNat_eq_ofNat] at hdrop_enc ⊢
        rw [← ls_blockPlacement_base (i := 333)]
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 11104#64) s2 _ _
        rw [show stackAt (s0.sp - 2400#64) dropStack32 = stackAt s2.sp dropStack32 from hsp2 ▸ rfl]
        wp_call hdrop_enc ((⟨s0.sp - 1008#64, enc⟩ : DropGluePolyEncoderGhost), st)
        rw [hsp2]
        rw [hlr_2] at *
        have hevs_w : FreeOnlyEvs w := ‹_›
        have hacp_w : AllocCallPreserved s2 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s2.sp›.trans hsp2
        have htr_sf : sf.trace = s0.trace := hacp_w.2.1.trans htr2.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
        apply sepWP_with_evs w hevs_w
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
    · intro evs_a s2 hevs_a hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, htr2⟩
      refine seq_clean_lscl_st hcl2
        (mid := lsmpl.base 279)
        (P_mid := fun sm =>
          unchunkedCt1SentAt A.repAlloc (s0.sp - 1136#64) uc ∗
          A.pool lim (M.stepEvents evs_a st) sm ∗
          stackAt (s0.sp - 2400#64) dropStack32 ∗
          (memRegion (s0.sp - 7552#64) 1024 ∗
           memRegion (s0.sp - 1008#64) 400 ∗
           Frame))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x0 = s0.sp - 1136#64 ∧
          sm.readReg64 .lr = (blkPl_333).base + 11112#64 ∧
          sm.readReg64 .x19 = out ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · rw [← ls_blockPlacement_base (i := 333)] at hpc2
        change s2.pc = (blkPl_333).base + 11104#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          (lsmpl.base 279) s2 _ _
        wp_steps_sync_333 (lsmpl.base 279)
        try simp only [State.setMem_setMem]
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      · intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hx0_3, hlr_3, hx19_3, htr3⟩
        have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := hsp3 ▸ hfsp_align
        have hdrop_uc := v7_sub_ok_drop_unchunked_ct1_sent_local2_mem_placed (F := F) hA hcl3
        simp only [withMemEq, dropUnchunkedCt1SentSpec] at hdrop_uc
        dsimp only [unchunkedCt1SentSize, BitVec.ofNat_eq_ofNat] at hdrop_uc ⊢
        rw [← ls_blockPlacement_base (i := 333)]
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 11112#64) s3 _ _
        rw [show stackAt (s0.sp - 2400#64) dropStack32 = stackAt s3.sp dropStack32 from hsp3 ▸ rfl]
        wp_call hdrop_uc ((⟨s0.sp - 1136#64, uc⟩ : DropUnchunkedCt1SentGhost F), M.stepEvents evs_a st)
        rw [hsp3]
        rw [hlr_3] at *
        have hevs_w : FreeOnlyEvs w := ‹_›
        have hacp_w : AllocCallPreserved s3 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s3.sp›.trans hsp3
        have htr_sf : sf.trace = s0.trace := hacp_w.2.1.trans htr3.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s3›.trans htr3.2
        apply sepWP_with_evs (evs_a ++ w) (hevs_a.append hevs_w)
        rw [AllocCostModel.stepEvents_append]
        refine entails_pre_st (fun _ hsc => ?_) ?_
        · subst hsc
          have hst := v7_stackAt_dropStack32_to_encoderFromPbStack (s0.sp - 2400#64)
          rw [h7552] at hst
          refine Entails.trans
            (Entails.of_eq (show _ =
              (stackAt (s0.sp - 2400#64) dropStack32 ∗ memRegion (s0.sp - 7552#64) 1024) ∗
              (memRegion (s0.sp - 1008#64) 400 ∗
               memRegion (s0.sp - 1136#64) 128 ∗
               A.pool lim (M.stepEvents w (M.stepEvents evs_a st)) _ ∗ Frame) by sep_ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by sep_ac_rfl))
        · wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
    have h11112 := v7_cleanup_11112_placed_budget A lim (M.stepEvents evs1 st) (ext := ext)
      s0 s2 out
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
       memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
       Frame)
      hpc2 hrun2 hsp2 hx19_2 htr2
    have hpre_eq :
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
          memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
          A.pool lim (M.stepEvents evs1 st) s2 ∗
          Frame =
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
          memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
          Frame) ∗
          A.pool lim (M.stepEvents evs1 st) s2 := by
      sep_ac_rfl
    exact SepWP.weaken_pre (Entails.of_eq hpre_eq)
      (SepWP.mono h11112 fun _ _ _ _ ⟨hPm, _, hrest⟩ =>
        ⟨evs1, hevs1, Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hrest⟩)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bPlacedBudget
