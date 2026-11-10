/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB300StepsPlacedBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1Sent
import LibsignalBinary.Proofs.SpqrV1.Varint.VarintCodeSym
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbChunked
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp

/-!
# Guarded-Tight Placed Budget Proof for `Chunked.Ct1Sampled::merge` (Block `300`)

Proves `tlb_ChunkedCt1SampledMergePlacedTightOkOf` on Block `300` within
`SpqrTightEvs maxOps 731332 2560` (`ucOps + encOps + decOps ≤ maxOps`, default `80 = 10 + 35 + 35`:
`Unchunked.Ct1Sent` `46,102` B + `PolynomialEncoder` `342,615` B + `PolynomialDecoder` `342,615` B)
on canonical `tlb_ChunkedCt1SampledDom` inputs, falling back to `ChunkedCt1SampledMergeEnv` outside the domain.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB300PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement blkPC_312 blkPl_312 libsignalMutatedBlocks
   libsignalSessionExterns libsignalSessionLib ls_blockPlacement_base lsmpl)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length)
open CryptoVerification.LibsignalTripleRatchet
  (keys_ls_subroutine_ok_of_block_cro withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (DecodeVarintSlowGhost IsDropSuffix decodeVarint_suffix
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAt ule_len_of_ge)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.LibsignalSpqrV1 (PolynomialDecoder PolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeOptMessage mergeMessage)
open CryptoVerification.SpqrV1.Auth (WppPost)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedCt1SampledMergeGhost ChunkedLoopRegs SepWPpLscro
   bv64_add_zero bv64_sub_zero bv_len_sub_limit
   chunkedBelow_leaf chunkedBelow_leaf_entails
   chunkedCt1SampledMerge_fnOff chunkedCt1SampledPBCapAt chunkedCt1SampledPBCapAt_mono
   chunkedMergeStack chunkedSavedRegs codecWireTypeToProto
   stackAt_chunkedMerge subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
   withLscroProp wt_beq_two_of_lengthDelimited)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_300 blkPl_300)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_ChunkedCt1SampledDom tlb_ChunkedCt1SampledGuardedEnvOf
   tlb_ChunkedCt1SampledMergePlacedTightOk tlb_ChunkedCt1SampledMergePlacedTightOkOf
   tlb_ChunkedCt1SampledTightEnvOf
   tlb_PolyDecoderGuardedEnvOf tlb_PolyDecoderMergePlacedTightOkOf
   tlb_PolyEncoderGuardedEnvOf tlb_PolyEncoderMergePlacedTightOkOf
   tlb_UcCt1SentGuardedEnvOf tlb_UcCt1SentMergePlacedTightOkOf
   tlb_polyDecoderMergeTightSpecOfEnv tlb_polyEncoderMergeTightSpecOfEnv
   tlb_ucCt1SentMergeTightSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudget
  (chunked_ct1_sampled_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetAux
  (stackAt_decodeVarint2_raw_eq)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (chunkedCt1SampledMergePostEnv_imp_pre chunkedCt1SampledMergeSpec
   chunkedCt1SampledMergeSpecOfEnv decodeErrorPushMergeBudgetSpec unchunkedCt1SentMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some
   sepWPpLscro_of_vm sepWPpLscro_pure_elim)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB300StepsPlacedBudget
  (e2ka_b300TightPre e2ka_b300TightSpec e2ka_b300_opt1_step e2ka_b300_opt2_step
   e2ka_b300_opt3_step e2ka_b300_ret_exit e2ka_b300_tightEnv_combine
   e2ka_decodeVarint_lenPrefixed e2ka_mergeMessage_ct1Sampled_ok)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (polyDecoderMergeSpec polyEncoderMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

private theorem e2ka_b300_sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl
private theorem e2ka_b300_pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl
private theorem e2ka_b300_status_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).status = s.status := by cases s; rfl
private theorem e2ka_b300_pstate_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).pstate = s.pstate := by cases s; rfl
private theorem e2ka_b300_trace_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := by cases s; rfl
private theorem e2ka_b300_readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem e2ka_b300_readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem e2ka_b300_readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem e2ka_b300_calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedCt1SampledMerge_fnOff
attribute [local arm64_norm ↓, local wp_norm ↓]
  e2ka_b300_sp_setMem_pre e2ka_b300_pc_setMem_pre e2ka_b300_status_setMem_pre
  e2ka_b300_pstate_setMem_pre e2ka_b300_trace_setMem_pre e2ka_b300_readReg64_setMem_pre
  e2ka_b300_readReg32_setMem_pre e2ka_b300_readReg_setMem_pre
  e2ka_b300_calleeSavedVRegs_setMem_pre

/-! ## 1. Cross-Block Transfer & Pure Helpers -/

private theorem e2ka_b300_ls_subroutine_ok_cro_of_blockProgram_ext [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {entry : BitVec 64} {spec : Spec α}
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns)
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry
      (withLsCodeRoLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) :=
  @keys_ls_subroutine_ok_of_block_cro _ _ callerProg
    (libsignalSessionLib.blockProgram lsmpl j H) i j H hcaller ⟨rfl, hext_j⟩ entry spec
    hcallee _ _ _ _ hi hj hj_unmut

private theorem e2ka_b300_wt_eq_lengthDelimited {wt : WireType}
    (h : codecWireTypeToProto wt = .lengthDelimited) :
    wt = .lengthDelimited := by
  cases wt <;> cases h
  rfl

private theorem e2ka_b300_fitsEnv_decodeVarint2_of_some {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {bs : List (BitVec 8)} {p : BitVec 64 × List (BitVec 8)}
    (hd : decodeVarint bs = some p) :
    FitsEnv M lim st (DecodeVarint2Env bs) := by
  intro evs h
  rw [decodeVarint2Env_eq_nil_of_some hd h]
  trivial

/-! ## 2. Canonical `Dom` Prologue & Full `Dom` Proof for Block `300` -/

private theorem e2ka_b300_dom_prologue [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps : Nat}
    (hVarintCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedCt1SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {len : BitVec 64} {rest0 : List (BitVec 8)}
    (hpc : s0.pc = (blkPl_300).base) (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0_wt : (s0.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat)
    (hx1_msg : s0.readReg64 .x1 = x.msgPtr)
    (hx2_buf : s0.readReg64 .x2 = x.bufRef)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hwt_ld : x.wt = .lengthDelimited)
    (hdv0 : decodeVarint x.bs = some (len, rest0))
    (hge_len : ¬ rest0.length < len.toNat)
    (hcont : ∀ s : State,
      s.pc = (blkPl_300).base + 192#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot →
      s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 (rest0.length - len.toNat) →
      ChunkedLoopRegs s0 s →
      SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
        (e2ka_b300TightPre A lim st [] s0 s x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
        (WppPost (e2ka_b300TightSpec A lim maxOps) (x, st) R s0)
        (WppPanicFalse R)) :
    SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s0
      (chunkedCt1SampledPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
        ((x.bufRef ↦₆₄ x.slot) ∗ (sliceCursorAt x.slot x.ptr x.bs ∗
          (A.pool lim st s0 ∗ stackAt s0.sp chunkedMergeStack))))
      (WppPost (e2ka_b300TightSpec A lim maxOps) (x, st) R s0)
      (WppPanicFalse R) := by
  have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [hx0_wt, hwt_ld]; rfl
  have hbeq := wt_beq_two_of_lengthDelimited h_1'
  have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
    simp only [bne, hbeq, Bool.not_true]
  have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64
      (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
    rw [truncate32_zeroExtend64_and_255_eq, h_1']; decide
  have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64
      (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
    revert h_1'; bv_bits
  let x_dv0 : DecodeVarintSlowGhost := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [stackAt_chunkedMerge s0.sp, chunkedBelow_leaf s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v23; apply SepWP.exists_elim; intro v24
    apply SepWP.exists_elim; intro v25; apply SepWP.exists_elim; intro v_lr
    apply SepWP.exists_elim; intro v_fp
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_dv0, st))
      (ret_pc := (blkPl_300).base + 56#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv0]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm,
              stackAt_decodeVarint2_raw_eq])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx2_buf], hbs_lt,
        e2ka_b300_fitsEnv_decodeVarint2_of_some hdv0⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m,
            hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hx1_msg, hx2_buf]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m
         hx26_m hx27_m hx28_m hvregs_m
    have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
    have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
    have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
    have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
    let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
    have hule := ule_len_of_ge hge_len hrest0_lt
    have hsub := bv_len_sub_limit hge_len
    apply sepWPpLscro_of_vm (mid := (blkPl_300).base + 192#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv0, hdv0,
        stackAt_decodeVarint2_raw_eq, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
        sliceCursorAt, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro evs_dv
      wp_focus_pure; intro hsm01
      wp_focus_pure; intro htrm
      wp_focus_pure; intro hevs_dv
      rcases hsm01 with ⟨hsm0, hsm1⟩
      have hevs_nil : evs_dv = [] := decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv
      subst hevs_nil
      (conv => arg 4; simp only [AllocCostModel.stepEvents_nil, arm64_norm, wp_norm])
      apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (chunkedCt1SampledPBCapAt_mono A.repAlloc x.msgPtr x.msg hrest0_le)
        (by sep_focus)
      wp_steps
      have hrest0_fold :
          (x.slot ↦₆₄ rest0Ptr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗
            (x.ptr ↦ₛ x.bs.take (x.bs.length - rest0.length)) ∗ (rest0Ptr ↦ₛ rest0) ⊢
          sliceCursorAfter x.slot x.ptr x.bs rest0 := by
        rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
        dsimp only [rest0Ptr]
        exact Entails.of_eq (by sep_ac_rfl)
      apply SepWP.fold hrest0_fold (by dsimp only [rest0Ptr]; sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2ka_b300TightPre A lim st [] s0 _ x.msgPtr x.bufRef x.slot x.ptr
          x.msg x.bs rest0)
        (by dsimp only [e2ka_b300TightPre, AllocCostModel.stepEvents_nil, chunkedSavedRegs]
            sep_entail)
      exact hcont _
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm])
        (by simp only [arm64_norm, wp_norm, hx19_m])
        (by simp only [arm64_norm, wp_norm, hx20_m])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hsm1, hsub])
        ⟨by simp only [arm64_norm, wp_norm],
         by simp only [arm64_norm, wp_norm],
         by simp only [arm64_norm, wp_norm],
         ⟨by simp only [arm64_norm, wp_norm, hx26_m],
          by simp only [arm64_norm, wp_norm, hx27_m],
          by simp only [arm64_norm, wp_norm, hx28_m],
          by simp only [arm64_norm, wp_norm, hvregs_m]⟩⟩

private def e2ka_b300_domOnlySpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (maxOps : Nat) : Spec (ChunkedCt1SampledMergeGhost × M.σ) :=
  let base := e2ka_b300TightSpec A lim maxOps
  { base with pre := fun (x, st) s => ⌜tlb_ChunkedCt1SampledDom x⌝ ∗ base.pre (x, st) s }

private theorem e2ka_b300_dom_only_subroutine_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ucOps encOps decOps maxOps : Nat} {H : String → Option (State → State)}
    (hOps : ucOps + encOps + decOps ≤ maxOps)
    (hVarintCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hUcTightCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl
        (tlb_ucCt1SentMergeTightSpecOfEnv A lim
          (tlb_UcCt1SentGuardedEnvOf ucOps) (tlb_UcCt1SentGuardedEnvOf ucOps))))
    (hPolyEncTightCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (tlb_PolyEncoderGuardedEnvOf encOps) (tlb_PolyEncoderGuardedEnvOf encOps))))
    (hPolyDecTightCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyDecoderMergeTightSpecOfEnv A lim
          (tlb_PolyDecoderGuardedEnvOf decOps) (tlb_PolyDecoderGuardedEnvOf decOps)))) :
    subroutine_ok ((blkPC_300).rebase (blkPl_300).base H)
      (blkPl_300).base
      (withLsCodeRoLoaded lsmpl (e2ka_b300_domOnlySpec A lim maxOps)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp e2ka_b300_domOnlySpec
  dsimp only [e2ka_b300TightSpec, chunkedCt1SampledMergeSpecOfEnv]
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  replace hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (e2ka_b300TightSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R)
  apply sepWPpLscro_pure_elim
  intro hDom
  apply sepWPpLscro_pure_elim
  rintro ⟨hx0_wt, hx1_msg, hx2_buf, _hpts_0, _hpolys_0, hdec_0, hFit⟩
  have hFitTight : FitsEnv M lim st (tlb_ChunkedCt1SampledTightEnvOf maxOps) :=
    fun evs ht => hFit evs (Or.inl ⟨hDom, ht⟩)
  have hbs_lt56 : x.bs.length < 2 ^ 56 := by omega
  have hbs_lt : x.bs.length < 2 ^ 63 := by omega
  rcases hDom with ⟨hwt_proto, hmsg_def, pb, tail, ⟨hValUc, hValEnc, hValDec⟩, hbs_eq⟩
  have hDom' : tlb_ChunkedCt1SampledDom x :=
    ⟨hwt_proto, hmsg_def, pb, tail, ⟨hValUc, hValEnc, hValDec⟩, hbs_eq⟩
  have hwt_ld : x.wt = .lengthDelimited := e2ka_b300_wt_eq_lengthDelimited hwt_proto
  let raw := V1State.Chunked.Ct1Sampled.encodeRaw pb
  have hdv0 : decodeVarint x.bs = some (BitVec.ofNat 64 raw.length, raw ++ tail) := by
    rw [hbs_eq]; exact e2ka_decodeVarint_lenPrefixed raw tail
  have hrest0_lt_bs : (raw ++ tail).length < x.bs.length := decodeVarint_length hdv0
  have hraw_lt64 : raw.length < 2 ^ 64 := by
    rw [List.length_append] at hrest0_lt_bs; omega
  have hraw_bv : (BitVec.ofNat 64 raw.length).toNat = raw.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hraw_lt64]
  have hge_len : ¬ (raw ++ tail).length < (BitVec.ofNat 64 raw.length).toNat := by
    rw [hraw_bv, List.length_append]; omega
  have hlim_eq : (raw ++ tail).length - (BitVec.ofNat 64 raw.length).toNat = tail.length := by
    rw [hraw_bv, List.length_append]; omega
  have hsome_top :
      (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (pb, tail) := by
    rw [hwt_proto, hmsg_def, hbs_eq]
    exact e2ka_mergeMessage_ct1Sampled_ok pb tail hraw_lt64
  have hrest0_le : (raw ++ tail).length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
  have hrest0_suf : IsDropSuffix x.bs (raw ++ tail) := decodeVarint_suffix hdv0
  let cur₂ := encodeOptMessage PolynomialDecoder.encodeRaw 3#32 pb.receivingEk ++ tail
  let cur₁ := encodeOptMessage PolynomialEncoder.encodeRaw 2#32 pb.sendingCt1 ++ cur₂
  have hcur0_eq :
      raw ++ tail = encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 pb.uc ++ cur₁ := by
    simp only [raw, V1State.Chunked.Ct1Sampled.encodeRaw, cur₁, cur₂, List.append_assoc]
  have htail_le_cur2 : tail.length ≤ cur₂.length := by
    simp only [cur₂, List.length_append]; omega
  have hcur2_le_cur1 : cur₂.length ≤ cur₁.length := by
    simp only [cur₁, List.length_append]; omega
  have htail_le_cur1 : tail.length ≤ cur₁.length := Nat.le_trans htail_le_cur2 hcur2_le_cur1
  refine e2ka_b300_dom_prologue hVarintCall hpc hrun hsp_align hx0_wt hx1_msg hx2_buf
    hbs_lt hwt_ld hdv0 hge_len ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1
  rw [hlim_eq] at hx22_1
  rw [hmsg_def]
  refine e2ka_b300_opt1_step (encOps := encOps) (decOps := decOps) hOps
    hVarintCall hUcTightCall hFitTight hValUc hcur0_eq htail_le_cur1 hsp_align hbs_lt
    hrest0_le hrest0_suf ?_ hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1
  intro evsUc s2 hUcEvs hcur1_le hcur1_suf hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2
  refine e2ka_b300_opt2_step (decOps := decOps) hOps
    hVarintCall hPolyEncTightCall hFitTight hUcEvs hValEnc rfl htail_le_cur2 hsp_align hbs_lt56
    hcur1_le hcur1_suf ?_ hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2
  intro evsEnc s3 hEncEvs hcur2_le hcur2_suf hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hcs3
  refine e2ka_b300_opt3_step (pb := pb) hOps
    hVarintCall hPolyDecTightCall hFitTight hUcEvs hEncEvs hValDec rfl rfl hsp_align hbs_lt56
    hcur2_le hcur2_suf ?_ hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hcs3
  intro evsDec s4 hDecEvs htail_le htail_suf hpc4 hrun4 hsp4 htr4 hx21_4 hx22_4 hcs4
  exact e2ka_b300_ret_exit hDom' (e2ka_b300_tightEnv_combine hOps hUcEvs hEncEvs hDecEvs)
    rfl hsp_align hsome_top htail_le htail_suf hpc4 hrun4 hsp4 htr4 hx21_4 hx22_4 hcs4

/-! ## 3. Guarded-Tight Block `300` Composition & Tight Contracts -/

theorem e2ka_b300_chunkedCt1Sampled_merge_blk_tight_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ucOps encOps decOps maxOps : Nat} {H : String → Option (State → State)}
    (hOps : ucOps + encOps + decOps ≤ maxOps)
    (hFromCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hUcCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)))
    (hPolyEncCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hPolyDecCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hUcTightCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl
        (tlb_ucCt1SentMergeTightSpecOfEnv A lim
          (tlb_UcCt1SentGuardedEnvOf ucOps) (tlb_UcCt1SentGuardedEnvOf ucOps))))
    (hPolyEncTightCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (tlb_PolyEncoderGuardedEnvOf encOps) (tlb_PolyEncoderGuardedEnvOf encOps))))
    (hPolyDecTightCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyDecoderMergeTightSpecOfEnv A lim
          (tlb_PolyDecoderGuardedEnvOf decOps) (tlb_PolyDecoderGuardedEnvOf decOps)))) :
    subroutine_ok ((blkPC_300).rebase (blkPl_300).base H)
      (blkPl_300).base
      (withLsCodeRoLoaded lsmpl (e2ka_b300TightSpec A lim maxOps)) := by
  have hDomOk := e2ka_b300_dom_only_subroutine_ok hOps
    hVarintCall hUcTightCall hPolyEncTightCall hPolyDecTightCall
  have hKleene := chunked_ct1_sampled_merge_cl_placed_ok_of_contracts
    hFromCall hPushCall hVarintCall hSkipCall hUcCall hPolyEncCall hPolyDecCall
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hDom : tlb_ChunkedCt1SampledDom x.1
  · have hpre_dom : s0.mem ⊨
        (withLsCodeRoLoaded lsmpl (e2ka_b300_domOnlySpec A lim maxOps)).pre x s0 ∗ R := by
      refine Satisfies.mono ?_ hpre
      dsimp only [withLsCodeRoLoaded, e2ka_b300_domOnlySpec]
      exact sepConj_mono_left (sepConj_mono_left (Entails.pure_right hDom (Entails.refl _)))
    exact hDomOk.mono_outcome x R s0 hpc hrun hpre_dom hsp fun _ out => out
  · have hpre_kl : s0.mem ⊨
        (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)).pre x s0 ∗ R := by
      refine Satisfies.mono ?_ hpre
      dsimp only [withLsCodeRoLoaded, e2ka_b300TightSpec,
        chunkedCt1SampledMergeSpec, chunkedCt1SampledMergeSpecOfEnv]
      refine sepConj_mono_left (sepConj_mono_left ?_)
      refine Entails.pure_left fun ⟨h1, h2, h3, h4, h5, h6, hFit⟩ =>
        Entails.pure_right ⟨h1, h2, h3, h4, h5, h6, fun evs he => hFit evs (Or.inr ⟨hDom, he⟩)⟩
          (Entails.refl _)
    refine hKleene.mono_outcome x R s0 hpc hrun hpre_kl hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, Satisfies.mono ?_ hq⟩
      dsimp only [withLsCodeRoLoaded, e2ka_b300TightSpec,
        chunkedCt1SampledMergeSpec, chunkedCt1SampledMergeSpecOfEnv]
      refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))
      refine Entails.sepExists_elim fun evs => Entails.pure_left fun hevs => ?_
      exact Entails.sepExists_right evs
        (Entails.pure_right (Or.inr ⟨hDom, chunkedCt1SampledMergePostEnv_imp_pre hevs⟩)
          (Entails.refl _))
    · dsimp only [withLsCodeRoLoaded, chunkedCt1SampledMergeSpec,
        chunkedCt1SampledMergeSpecOfEnv] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1
    · dsimp only [withLsCodeRoLoaded, chunkedCt1SampledMergeSpec,
        chunkedCt1SampledMergeSpecOfEnv] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1
    · dsimp only [withLsCodeRoLoaded, chunkedCt1SampledMergeSpec,
        chunkedCt1SampledMergeSpecOfEnv] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1

/-- Guarded-tight contract `tlb_ChunkedCt1SampledMergePlacedTightOkOf A lim maxOps ext` on
`libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext)` (`ucOps + encOps + decOps ≤ maxOps`). -/
theorem e2ka_b300_chunkedCt1SampledMerge_placed_tight_ok_of [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ucOps encOps decOps maxOps : Nat} {ext : String → Option (State → State)}
    (hOps : ucOps + encOps + decOps ≤ maxOps)
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hUcUntight : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      (lsmpl.base 312) (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)))
    (hPolyEncUntight : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hPolyDecUntight : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hUcTight : tlb_UcCt1SentMergePlacedTightOkOf A lim ucOps ext)
    (hPolyEncTight : tlb_PolyEncoderMergePlacedTightOkOf A lim encOps ext)
    (hPolyDecTight : tlb_PolyDecoderMergePlacedTightOkOf A lim decOps ext) :
    tlb_ChunkedCt1SampledMergePlacedTightOkOf A lim maxOps ext := by
  have hok := e2ka_b300_chunkedCt1Sampled_merge_blk_tight_ok_of_contracts
    (H := Rust.withPanics ext) hOps
    (e2ka_b300_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_261).rebase (CryptoVerification.blkPl_261).base (fun _ => none))) hFrom)
    (e2ka_b300_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.RecordCodecs.Placed.blkPC_257).rebase (CryptoVerification.RecordCodecs.Placed.blkPl_257).base (fun _ => none))) hPush)
    (e2ka_b300_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_291).rebase (CryptoVerification.blkPl_291).base (fun _ => none))) hVarint)
    (e2ka_b300_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_263).rebase (CryptoVerification.blkPl_263).base (fun _ => none))) hSkip)
    (e2ka_b300_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (blkPC_312).rebase (blkPl_312).base (fun _ => none))) hUcUntight)
    (e2ka_b300_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_297).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_297).base (fun _ => none))) hPolyEncUntight)
    (e2ka_b300_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_296).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_296).base (fun _ => none))) hPolyDecUntight)
    (e2ka_b300_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (blkPC_312).rebase (blkPl_312).base (fun _ => none))) hUcTight)
    (e2ka_b300_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_297).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_297).base (fun _ => none))) hPolyEncTight)
    (e2ka_b300_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_296).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_296).base (fun _ => none))) hPolyDecTight)
  rw [IsLsBlockProg.eq_blockProgram (prog := (blkPC_300).rebase (blkPl_300).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 300)] at hok
  exact hok

/-- Default `maxOps = 80` (`10 + 35 + 35`) specialization proving
`tlb_ChunkedCt1SampledMergePlacedTightOk`. -/
theorem e2ka_b300_chunkedCt1SampledMerge_placed_tight_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hUcUntight : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      (lsmpl.base 312) (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)))
    (hPolyEncUntight : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hPolyDecUntight : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hUcTight : tlb_UcCt1SentMergePlacedTightOkOf A lim 10 ext)
    (hPolyEncTight : tlb_PolyEncoderMergePlacedTightOkOf A lim 35 ext)
    (hPolyDecTight : tlb_PolyDecoderMergePlacedTightOkOf A lim 35 ext) :
    tlb_ChunkedCt1SampledMergePlacedTightOk A lim ext :=
  e2ka_b300_chunkedCt1SampledMerge_placed_tight_ok_of (by decide)
    hFrom hPush hVarint hSkip hUcUntight hPolyEncUntight hPolyDecUntight
    hUcTight hPolyEncTight hPolyDecTight

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB300PlacedBudget
