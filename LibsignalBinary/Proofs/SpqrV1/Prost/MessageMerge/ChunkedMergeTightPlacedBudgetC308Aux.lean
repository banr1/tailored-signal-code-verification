/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetC308UcAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbChunked
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbLeaf
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Varint
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Canonical-Domain Outer Steps & Proof for `Chunked.NoHeaderReceived::merge` (Block `308`)

Proves `e2kc_chunkedNoHeaderReceived_dom_ok` for `V1State.Chunked.NoHeaderReceived::merge` on
Block `308` under `tlb_ChunkedNoHeaderReceivedDom x`, stepping Tag `1` (`uc`), Tag `2`
(`receivingHdr`), and the outer `cur.length = outerLimit` exit.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetC308Aux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length)
open CryptoVerification.LibsignalTripleRatchet
  (decodeErrorHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix bv32_zeroExtend_ofNat decodeVarint_suffix key_shr32_of_lt key_wt_some
   pointsToBytes_prefix_join sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join
   sliceCursorAt suffix_trans tag_cbz_false ule_len_of_ge w1_tag_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.LibsignalSpqrV1
  (Bytes PolynomialDecoder ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.ProtoRepr (noneCap2 optPolynomialDecoderPBAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Auth (WppPost)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedInl10CalleeSaved ChunkedNoHeaderReceivedMergeGhost OptPolyDecoderBound
   PolyDecoderMergeGhost SepWPpLscro
   blkPC_308 blkPl_308 bv64_add_zero bv64_sub_zero bv_len_sub_limit
   chunkedInlBelowStack chunkedInlBelow_decodeVarint2 chunkedInlBelow_decodeVarint2_entails
   chunkedInlBelow_eq_polyMerge chunkedInlSavedRegs10 chunkedInlStack
   chunkedNoHeaderReceivedMerge_fnOff chunkedNoHeaderReceivedPBCapAt
   chunkedNoHeaderReceivedPBCapAt_mono cmp_len_limit_of_eq cmp_len_limit_of_gt
   codecWireTypeToProto default_unchunked2_entails_cap memRegion_48_split_40_8
   memRegion_polyDecoder_none_split_inl optNoHeaderReceivedPBCapAt
   optNoHeaderReceivedPBCapAt_mono optPolyDecoderBound_mono
   optPolynomialDecoderPBAt_some_eq polyDecoderToProto
   setWidth8_zext64_trunc32_ofNat64_wt_nhr stackAt_chunkedInl10_epilogue
   stackAt_chunkedInl_prologue subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
   unchunked2CapAt unchunked2CapAt_mono withLscroProp wt_beq_two_of_lengthDelimited)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open CryptoVerification.SpqrV1Sync.Codec
  (loopsTo_ch_noHeaderReceived loopsTo_polyDecoder mergeMessage_encode)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_AuthGuardedEnvOf tlb_ChunkedNoHeaderReceivedDom
   tlb_ChunkedNoHeaderReceivedGuardedEnvOf tlb_PolyDecoderDom tlb_PolyDecoderGuardedEnvOf
   tlb_ValidPolyDecoderPB tlb_ValidUcNoHeaderReceivedPB tlb_authMergeTightSpecOfEnv
   tlb_domHeap_of_dom tlb_guardedEnv_tight_of_dom tlb_lenPrefixed
   tlb_polyDecoderMergeTightSpecOfEnv tlb_polyDecoderZeroCapAt)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (chunkedNoHeaderReceivedMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some
   sepWPpLscro_of_ret_vm sepWPpLscro_of_vm sepWPpLscro_pure_elim)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetC308UcAux
  (e2kc_chunkedNoHeaderReceivedDomSpec e2kc_decodeVarint_encodeVarint
   e2kc_default_cells_entails_polyDecoderZeroCap e2kc_fitsEnv_decodeVarint2_of_some
   e2kc_fitsEnv_polyTight e2kc_isDropSuffix_append_left e2kc_loopPre
   e2kc_pool_entails_tightPoolAt_append e2kc_pool_entails_tightPoolAt_init
   e2kc_pool_entails_tightPoolAt_nil e2kc_tightPoolAt e2kc_tightPoolAt_mono
   e2kc_tightPoolAt_of_vmPreserved e2kc_ucLoopPre
   e2kc_uc_auth_opt_step_placed e2kc_uc_epoch_opt_step_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (PolyDecoderMergePostEnv polyDecoderMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec decodeVarint2SpecGen)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedNoHeaderReceivedMerge_fnOff

private theorem stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

private theorem e2kc_nhr_dom_ok_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (maxOps : Nat) (st : M.σ) (x : ChunkedNoHeaderReceivedMergeGhost)
    (s0 s sf : State) (pb : V1State.Chunked.NoHeaderReceived) (tail : List (BitVec 8))
    (evs : List AllocEvent)
    (hDom : tlb_ChunkedNoHeaderReceivedDom x)
    (hsome : (mergeMessage V1State.Chunked.NoHeaderReceived.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (pb, tail))
    (hvm : VmPreserved s sf)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = 0#64)
    (hevs : SpqrTightEvs maxOps 345567 2560 evs) :
    stackAt s0.sp chunkedInlStack ∗
      (chunkedNoHeaderReceivedPBCapAt A.repAlloc x.msgPtr tail.length pb ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs tail ∗ A.pool lim (M.stepEvents evs st) s))) ⊢
    (e2kc_chunkedNoHeaderReceivedDomSpec A lim maxOps).post (x, st) s0 sf := by
  dsimp only [e2kc_chunkedNoHeaderReceivedDomSpec, chunkedNoHeaderReceivedMergeSpecOfEnv]
  rw [hsome, htr, hx0, ← A.pool_of_vmPreserved hvm]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp chunkedInlStack ∗
      (chunkedNoHeaderReceivedPBCapAt A.repAlloc x.msgPtr tail.length pb ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs tail ∗ A.pool lim (M.stepEvents evs st) sf))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) sf ∗
        (stackAt s0.sp chunkedInlStack ∗
          (chunkedNoHeaderReceivedPBCapAt A.repAlloc x.msgPtr tail.length pb ∗
            sliceCursorAfter x.slot x.ptr x.bs tail))))) ?_
  have hguard : tlb_ChunkedNoHeaderReceivedGuardedEnvOf maxOps x evs := Or.inl ⟨hDom, hevs⟩
  exact sepConj_mono_right (sepConj_mono
    (Entails.sepExists_right evs (Entails.pure_right hguard (Entails.refl _)))
    (sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))))

section ClPlaced

set_option quotPrecheck false in
local notation "entry" => (blkPl_308).base

/-- Canonical outer key decode at `entry + 168#64` when `cur` begins with a known varint key. -/
theorem e2kc_outer_decode_known_key_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps ops cum req : Nat}
    (hVarintCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedNoHeaderReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.NoHeaderReceived} {cur rest : Bytes}
    {key : BitVec 64} {iwt : WireType} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 345567 2560))
    (ho : ops ≤ maxOps) (hc : cum ≤ 345567) (hr : req ≤ 2560)
    (hgt_lim : ¬ cur.length ≤ outerLimit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_lt : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (hitag : ¬ key.toNat / 8 < 1)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_308).base + 228#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s'
        (e2kc_loopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest ops cum req)
        (WppPost (e2kc_chunkedNoHeaderReceivedDomSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_308).base + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (e2kc_loopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur ops cum req)
      (WppPost (e2kc_chunkedNoHeaderReceivedDomSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
  have hshr := key_shr32_of_lt hk_lt
  obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
  obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_lt
  obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
  obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_lt hitag
  have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2kc_loopPre, e2kc_tightPoolAt,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs st))
      (ret_pc := entry + 188#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm, hsp, hx19]; try rfl)
      (And.intro hcur_lt (e2kc_fitsEnv_decodeVarint2_of_some ho hc hr hd hevs hFit))
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 228#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        stackAt_decodeVarint2_raw_eq, hd, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_mono A.repAlloc x.msgPtr m hrest_le_cur) (by sep_focus)
      apply SepWP.fold
        (e2kc_pool_entails_tightPoolAt_nil A lim st sm hevs (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := e2kc_loopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest ops cum req)
        (by dsimp only [e2kc_loopPre]; rw [← e2kc_tightPoolAt_of_vmPreserved hvm2]; sep_entail)
      exact hcont _
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm, htr])
        (by simp only [arm64_norm, wp_norm, hsm1, hand_wt])
        (by simp only [arm64_norm, wp_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
        (by simp only [arm64_norm, wp_norm, hx19_m])
        (by simp only [arm64_norm, wp_norm, hx20_m])
        (by simp only [arm64_norm, wp_norm, hx21_m])
        (by simp only [arm64_norm, wp_norm, hx22_m])
        (by simp only [arm64_norm, wp_norm, hx23_m])
        (by simp only [arm64_norm, wp_norm, hx24_m])
        (by simp only [arm64_norm, wp_norm, hx25_m])
        ⟨by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

/-- Canonical Tag `1` (`pb.uc : Option V1State.Unchunked.NoHeaderReceived`) step at `entry + 168#64`. -/
theorem e2kc_uc_opt_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {authOps maxOps : Nat}
    (hVarintCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hAuthTight : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim (tlb_AuthGuardedEnvOf authOps) (tlb_AuthGuardedEnvOf authOps))))
    {x : ChunkedNoHeaderReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {ucOpt : Option V1State.Unchunked.NoHeaderReceived} {afterUc : Bytes} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 345567 2560))
    (ho : authOps ≤ maxOps)
    (hValidUcOpt : ∀ u, ucOpt = some u → tlb_ValidUcNoHeaderReceivedPB u)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hlim_le_after : outerLimit ≤ afterUc.length)
    (hcur_le : (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      V1State.Unchunked.NoHeaderReceived.encodeRaw 1#32 ucOpt ++ afterUc).length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      V1State.Unchunked.NoHeaderReceived.encodeRaw 1#32 ucOpt ++ afterUc))
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_308).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s'
        (e2kc_loopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { receivingHdr := none, uc := ucOpt } x.bs afterUc authOps 2952 32)
        (WppPost (e2kc_chunkedNoHeaderReceivedDomSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_308).base + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (e2kc_loopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr default x.bs
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          V1State.Unchunked.NoHeaderReceived.encodeRaw 1#32 ucOpt ++ afterUc) 0 0 0)
      (WppPost (e2kc_chunkedNoHeaderReceivedDomSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  rcases ucOpt with _ | ucPb
  · have hdef_eq : ({ receivingHdr := none, uc := none } : V1State.Chunked.NoHeaderReceived) = default := rfl
    rw [hdef_eq] at hcont
    simpa only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, List.nil_append] using
      SepWPpLscro.weaken_pre
        (by dsimp only [e2kc_loopPre]; exact sepConj_mono_left (e2kc_tightPoolAt_mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)))
        (hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs)
  · have hValidUc : tlb_ValidUcNoHeaderReceivedPB ucPb := hValidUcOpt ucPb rfl
    let ucPayload := tlb_lenPrefixed (V1State.Unchunked.NoHeaderReceived.encodeRaw ucPb) afterUc
    have hk10 : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited = [10#8] := by decide
    have henc : CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        V1State.Unchunked.NoHeaderReceived.encodeRaw 1#32 (some ucPb) ++ afterUc = [10#8] ++ ucPayload := by
      dsimp only [ucPayload, tlb_lenPrefixed]
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
        CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hk10, List.append_assoc]
    rw [henc] at hcur_le hcur_suf ⊢
    have hgt : ¬ ([10#8] ++ ucPayload).length ≤ outerLimit := by
      simp only [List.singleton_append, List.length_cons, ucPayload, tlb_lenPrefixed, List.length_append]; omega
    have hd_key : decodeVarint ([10#8] ++ ucPayload) = some (10#64, ucPayload) := rfl
    have hcur_lt : ([10#8] ++ ucPayload).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    refine e2kc_outer_decode_known_key_placed (iwt := .lengthDelimited) hVarintCall hFit
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      hgt hsp_align hcur_le hcur_lt hcur_suf hd_key (by decide) (by decide) (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
    obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hpay_le_cur : ucPayload.length ≤ ([10#8] ++ ucPayload).length := by simp
    have hpay_le : ucPayload.length ≤ x.bs.length := Nat.le_trans hpay_le_cur hcur_le
    have hpay_lt : ucPayload.length < 2 ^ 63 := Nat.lt_of_le_of_lt hpay_le hbs_lt
    have hpay_suf : IsDropSuffix x.bs ucPayload :=
      suffix_trans hcur_le hcur_suf hpay_le_cur (decodeVarint_suffix hd_key)
    let payPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - ucPayload.length)
    let rest0 : Bytes := V1State.Unchunked.NoHeaderReceived.encodeRaw ucPb ++ afterUc
    let lenBv : BitVec 64 := BitVec.ofNat 64 (V1State.Unchunked.NoHeaderReceived.encodeRaw ucPb).length
    have hlenUc : (V1State.Unchunked.NoHeaderReceived.encodeRaw ucPb).length < 2 ^ 64 := by
      have : (V1State.Unchunked.NoHeaderReceived.encodeRaw ucPb).length ≤ ucPayload.length := by
        simp [ucPayload, tlb_lenPrefixed]; omega
      omega
    have hlenBv_toNat : lenBv.toNat = (V1State.Unchunked.NoHeaderReceived.encodeRaw ucPb).length := by
      dsimp only [lenBv]; exact Nat.mod_eq_of_lt hlenUc
    have hdv_len : decodeVarint ucPayload = some (lenBv, rest0) := by
      simpa only [ucPayload, tlb_lenPrefixed, lenBv, rest0, List.append_assoc] using
        e2kc_decodeVarint_encodeVarint lenBv rest0
    have hrest0_le_pay : rest0.length ≤ ucPayload.length := Nat.le_of_lt (decodeVarint_length hdv_len)
    have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_trans hrest0_le_pay hpay_le
    have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
    have hrest0_suf : IsDropSuffix x.bs rest0 :=
      suffix_trans hpay_le hpay_suf hrest0_le_pay (decodeVarint_suffix hdv_len)
    have hge_len : ¬ rest0.length < lenBv.toNat := by
      rw [hlenBv_toNat]; dsimp only [rest0]; rw [List.length_append]; omega
    have hule := ule_len_of_ge hge_len hrest0_lt
    have hsub : BitVec.ofNat 64 rest0.length - lenBv = BitVec.ofNat 64 afterUc.length := by
      rw [bv_len_sub_limit hge_len, hlenBv_toNat]; dsimp only [rest0]
      rw [List.length_append, Nat.add_sub_cancel_left]
    apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
    by_vm_steps
      (conv => arg 4; rw [e2kc_loopPre, e2kc_tightPoolAt, chunkedNoHeaderReceivedPBCapAt,
        show (default : V1State.Chunked.NoHeaderReceived).uc = none from rfl,
        optNoHeaderReceivedPBCapAt, memRegion_48_split_40_8 (x.msgPtr + 40#64),
        sliceCursorAfter_eq_split hpay_le hpay_suf, chunkedInlBelow_decodeVarint2 s0.sp])
      (conv => arg 4; simp only [noneCap2, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, sepConj_pure_left_comm, arm64_norm])
      apply SepWP.exists_elim; intro v48
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      have hdef :
          ((x.msgPtr + 40#64) ↦₆₄ 0xffffffffffffffff#64) ∗
            memRegion (x.msgPtr + 48#64) 40 ∗
            ((x.msgPtr + 88#64) ↦₆₄ 0#64) ⊢
          unchunked2CapAt A.repAlloc (x.msgPtr + 40#64) ucPayload.length
            (default : V1State.Unchunked.NoHeaderReceived).epoch
            (default : V1State.Unchunked.NoHeaderReceived).auth := by
        change ((x.msgPtr + 40#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          memRegion (x.msgPtr + 48#64) 40 ∗
          ((x.msgPtr + 88#64) ↦₆₄ 0#64) ⊢
          unchunked2CapAt A.repAlloc (x.msgPtr + 40#64) ucPayload.length 0#64 none
        simpa only [noneCap, arm64_norm] using
          default_unchunked2_entails_cap A.repAlloc (x.msgPtr + 40#64) ucPayload.length
      apply SepWP.fold hdef (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (⟨x.bufRef, x.slot, payPtr, ucPayload⟩, M.stepEvents evs st))
        (ret_pc := entry + 332#64) hVarintCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
            simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm, hsp1, hx19_1]; try rfl)
        (And.intro hpay_lt (e2kc_fitsEnv_decodeVarint2_of_some (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) hdv_len hevs hFit))
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 408#64)
      by_vm_steps
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
          stackAt_decodeVarint2_raw_eq, hdv_len, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp1])
        apply SepWP.exists_elim; intro evs_dv
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hpay_le hpay_suf hrest0_le_pay) (by sep_focus)
        apply SepWP.fold (unchunked2CapAt_mono A.repAlloc (x.msgPtr + 0x28#64)
          (default : V1State.Unchunked.NoHeaderReceived).epoch
          (default : V1State.Unchunked.NoHeaderReceived).auth hrest0_le_pay) (by sep_focus)
        apply SepWP.fold
          (e2kc_pool_entails_tightPoolAt_nil A lim st sm hevs (decodeVarint2Env_eq_nil_of_some hdv_len hevs_dv))
          (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt])
        (conv => arg 4; simp only [sepConj_assoc])
        wp_steps
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        let afterEpoch : Bytes :=
          CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
            ProtoAuthenticator.encodeRaw 2#32 ucPb.auth ++ afterUc
        have hrest0_eq : rest0 =
            CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 ucPb.epoch ++ afterEpoch := by
          dsimp only [rest0, afterEpoch, V1State.Unchunked.NoHeaderReceived.encodeRaw]
          rw [List.append_assoc]
        apply SepWPpLscro.weaken_pre
          (P' := e2kc_ucLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            none default x.bs
            (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 ucPb.epoch ++ afterEpoch) 0 0 0)
          (by rw [← hrest0_eq]; dsimp only [e2kc_ucLoopPre, sliceCursorAfter];
              rw [← e2kc_tightPoolAt_of_vmPreserved hvm2]; sep_entail)
        have hrest0_le' : (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 ucPb.epoch ++ afterEpoch).length ≤ x.bs.length := by
          rw [← hrest0_eq]; exact hrest0_le
        have hrest0_suf' : IsDropSuffix x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 ucPb.epoch ++ afterEpoch) := by
          rw [← hrest0_eq]; exact hrest0_suf
        have hafter_gt : ∀ b tl, CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 ucPb.epoch = b :: tl →
            ¬ (b :: tl ++ afterEpoch).length ≤ afterUc.length := by
          intro b tl _; dsimp only [afterEpoch]; simp only [List.cons_append, List.length_cons, List.length_append]; omega
        refine e2kc_uc_epoch_opt_step_placed (outerLimit := outerLimit) (innerLimit := afterUc.length)
          hVarintCall hFit hsp_align hbs_lt
          hrest0_le' hrest0_suf' hafter_gt ?_
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          (by simp only [arm64_norm, wp_norm, hx23_m])
          (by simp only [arm64_norm, wp_norm, hx24_m])
          (by simp only [arm64_norm, wp_norm, hx25_m])
          (by simp only [arm64_norm, wp_norm, hsm1, hsub])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
        intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hcs2
        have hafterEpoch_le : afterEpoch.length ≤ x.bs.length := by
          have : afterEpoch.length ≤ (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 ucPb.epoch ++ afterEpoch).length := by
            simp only [List.length_append]; omega
          omega
        have hafterEpoch_suf : IsDropSuffix x.bs afterEpoch :=
          suffix_trans hrest0_le' hrest0_suf'
            (by simp only [List.length_append]; omega)
            (e2kc_isDropSuffix_append_left _ _)
        refine e2kc_uc_auth_opt_step_placed (outerLimit := outerLimit)
          hVarintCall hAuthTight hFit ho hValidUc
          hsp_align hbs_lt hafterEpoch_le hafterEpoch_suf ?_
          hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hcs2
        intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hcs3
        obtain ⟨hx27_3, hx28_3, hvregs_3⟩ := hcs3
        have hafterUc_le : afterUc.length ≤ x.bs.length := by
          have : afterUc.length ≤ afterEpoch.length := by
            dsimp only [afterEpoch]; simp only [List.length_append]; omega
          omega
        have hafterUc_suf : IsDropSuffix x.bs afterUc :=
          suffix_trans hafterEpoch_le hafterEpoch_suf
            (by dsimp only [afterEpoch]; simp only [List.length_append]; omega)
            (by dsimp only [afterEpoch]; exact e2kc_isDropSuffix_append_left _ _)
        obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq (rfl : afterUc.length = afterUc.length)
        apply sepWPpLscro_of_vm (mid := entry + 168#64)
        by_vm_steps
          (conv => arg 4; rw [e2kc_ucLoopPre, sliceCursorAfter_eq_split hafterUc_le hafterUc_suf,
            sliceCursorAt])
          wp_steps
          apply SepWP.fold (pointsToBytes_prefix_join hafterUc_le hafterUc_suf) (by sep_focus)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm3 => ?_⟩
          apply SepWPpLscro.weaken_pre
            (P' := e2kc_loopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { receivingHdr := none, uc := some ucPb } x.bs afterUc authOps 2952 32)
            (by dsimp only [e2kc_loopPre, chunkedNoHeaderReceivedPBCapAt,
                  optNoHeaderReceivedPBCapAt, unchunked2CapAt, sliceCursorAfter];
                rw [← e2kc_tightPoolAt_of_vmPreserved hvm3]; sep_entail)
          exact hcont _
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrun3])
            (by simp only [arm64_norm, wp_norm, hsp3])
            (by simp only [arm64_norm, wp_norm, htr3])
            (by simp only [arm64_norm, wp_norm, hx19_3])
            (by simp only [arm64_norm, wp_norm, hx20_3])
            (by simp only [arm64_norm, wp_norm, hx21_3])
            (by simp only [arm64_norm, wp_norm, hx22_3])
            (by simp only [arm64_norm, wp_norm, hx23_3])
            (by simp only [arm64_norm, wp_norm, hx24_3])
            (by simp only [arm64_norm, wp_norm, hx25_3])
            ⟨by simp only [arm64_norm, wp_norm, hx27_3],
             by simp only [arm64_norm, wp_norm, hx28_3],
             by simp only [arm64_norm, wp_norm, hvregs_3]⟩

/-- Canonical Tag `2` (`pb.receivingHdr : Option PolynomialDecoder`) step at `entry + 168#64`. -/
theorem e2kc_hdr_opt_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {authOps decOps maxOps : Nat}
    (hOps : authOps + decOps ≤ maxOps)
    (hVarintCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hPolyTight : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyDecoderMergeTightSpecOfEnv A lim
          (tlb_PolyDecoderGuardedEnvOf decOps) (tlb_PolyDecoderGuardedEnvOf decOps))))
    {x : ChunkedNoHeaderReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {pb : V1State.Chunked.NoHeaderReceived} {tail : Bytes}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 345567 2560))
    (hValidDecOpt : ∀ d, pb.receivingHdr = some d → tlb_ValidPolyDecoderPB d)
    (hbound : OptPolyDecoderBound none x.bs.length)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hcur_le : (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      PolynomialDecoder.encodeRaw 2#32 pb.receivingHdr ++ tail).length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      PolynomialDecoder.encodeRaw 2#32 pb.receivingHdr ++ tail))
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_308).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 tail.length →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s'
        (e2kc_loopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr pb x.bs tail maxOps 345567 2560)
        (WppPost (e2kc_chunkedNoHeaderReceivedDomSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_308).base + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 tail.length)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (e2kc_loopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        { receivingHdr := none, uc := pb.uc } x.bs
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          PolynomialDecoder.encodeRaw 2#32 pb.receivingHdr ++ tail) authOps 2952 32)
      (WppPost (e2kc_chunkedNoHeaderReceivedDomSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  rcases pb with ⟨ucOpt, _ | decPb⟩
  · have hmono : e2kc_loopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        { receivingHdr := none, uc := ucOpt } x.bs tail authOps 2952 32 ⊢
        e2kc_loopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
          { receivingHdr := none, uc := ucOpt } x.bs tail maxOps 345567 2560 :=
      sepConj_mono_left
        (e2kc_tightPoolAt_mono (o1 := authOps) (o2 := maxOps) (c1 := 2952) (c2 := 345567) (r1 := 32) (r2 := 2560)
          (by omega) (by decide) (by decide))
    simpa only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, List.nil_append] using
      SepWPpLscro.weaken_pre hmono (hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs)
  · dsimp only at hValidDecOpt hcur_le hcur_suf ⊢
    have hValidDec : tlb_ValidPolyDecoderPB decPb := hValidDecOpt decPb rfl
    let decPayload := tlb_lenPrefixed (PolynomialDecoder.encodeRaw decPb) tail
    have hk18 : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 2#32 .lengthDelimited = [18#8] := by decide
    have henc : CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        PolynomialDecoder.encodeRaw 2#32 (some decPb) ++ tail = [18#8] ++ decPayload := by
      dsimp only [decPayload, tlb_lenPrefixed]
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
        CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hk18, List.append_assoc]
    rw [henc] at hcur_le hcur_suf ⊢
    have hgt : ¬ ([18#8] ++ decPayload).length ≤ tail.length := by
      simp only [List.singleton_append, List.length_cons, decPayload, tlb_lenPrefixed, List.length_append]; omega
    have hd_key : decodeVarint ([18#8] ++ decPayload) = some (18#64, decPayload) := rfl
    have hcur_lt : ([18#8] ++ decPayload).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    refine e2kc_outer_decode_known_key_placed (iwt := .lengthDelimited) hVarintCall hFit
      (by omega) (by decide) (by decide)
      hgt hsp_align hcur_le hcur_lt hcur_suf hd_key (by decide) (by decide) (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
    obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hpay_le_cur : decPayload.length ≤ ([18#8] ++ decPayload).length := by simp
    have hpay_le : decPayload.length ≤ x.bs.length := Nat.le_trans hpay_le_cur hcur_le
    have hpay_suf : IsDropSuffix x.bs decPayload :=
      suffix_trans hcur_le hcur_suf hpay_le_cur (decodeVarint_suffix hd_key)
    let payPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - decPayload.length)
    let x_poly : PolyDecoderMergeGhost :=
      ⟨.lengthDelimited, x.msgPtr, default, x.bufRef, x.slot, payPtr, decPayload⟩
    have hPolyDom : tlb_PolyDecoderDom x_poly := ⟨rfl, rfl, decPb, tail, hValidDec, rfl⟩
    have hpoly_bound : x_poly.msg.pts.length + x_poly.bs.length < 2 ^ 56 := by
      have hb := optPolyDecoderBound_mono hbound hpay_le
      simpa only [OptPolyDecoderBound, Option.getD_none, x_poly] using hb
    have hlenDec : (PolynomialDecoder.encodeRaw decPb).length < 2 ^ 64 := by
      have : (PolynomialDecoder.encodeRaw decPb).length ≤ decPayload.length := by
        simp [decPayload, tlb_lenPrefixed]; omega
      omega
    have hmergeDec : (mergeMessage PolynomialDecoder.mergeField
        (codecWireTypeToProto .lengthDelimited) default decPayload 98).toOption =
        some (decPb, tail) := by
      have hm := mergeMessage_encode PolynomialDecoder.mergeField 0 PolynomialDecoder.encodeRaw
        default decPb 98 tail (loopsTo_polyDecoder decPb hlenDec) hlenDec (by decide)
      simpa only [codecWireTypeToProto, decPayload, tlb_lenPrefixed, List.append_assoc, Except.toOption] using
        congrArg Except.toOption hm
    have htail_le_pay : tail.length ≤ decPayload.length := by
      simp [decPayload, tlb_lenPrefixed]; omega
    apply sepWPpLscro_of_vm (mid := lsmpl.base 296)
    by_vm_steps
      (conv => arg 4; rw [e2kc_loopPre, e2kc_tightPoolAt, chunkedNoHeaderReceivedPBCapAt,
        optPolynomialDecoderPBAt, memRegion_polyDecoder_none_split_inl x.msgPtr,
        sliceCursorAfter_eq_split hpay_le hpay_suf, chunkedInlBelow_eq_polyMerge s0.sp])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, sepConj_pure_left_comm, arm64_norm])
      apply SepWP.exists_elim; intro b32
      apply SepWP.exists_elim; intro v24
      apply SepWP.exists_elim; intro v16
      apply SepWP.exists_elim; intro v8
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.fold (e2kc_default_cells_entails_polyDecoderZeroCap A.repAlloc x.msgPtr) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (x_poly, M.stepEvents evs st))
        (ret_pc := entry + 284#64) hPolyTight
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [tlb_polyDecoderMergeTightSpecOfEnv]
              rw [tlb_domHeap_of_dom hPolyDom]
              dsimp only [x_poly]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
        (by exact ⟨by simp only [arm64_norm, wp_norm, hx8_1, setWidth8_zext64_trunc32_ofNat64_wt_nhr],
          by simp only [arm64_norm, wp_norm, hx20_1],
          by simp only [arm64_norm, wp_norm, hx19_1],
          hpoly_bound,
          e2kc_fitsEnv_polyTight hPolyDom hOps hevs hFit⟩)
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 168#64)
      by_vm_steps
        (conv => arg 4; simp only [tlb_polyDecoderMergeTightSpecOfEnv, polyDecoderMergeSpecOfEnv,
          PolyDecoderMergePostEnv, x_poly, hmergeDec, ← chunkedInlBelow_eq_polyMerge s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_p
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_p
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        apply SepWP.fold (sliceCursorAfter_join hpay_le hpay_suf htail_le_pay) (by sep_focus)
        apply SepWP.fold (optNoHeaderReceivedPBCapAt_mono A.repAlloc (x.msgPtr + 0x28#64) ucOpt htail_le_pay) (by sep_focus)
        apply SepWP.fold
          (e2kc_pool_entails_tightPoolAt_append A lim st sm
            (o3 := maxOps) (c3 := 345567) (r3 := 2560)
            hOps (by decide) (by decide) hevs
            (tlb_guardedEnv_tight_of_dom hPolyDom hevs_p))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        apply SepWPpLscro.weaken_pre
          (P' := e2kc_loopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { receivingHdr := some decPb, uc := ucOpt } x.bs tail maxOps 345567 2560)
          (by dsimp only [e2kc_loopPre, chunkedNoHeaderReceivedPBCapAt];
              rw [optPolynomialDecoderPBAt_some_eq, ← e2kc_tightPoolAt_of_vmPreserved hvm2]; sep_entail)
        exact hcont _
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          (by simp only [arm64_norm, wp_norm, hx23_m])
          (by simp only [arm64_norm, wp_norm, hx24_m])
          (by simp only [arm64_norm, wp_norm, hx25_m])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

/-- Canonical outer exact-limit exit (`cur = tail`, `outerLimit = tail.length`) at `entry + 168#64`. -/
theorem e2kc_outer_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps : Nat}
    {x : ChunkedNoHeaderReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {pb : V1State.Chunked.NoHeaderReceived} {tail : Bytes}
    (hDom : tlb_ChunkedNoHeaderReceivedDom x)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsome : (mergeMessage V1State.Chunked.NoHeaderReceived.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (pb, tail))
    (htail_le : tail.length ≤ x.bs.length)
    (htail_suf : IsDropSuffix x.bs tail)
    (hpc : s.pc = (blkPl_308).base + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (_hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (_hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 tail.length)
    (_hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (_hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (_hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (e2kc_loopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr pb x.bs tail maxOps 345567 2560)
      (WppPost (e2kc_chunkedNoHeaderReceivedDomSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - tail.length)
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq (rfl : tail.length = tail.length)
  apply sepWPpLscro_of_ret_vm
  by_vm_steps
    (conv => arg 4; simp only [e2kc_loopPre, e2kc_tightPoolAt,
      sliceCursorAfter_eq_split htail_le htail_suf, sliceCursorAt, chunkedInlSavedRegs10,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm, arm64_norm, hsp])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus)
    have hcur_fold :
        (x.slot ↦₆₄ curPtr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
          (x.ptr ↦ₛ x.bs.take (x.bs.length - tail.length)) ∗ (curPtr ↦ₛ tail) ⊢
        sliceCursorAfter x.slot x.ptr x.bs tail := by
      rw [sliceCursorAfter_eq_split htail_le htail_suf, sliceCursorAt]
      dsimp only [curPtr]
      exact Entails.of_eq (by sep_ac_rfl)
    apply SepWP.fold hcur_fold (by dsimp only [curPtr]; sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
    refine ⟨fun hm => Satisfies.of_entails hm (sepConj_mono_left ?_),
      by simp only [arm64_norm, wp_norm, hsp],
      by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx27, hx28, hvregs]⟩
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (e2kc_nhr_dom_ok_exit_entails A lim maxOps st x s0 s _ pb tail evs hDom hsome hvm
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm]) hevs)

/-- Canonical-domain `subroutine_ok` proof on `e2kc_chunkedNoHeaderReceivedDomSpec` (`tlb_ChunkedNoHeaderReceivedDom x`), parameterized by `authOps + decOps ≤ maxOps` and zero-capacity tight callee contracts. -/
theorem e2kc_chunkedNoHeaderReceived_dom_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {authOps decOps maxOps : Nat}
    (hOps : authOps + decOps ≤ maxOps)
    (hVarintCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hAuthTight : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim (tlb_AuthGuardedEnvOf authOps) (tlb_AuthGuardedEnvOf authOps))))
    (hPolyTight : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyDecoderMergeTightSpecOfEnv A lim
          (tlb_PolyDecoderGuardedEnvOf decOps) (tlb_PolyDecoderGuardedEnvOf decOps)))) :
    subroutine_ok ((blkPC_308).rebase (blkPl_308).base H)
      (blkPl_308).base
      (withLsCodeRoLoaded lsmpl (e2kc_chunkedNoHeaderReceivedDomSpec A lim maxOps)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp e2kc_chunkedNoHeaderReceivedDomSpec chunkedNoHeaderReceivedMergeSpecOfEnv
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  replace hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (e2kc_chunkedNoHeaderReceivedDomSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R)
  apply sepWPpLscro_pure_elim
  intro hDom
  apply sepWPpLscro_pure_elim
  rintro ⟨h_1, h_2, h_3, hbound, hFit0⟩
  have hFit : FitsEnv M lim st (SpqrTightEvs maxOps 345567 2560) :=
    fun evs hevs => hFit0 evs (Or.inl ⟨hDom, hevs⟩)
  have ⟨hwt_proto, hmsg_def, pb, tail, ⟨hValidUcOpt, hValidDecOpt⟩, hbs_eq⟩ := hDom
  have hwt_ld : x.wt = .lengthDelimited := by
    cases h : x.wt <;> simp [codecWireTypeToProto, h] at hwt_proto; rfl
  have hbs_lt : x.bs.length < 2 ^ 63 := by unfold OptPolyDecoderBound at hbound; omega
  have hbound_none : OptPolyDecoderBound none x.bs.length := by
    rw [hmsg_def] at hbound; exact hbound
  have hlenCh : (V1State.Chunked.NoHeaderReceived.encodeRaw pb).length < 2 ^ 64 := by
    have : (V1State.Chunked.NoHeaderReceived.encodeRaw pb).length ≤ x.bs.length := by
      rw [hbs_eq]; simp [tlb_lenPrefixed]; omega
    omega
  have hsome : (mergeMessage V1State.Chunked.NoHeaderReceived.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (pb, tail) := by
    have hm := mergeMessage_encode V1State.Chunked.NoHeaderReceived.mergeField 2
      V1State.Chunked.NoHeaderReceived.encodeRaw default pb 99 tail
      (loopsTo_ch_noHeaderReceived pb hlenCh) hlenCh (by decide)
    simpa only [hwt_proto, hmsg_def, hbs_eq, tlb_lenPrefixed, List.append_assoc, Except.toOption] using
      congrArg Except.toOption hm
  let lenBv : BitVec 64 := BitVec.ofNat 64 (V1State.Chunked.NoHeaderReceived.encodeRaw pb).length
  let rest0 : Bytes := V1State.Chunked.NoHeaderReceived.encodeRaw pb ++ tail
  have hlenBv_toNat : lenBv.toNat = (V1State.Chunked.NoHeaderReceived.encodeRaw pb).length := by
    dsimp only [lenBv]; exact Nat.mod_eq_of_lt hlenCh
  have hdv0 : decodeVarint x.bs = some (lenBv, rest0) := by
    rw [hbs_eq]
    simpa only [tlb_lenPrefixed, lenBv, rest0, List.append_assoc] using
      e2kc_decodeVarint_encodeVarint lenBv rest0
  have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt (decodeVarint_length hdv0)
  have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
  have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
  have hge_len : ¬ rest0.length < lenBv.toNat := by
    rw [hlenBv_toNat]; dsimp only [rest0]; rw [List.length_append]; omega
  have hule := ule_len_of_ge hge_len hrest0_lt
  have hsub : BitVec.ofNat 64 rest0.length - lenBv = BitVec.ofNat 64 tail.length := by
    rw [bv_len_sub_limit hge_len, hlenBv_toNat]; dsimp only [rest0]
    rw [List.length_append, Nat.add_sub_cancel_left]
  have hsaved :
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
      chunkedInlSavedRegs10 s0.sp s0 := Entails.refl _
  have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
  have hbeq := wt_beq_two_of_lengthDelimited h_1'
  have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
    simp only [bne, hbeq, Bool.not_true]
  have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
    rw [truncate32_zeroExtend64_and_255_eq, h_1']; decide
  have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
    revert h_1'; bv_bits
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [stackAt_chunkedInl_prologue s0.sp, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v8
    apply SepWP.exists_elim; intro v9
    wp_steps
    apply SepWP.fold hsaved (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (spec := decodeVarint2Spec A lim)
      (x := (⟨x.bufRef, x.slot, x.ptr, x.bs⟩, st))
      (ret_pc := entry + 56#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm])
      (by exact ⟨by simp only [arm64_norm, wp_norm, h_3],
        hbs_lt,
        by simpa only [AllocCostModel.stepEvents, List.foldl] using
             e2kc_fitsEnv_decodeVarint2_of_some (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
               hdv0 (SpqrTightEvs.nil 0 0 0) hFit⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, h_2, h_3]
      at hpcm hrunm hspm hx19_m hx20_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 168#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        stackAt_decodeVarint2_raw_eq, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
        sliceCursorAt, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (chunkedNoHeaderReceivedPBCapAt_mono A.repAlloc x.msgPtr x.msg hrest0_le) (by sep_focus)
      have hpool0 : A.pool lim (M.stepEvents evs_dv st) sm ⊢ e2kc_tightPoolAt A lim st 0 0 0 sm := by
        rw [decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv]
        simpa only [AllocCostModel.stepEvents, List.foldl] using
          e2kc_pool_entails_tightPoolAt_init A lim st sm
      apply SepWP.fold hpool0 (by sep_focus)
      wp_steps
      apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      let afterUc : Bytes :=
        CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          PolynomialDecoder.encodeRaw 2#32 pb.receivingHdr ++ tail
      have hrest0_eq : rest0 =
          CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
            V1State.Unchunked.NoHeaderReceived.encodeRaw 1#32 pb.uc ++ afterUc := by
        dsimp only [rest0, afterUc, V1State.Chunked.NoHeaderReceived.encodeRaw]
        rw [List.append_assoc]
      apply SepWPpLscro.weaken_pre
        (P' := e2kc_loopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr default x.bs
          (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
            V1State.Unchunked.NoHeaderReceived.encodeRaw 1#32 pb.uc ++ afterUc) 0 0 0)
        (by rw [← hrest0_eq, ← hmsg_def]; dsimp only [e2kc_loopPre, sliceCursorAfter];
            rw [← e2kc_tightPoolAt_of_vmPreserved hvm2]; sep_entail)
      have hrest0_le' : (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          V1State.Unchunked.NoHeaderReceived.encodeRaw 1#32 pb.uc ++ afterUc).length ≤ x.bs.length := by
        rw [← hrest0_eq]; exact hrest0_le
      have hrest0_suf' : IsDropSuffix x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          V1State.Unchunked.NoHeaderReceived.encodeRaw 1#32 pb.uc ++ afterUc) := by
        rw [← hrest0_eq]; exact hrest0_suf
      have hlim_le_after : tail.length ≤ afterUc.length := by
        dsimp only [afterUc]; rw [List.length_append]; omega
      refine e2kc_uc_opt_step_placed hVarintCall hAuthTight hFit (by omega) hValidUcOpt
        hsp_align hbs_lt hlim_le_after hrest0_le' hrest0_suf' ?_
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm])
        (by simp only [arm64_norm, wp_norm, hx19_m])
        (by simp only [arm64_norm, wp_norm, hx20_m])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hsm1, hsub])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        ⟨by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩
      intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
      have hafterUc_le : afterUc.length ≤ x.bs.length := by
        have : afterUc.length ≤ (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
            V1State.Unchunked.NoHeaderReceived.encodeRaw 1#32 pb.uc ++ afterUc).length := by
          simp only [List.length_append]; omega
        omega
      have hafterUc_suf : IsDropSuffix x.bs afterUc :=
        suffix_trans hrest0_le' hrest0_suf'
          (by simp only [List.length_append]; omega)
          (e2kc_isDropSuffix_append_left _ _)
      refine e2kc_hdr_opt_step_placed hOps hVarintCall hPolyTight hFit hValidDecOpt hbound_none
        hsp_align hbs_lt hafterUc_le hafterUc_suf ?_
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
      intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hcs2
      have htail_le : tail.length ≤ x.bs.length := by
        have : tail.length ≤ afterUc.length := by
          dsimp only [afterUc]; simp only [List.length_append]; omega
        omega
      have htail_suf : IsDropSuffix x.bs tail :=
        suffix_trans hafterUc_le hafterUc_suf
          (by dsimp only [afterUc]; simp only [List.length_append]; omega)
          (by dsimp only [afterUc]; exact e2kc_isDropSuffix_append_left _ _)
      exact e2kc_outer_exit_placed hDom hsp_align hsome htail_le htail_suf
        hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hcs2

end ClPlaced

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetC308Aux
