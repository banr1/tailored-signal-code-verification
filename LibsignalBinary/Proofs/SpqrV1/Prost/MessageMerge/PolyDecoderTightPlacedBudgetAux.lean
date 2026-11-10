/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Canonical-Domain Tight Budget Proof of `PolynomialDecoder::merge` (Block `296`)

Proves the `tlb_PolyDecoderDom x` branch of `PolynomialDecoder::merge` (Block `296`) under
zero-initial-capacity `tlb_polyDecoderZeroCapAt` (`pts.cap = 0#64`) within
`SpqrTightEvs maxOps 342615 2560` (`35 ≤ maxOps`), discharging all decode-error branches purely
from `mergeMessage` success on canonical wire inputs (`pts.length ≤ 16`, slice lengths `≤ 2,560`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderTightPlacedBudgetAux

open Arm64 ProofLib SepProp
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap
  (RustAlloc arrayAt vecAt vecBuf vecHeader vecOf vecU8 vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded reserveCap withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix bv32_zeroExtend_ofNat decodeVarint_suffix itag_beq_tag_false key_shr32_of_lt
   key_wt_some sf_truncate32_ofNat64 skip_suffix sliceCursorAfter sliceCursorAfter_eq_split
   sliceCursorAfter_join sliceCursorAt suffix_trans tag_cbz_false ule_len_of_ge w1_tag_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.LibsignalSpqrV1
  (GrowOneCall PolynomialDecoder ProtoPolynomialDecoder growOneVecU8Name newCapVecU8)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Poly
  (ProtoPolynomialDecoderGhost boolByte protoPolynomialDecoderAt
   protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff protoPolynomialDecoderPadSize
   protoPolynomialDecoderPinnedAt protoPolynomialDecoderPolysOff protoPolynomialDecoderPtsNeededOff
   vecHeaderBytes vecVecU8PinnedAt)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_decodeVarint_toOption)
open CryptoVerification.SpqrV1.Prost.MessageEncode (protoPolynomialDecoderAt_eq_exists_pinned)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (PolyCalleeSaved PolyDecoderMergeGhost SepWPp.call_frame_lscro SepWPp.elim_lscroProp
   SepWPp.of_sepWP_lscro WppPost arrayAt_append_singleton blkPC_296 blkPl_296 bv64_add_zero
   bv64_ofNat_add_one
   bv_len_sub_limit cells160_entails_memRegion32 cmp_len_limit_of_eq cmp_len_limit_of_gt
   codecWireTypeToProto extractLsb'_append64_0 extractLsb'_append64_64 grow_post_entails_ready
   len_eq_cap_bne_false len_lt_cap_bne_true madd_24_eq madd_24_eq' memRegion_32_cells160
   memRegion_split_24_cells mergeBytes_eq_none_of_ne_len mergeBytes_length mergeBytes_suffix
   mergeLoopBin mergeLoopBin_eq_limit mergeLoopBin_lt_limit mergeLoopBin_of_decodeVarint_none
   mergeLoopBin_of_key_ge mergeLoopBin_of_key_ok mergeLoopBin_of_tag_zero mergeLoopBin_of_wt_none
   mergeMessageBin mergeMessageBin_eq_proto_mergeMessage polyBelowStack polyBelow_bytesMerge3
   polyBelow_bytesMerge3_entails polyBelow_decodeVarint2 polyBelow_decodeVarint2_entails
   polyBelow_extHook polyBelow_extHook_entails polyDecoderToProto polyMergeStack polySavedRegs
   polySavedRegsAny polySavedRegs_entails_any polynomialDecoder_mergeField_other
   polynomialDecoder_mergeField_tag1 polynomialDecoder_mergeField_tag2
   polynomialDecoder_mergeField_tag3 polynomialDecoder_mergeField_tag4
   protoPrefixStep_polynomialDecoder_mergeField setWidth8_ofNat64_wt slt_two_ofNat32_true
   stackAt_polyMerge_epilogue stackAt_polyMerge_prologue vecBuf_vecU8_entails_grow_pre
   vecU8ArrayBytes vecU8At_eq_header_sep_buf vecU8At_stack_to_cells vecU8At_zero_eq_cells vecU8Buf
   wt_beq_two_of_lengthDelimited)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (GrowOneVecU8Env RawVecGrowEnv growOneVecU8BudgetSpec rawVecGrowBudgetSpec rawVecNewCap)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_PolyDecoderDom tlb_PolyDecoderGuardedEnvOf tlb_ValidPolyDecoderPB)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (BytesMerge3EnvCore mergeBytes_len_bound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env WppBudgetPanic bytesMerge3RawBudgetSpec polyDecoderMergeSpecOfEnv
   wppBudgetPanic_false)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderBudgetAux
  (decodeVarint2Stack_eq decodeVarint2_pool_of_some sepWPp_focus_pure sepWPp_fold)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (SkipField3Env skipField3Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv SkipFieldEnv decodeVarintSliceEvents skipFieldEventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)

private theorem sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.trace) = (s.setMem m).trace := by
  cases s; rfl
private theorem trace_setMem_pre' (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm]
  bv_sub_add_lit BitVec.toNat_zero growOneVecU8Name bv64_add_zero bv64_ofNat_add_one
  madd_24_eq madd_24_eq' extractLsb'_append64_0 extractLsb'_append64_64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre'
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre calleeSavedVRegs_setMem_pre

/-! ## 1. Doubling Capacity Invariant, Prefix Lemma, & Callee `SpqrTightEvs` Envelopes -/

def e2p_ValidPolyVecCap (cap : Nat) : Prop :=
  cap = 0 ∨ cap = 4 ∨ cap = 8 ∨ 16 ≤ cap

def e2p_polyGrowRemOps (cap : Nat) : Nat :=
  if 16 ≤ cap then 0
  else if 8 ≤ cap then 1
  else if 4 ≤ cap then 2
  else 3

def e2p_polyGrowDoneOps (cap : Nat) : Nat :=
  3 - e2p_polyGrowRemOps cap

def e2p_doneOps (cap ptsLen : Nat) : Nat :=
  e2p_polyGrowDoneOps cap + 2 * ptsLen

def e2p_remOps (cap ptsLen : Nat) : Nat :=
  e2p_polyGrowRemOps cap + 2 * (16 - ptsLen)

theorem e2p_polyGrowRemOps_le_3 (cap : Nat) : e2p_polyGrowRemOps cap ≤ 3 := by
  by_cases h16 : 16 ≤ cap <;> by_cases h8 : 8 ≤ cap <;> by_cases h4 : 4 ≤ cap <;>
    simp [e2p_polyGrowRemOps, h16, h8, h4]

theorem e2p_doneOps_add_remOps (cap : Nat) {ptsLen : Nat} (hpts : ptsLen ≤ 16) :
    e2p_doneOps cap ptsLen + e2p_remOps cap ptsLen = 35 := by
  have hr := e2p_polyGrowRemOps_le_3 cap
  unfold e2p_doneOps e2p_remOps e2p_polyGrowDoneOps
  omega

theorem e2p_validPolyVecCap_step {cap : Nat} (hv : e2p_ValidPolyVecCap cap) (hlt : cap < 16) :
    e2p_ValidPolyVecCap (max (2 * cap) 4) ∧
      max (2 * cap) 4 * 24 ≤ 384 ∧
      1 ≤ e2p_polyGrowRemOps cap ∧
      e2p_polyGrowDoneOps (max (2 * cap) 4) = e2p_polyGrowDoneOps cap + 1 := by
  rcases hv with rfl | rfl | rfl | hge
  · refine ⟨Or.inr (Or.inl rfl), by decide, by decide, by decide⟩
  · refine ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, by decide, by decide⟩
  · refine ⟨Or.inr (Or.inr (Or.inr (by decide))), by decide, by decide, by decide⟩
  · omega

private theorem e2p_mergeField_pts_prefix {m m' : PolynomialDecoder} {tag : BitVec 32}
    {wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType} {rest rest' : List (BitVec 8)}
    {depth : Nat}
    (h : PolynomialDecoder.mergeField m tag wt rest depth = .ok (m', rest')) :
    ∃ sfx, m'.pts = m.pts ++ sfx := by
  unfold PolynomialDecoder.mergeField at h
  split at h
  · rcases h1 : CryptoVerification.LibsignalSpqrV1.Proto.mergeUint32 wt rest with _ | ⟨v, bs'⟩ <;>
      simp [h1, Bind.bind, Except.bind] at h
    rcases h with ⟨rfl, rfl⟩; exact ⟨[], by simp⟩
  · split at h
    · rcases h1 : CryptoVerification.LibsignalSpqrV1.Proto.mergeUint32 wt rest with _ | ⟨v, bs'⟩ <;>
        simp [h1, Bind.bind, Except.bind] at h
      rcases h with ⟨rfl, rfl⟩; exact ⟨[], by simp⟩
    · split at h
      · unfold CryptoVerification.LibsignalSpqrV1.Proto.mergeRepeatedBytes at h
        rcases h1 : CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes wt rest with _ | ⟨v, bs'⟩ <;>
          simp [h1, Bind.bind, Except.bind] at h
        rcases h with ⟨rfl, rfl⟩; exact ⟨[v], rfl⟩
      · split at h
        · rcases h1 : CryptoVerification.LibsignalSpqrV1.Proto.mergeBool wt rest with _ | ⟨v, bs'⟩ <;>
            simp [h1, Bind.bind, Except.bind] at h
          rcases h with ⟨rfl, rfl⟩; exact ⟨[], by simp⟩
        · rcases h1 : CryptoVerification.LibsignalSpqrV1.Proto.skipField wt tag rest depth with _ | bs' <;>
            simp [h1, Bind.bind, Except.bind] at h
          rcases h with ⟨rfl, rfl⟩; exact ⟨[], by simp⟩

theorem e2p_mergeLoopBin_pts_prefix {fuel : Nat} {m m' : PolynomialDecoder}
    {cur : List (BitVec 8)} {limit depth : Nat}
    (h : mergeLoopBin PolynomialDecoder.mergeField fuel m cur limit depth = some m') :
    ∃ sfx, m'.pts = m.pts ++ sfx := by
  induction fuel generalizing m cur with
  | zero =>
    unfold mergeLoopBin at h; split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact ⟨[], by simp⟩
      · contradiction
    · contradiction
  | succ fuel ih =>
    unfold mergeLoopBin at h; split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact ⟨[], by simp⟩
      · contradiction
    · rcases hdk : CryptoVerification.LibsignalSpqrV1.Proto.decodeKey cur with _ | ⟨⟨tag, wt⟩, rest⟩
      · simp [hdk, Except.toOption] at h
      · simp only [hdk, Except.toOption] at h
        rcases hmf : PolynomialDecoder.mergeField m tag wt rest depth with _ | ⟨m1, rest'⟩
        · simp [hmf] at h
        · simp only [hmf] at h
          obtain ⟨s1, hs1⟩ := e2p_mergeField_pts_prefix hmf
          obtain ⟨s2, hs2⟩ := ih h
          exact ⟨s1 ++ s2, by rw [hs2, hs1, List.append_assoc]⟩

theorem e2p_bytesMerge3_tight {bs v rest' : List (BitVec 8)} {evs : List AllocEvent}
    (hmb : mergeBytes .lengthDelimited bs = some (v, rest'))
    (hv : v.length ≤ 2560)
    (hb : BytesMerge3EnvCore .lengthDelimited 0#64 bs evs) :
    SpqrTightEvs 2 (2 * 9789) 2560 evs := by
  unfold BytesMerge3EnvCore bytesMergeEventsCore at hb
  rw [hmb] at hb
  by_cases hv0 : v.length = 0
  · simp only [hv0, ↓reduceIte] at hb
    subst hb
    exact SpqrTightEvs.nil 2 (2 * 9789) 2560
  · simp only [hv0, ↓reduceIte] at hb
    subst hb
    have h0 : (0#64).toNat = 0 := rfl
    have hdrc : doReserveClearEvents (0#64).toNat v.length =
        rustAllocEvents (reserveCap 0 0 v.length) 1 := by
      rw [h0]
      unfold doReserveClearEvents
      simp only [show ¬ v.length ≤ 0 by omega, ↓reduceIte]
    have hrc_le : reserveCap 0 0 v.length ≤ 2560 := by
      unfold reserveCap; omega
    rw [hdrc]
    have h1 : SpqrTightEvs 1 9789 2560 (rustAllocEvents v.length 1) :=
      (SpqrTightEvs.rustAlloc (R := 2560) hv (by decide)).mono
        (Nat.le_refl _) (by decide) (Nat.le_refl _)
    have h2 : SpqrTightEvs 1 9789 2560 (rustAllocEvents (reserveCap 0 0 v.length) 1) :=
      (SpqrTightEvs.rustAlloc (R := 2560) hrc_le (by decide)).mono
        (Nat.le_refl _) (by decide) (Nat.le_refl _)
    have h3 : SpqrTightEvs 0 0 0 (rustDeallocEvents v.length 1) :=
      SpqrTightEvs.rustDealloc v.length 1
    exact ((h1.append h2).append h3).mono (by decide) (by decide) (by decide)

theorem e2p_growOneVecU8_tight {g : GrowOneCall} {evs : List AllocEvent}
    (hv : e2p_ValidPolyVecCap g.cap.toNat) (hlt : g.cap.toNat < 16)
    (hg : GrowOneVecU8Env g evs) :
    SpqrTightEvs 1 9789 2560 evs := by
  unfold GrowOneVecU8Env RawVecGrowEnv at hg
  rcases hg with ⟨hz, rfl⟩ | ⟨hnz, rfl⟩
  · exact (SpqrTightEvs.rustAlloc (R := 96) (by decide) (by decide)).mono
      (Nat.le_refl _) (by decide) (by decide)
  · rcases hv with h0 | h4 | h8 | hge
    · exact False.elim (hnz (BitVec.eq_of_toNat_eq (by simpa using h0)))
    · rw [h4]
      exact (SpqrTightEvs.rustRealloc384 (by decide) (by decide) (by decide)).mono
        (Nat.le_refl _) (Nat.le_refl _) (by decide)
    · rw [h8]
      exact (SpqrTightEvs.rustRealloc384 (by decide) (by decide) (by decide)).mono
        (Nat.le_refl _) (Nat.le_refl _) (by decide)
    · omega

theorem e2p_fitsEnv_rem_tight {M : AllocCostModel} {lim : BudgetLimits} {st0 st_cur : M.σ}
    {maxOps cap ptsLen : Nat} {evs_acc : List AllocEvent}
    (hOps : 35 ≤ maxOps) (hpts : ptsLen ≤ 16)
    (hFit0 : FitsEnv M lim st0 (SpqrTightEvs maxOps 342615 2560))
    (hevs_acc : SpqrTightEvs (e2p_doneOps cap ptsLen) (e2p_doneOps cap ptsLen * 9789) 2560 evs_acc)
    (hst_cur : st_cur = M.stepEvents evs_acc st0) :
    FitsEnv M lim st_cur (SpqrTightEvs (e2p_remOps cap ptsLen) (e2p_remOps cap ptsLen * 9789) 2560) := by
  have hsum := e2p_doneOps_add_remOps cap hpts
  have hseq : FitsEnv M lim st0
      (SeqEnv (SpqrTightEvs (e2p_doneOps cap ptsLen) (e2p_doneOps cap ptsLen * 9789) 2560)
              (SpqrTightEvs (e2p_remOps cap ptsLen) (e2p_remOps cap ptsLen * 9789) 2560)) :=
    FitsEnv.mono (fun _ h => (SpqrTightEvs.seq h).mono (by omega)
      (by omega) (Nat.le_refl 2560)) hFit0
  exact hst_cur ▸ hseq.seq_right hevs_acc

theorem e2p_fitsEnv_decodeVarint2_of_some {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {bs : List (BitVec 8)} {p : BitVec 64 × List (BitVec 8)} {n c r : Nat}
    (hd : decodeVarint bs = some p) (hFit : FitsEnv M lim st (SpqrTightEvs n c r)) :
    FitsEnv M lim st (DecodeVarint2Env bs) :=
  FitsEnv.mono (fun evs h => by
    have hnil : evs = [] := by
      simpa [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hd] using h
    subst hnil; exact SpqrTightEvs.nil n c r) hFit

theorem e2p_fitsEnv_skipField3_of_some {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {iwt : WireType} {tag : Nat} {bufRef slot ptr : BitVec 64} {rest rest' : List (BitVec 8)}
    {n c r : Nat}
    (hsf : skipField (2 * rest.length + 2) 97 tag iwt rest = some rest')
    (hFit : FitsEnv M lim st (SpqrTightEvs n c r)) :
    FitsEnv M lim st (SkipField3Env ⟨iwt, tag, 97, bufRef, slot, ptr, rest⟩) :=
  FitsEnv.mono (fun evs h => by
    have hnil : evs = [] := by
      change SkipFieldEnv _ evs at h
      simpa [SkipFieldEnv, skipFieldEventsCore, hsf] using h
    subst hnil; exact SpqrTightEvs.nil n c r) hFit

/-! ## 2. Pinned `PolynomialDecoder` Unfolding, Push Fold, & Loop Bundle -/

private theorem e2p_protoPolynomialDecoderPinnedAt_unfold_pts (A : RustAlloc)
    (cap ptr a : BitVec 64) (m : PolynomialDecoder) :
    protoPolynomialDecoderPinnedAt A ⟨⟨cap, ptr⟩⟩ a (polyDecoderToProto m) =
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 m.pts.length) ∗
        ⌜m.pts.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr m.pts ∗
           memRegion (ptr + BitVec.ofNat 64 (m.pts.length * 24)) ((cap.toNat - m.pts.length) * 24))) ∗
      ((a + protoPolynomialDecoderPtsNeededOff) ↦₃₂ m.ptsNeeded) ∗
      ((a + protoPolynomialDecoderPolysOff) ↦₃₂ m.polys) ∗
      ((a + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte m.isComplete) ∗
      memRegion (a + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize := by
  unfold protoPolynomialDecoderPinnedAt polyDecoderToProto vecVecU8PinnedAt vecHeaderBytes
    vecAt vecHeader vecBuf
  simp only [sepConj_assoc]

private theorem e2p_vecVecU8PinnedAt_after_push (A : RustAlloc)
    (vecAddr cap' ptr' cap_e ptr_e : BitVec 64) (bss : List (List (BitVec 8))) (v : List (BitVec 8))
    (hlt : bss.length < cap'.toNat) (hbound : cap'.toNat * 24 < 2 ^ 63) (hptr : ptr' ≠ 0) :
    (vecAddr ↦₆₄ cap') ∗ ((vecAddr + 8#64) ↦₆₄ ptr') ∗
      ((vecAddr + 16#64) ↦₆₄ BitVec.ofNat 64 (bss.length + 1)) ∗
      A.live ptr' (cap'.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr' bss ∗
      ((ptr' + BitVec.ofNat 64 (bss.length * 24)) ↦₆₄ cap_e) ∗
      ((ptr' + BitVec.ofNat 64 (bss.length * 24) + 8#64) ↦₆₄ ptr_e) ∗
      ((ptr' + BitVec.ofNat 64 (bss.length * 24) + 16#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗
      vecU8Buf A cap_e ptr_e v ∗
      memRegion (ptr' + BitVec.ofNat 64 ((bss.length + 1) * 24)) ((cap'.toNat - (bss.length + 1)) * 24) ⊢
    vecVecU8PinnedAt A ⟨cap', ptr'⟩ vecAddr (bss ++ [v]) := by
  unfold vecVecU8PinnedAt vecHeaderBytes vecAt vecHeader vecBuf
  have hcap_ne0 : cap' ≠ 0 := by intro h0; subst h0; change bss.length < 0 at hlt; omega
  have hlen_app : (bss ++ [v]).length = bss.length + 1 := by simp
  simp only [hlen_app, hcap_ne0, ite_false]
  rw [pure_sepConj_of_true ⟨by omega, hbound, hptr⟩,
    arrayAt_append_singleton (fun bs addr => vecU8 A addr bs) 24 ptr' bss v]
  let elemAddr := ptr' + BitVec.ofNat 64 (bss.length * 24)
  have helem :
      (elemAddr ↦₆₄ cap_e) ∗ ((elemAddr + 8#64) ↦₆₄ ptr_e) ∗
        ((elemAddr + 16#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗ vecU8Buf A cap_e ptr_e v ⊢
      vecU8 A elemAddr v := by
    have hhdr :
        (elemAddr ↦₆₄ cap_e) ∗ ((elemAddr + 8#64) ↦₆₄ ptr_e) ∗
          ((elemAddr + 16#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗ vecU8Buf A cap_e ptr_e v =
        vecU8At A elemAddr cap_e ptr_e v := by
      rw [vecU8At_eq_header_sep_buf]; unfold vecHeader; ac_rfl
    rw [hhdr]; unfold vecU8
    refine Entails.trans ?_
      (Entails.sepExists_intro (P := fun c => ∃∗ p, vecU8At A elemAddr c p v) cap_e)
    exact Entails.sepExists_intro (P := fun p => vecU8At A elemAddr cap_e p v) ptr_e
  have hpull1 :
      (vecAddr ↦₆₄ cap') ∗ ((vecAddr + 8#64) ↦₆₄ ptr') ∗
        ((vecAddr + 16#64) ↦₆₄ BitVec.ofNat 64 (bss.length + 1)) ∗
        A.live ptr' (cap'.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr' bss ∗
        (elemAddr ↦₆₄ cap_e) ∗ ((elemAddr + 8#64) ↦₆₄ ptr_e) ∗
        ((elemAddr + 16#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗ vecU8Buf A cap_e ptr_e v ∗
        memRegion (ptr' + BitVec.ofNat 64 ((bss.length + 1) * 24)) ((cap'.toNat - (bss.length + 1)) * 24) =
      ((elemAddr ↦₆₄ cap_e) ∗ ((elemAddr + 8#64) ↦₆₄ ptr_e) ∗
        ((elemAddr + 16#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗ vecU8Buf A cap_e ptr_e v) ∗
      ((vecAddr ↦₆₄ cap') ∗ ((vecAddr + 8#64) ↦₆₄ ptr') ∗
        ((vecAddr + 16#64) ↦₆₄ BitVec.ofNat 64 (bss.length + 1)) ∗
        A.live ptr' (cap'.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr' bss ∗
        memRegion (ptr' + BitVec.ofNat 64 ((bss.length + 1) * 24)) ((cap'.toNat - (bss.length + 1)) * 24)) := by
    ac_rfl
  have hpull2 :
      ((vecAddr ↦₆₄ cap') ∗ ((vecAddr + 8#64) ↦₆₄ ptr') ∗
        ((vecAddr + 16#64) ↦₆₄ BitVec.ofNat 64 (bss.length + 1))) ∗
        (A.live ptr' (cap'.toNat * 24) 8 ∗
          (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr' bss ∗ vecU8 A elemAddr v) ∗
          memRegion (ptr' + BitVec.ofNat 64 ((bss.length + 1) * 24)) ((cap'.toNat - (bss.length + 1)) * 24)) =
      vecU8 A elemAddr v ∗
        ((vecAddr ↦₆₄ cap') ∗ ((vecAddr + 8#64) ↦₆₄ ptr') ∗
          ((vecAddr + 16#64) ↦₆₄ BitVec.ofNat 64 (bss.length + 1)) ∗
          A.live ptr' (cap'.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr' bss ∗
          memRegion (ptr' + BitVec.ofNat 64 ((bss.length + 1) * 24)) ((cap'.toNat - (bss.length + 1)) * 24)) := by
    ac_rfl
  rw [hpull1]; refine Entails.trans (sepConj_mono_left helem) (Entails.of_eq hpull2.symm)

private theorem e2p_pinned_entails_unpinned (A : RustAlloc) (g : ProtoPolynomialDecoderGhost)
    (a : BitVec 64) (pb : ProtoPolynomialDecoder) :
    protoPolynomialDecoderPinnedAt A g a pb ⊢ protoPolynomialDecoderAt A a pb := by
  rw [protoPolynomialDecoderAt_eq_exists_pinned]
  exact Entails.sepExists_right g (Entails.refl _)

def e2p_polyDecoderPinnedLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State) (g : ProtoPolynomialDecoderGhost)
    (msgPtr bufRef slot ptr : BitVec 64)
    (m : PolynomialDecoder) (bs cur : List (BitVec 8)) : SepProp :=
  stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗
    memRegion (s0.sp - 128#64) 48 ∗ polySavedRegsAny s0.sp s0 ∗
    protoPolynomialDecoderPinnedAt A.repAlloc g msgPtr (polyDecoderToProto m) ∗
    (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗ A.pool lim st s

/-! ## 3. Canonical-Domain Per-Tag, Key-Decode, & Loop Step Lemmas -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem e2p_tag3_copy_step_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyDecoderMergeGhost → List AllocEvent → Prop}
    {x : PolyDecoderMergeGhost} {st0 st_next : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder}
    {v rest' : List (BitVec 8)} {limit : Nat} {v_stk0 cap' ptr' cap_e ptr_e : BitVec 64}
    (_hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlt : m.pts.length < cap'.toNat) (hbound : cap'.toNat * 24 < 2 ^ 63) (hptr : ptr' ≠ 0)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_296).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (e2p_polyDecoderPinnedLoopPre A lim st_next s0 s' ⟨⟨cap', ptr'⟩⟩
          x.msgPtr x.bufRef x.slot x.ptr { m with pts := m.pts ++ [v] } x.bs rest')
        (WppPost (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_296).base + 432#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 m.pts.length)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 160#64) ↦₆₄ v_stk0) ∗ vecU8At A.repAlloc (s0.sp - 152#64) cap_e ptr_e v ∗
        (x.msgPtr ↦₆₄ cap') ∗ ((x.msgPtr + 8#64) ↦₆₄ ptr') ∗
        ((x.msgPtr + 16#64) ↦₆₄ BitVec.ofNat 64 m.pts.length) ∗
        A.repAlloc.live ptr' (cap'.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptr' m.pts ∗
        memRegion (ptr' + BitVec.ofNat 64 (m.pts.length * 24)) ((cap'.toNat - m.pts.length) * 24) ∗
        ((x.msgPtr + protoPolynomialDecoderPtsNeededOff) ↦₃₂ m.ptsNeeded) ∗
        ((x.msgPtr + protoPolynomialDecoderPolysOff) ↦₃₂ m.polys) ∗
        ((x.msgPtr + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte m.isComplete) ∗
        memRegion (x.msgPtr + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize ∗
        stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
        polySavedRegsAny s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest' ∗ A.pool lim st_next s)
      (WppPost (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 164#64) hinv
  conv => arg 4; rw [vecU8At_stack_to_cells A.repAlloc s0.sp cap_e ptr_e v,
    memRegion_split_24_cells ptr' m.pts.length cap'.toNat hlt hbound]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w0
  wp_steps_sync_pool ((blkPl_296).base + 164#64)
  simp only [State.setMem_setMem]
  apply SepWP.fold
    (cells160_entails_memRegion32 s0.sp v_stk0 cap_e ptr_e (BitVec.ofNat 64 v.length)) (by sep_focus)
  apply SepWP.fold
    (e2p_vecVecU8PinnedAt_after_push A.repAlloc x.msgPtr cap' ptr' cap_e ptr_e m.pts v hlt hbound hptr)
    (by sep_focus)
  wp_reach; intro hinvm
  refine SepWPp.weaken_pre
    (Entails.of_eq (by
      dsimp only [e2p_polyDecoderPinnedLoopPre, protoPolynomialDecoderPinnedAt, polyDecoderToProto]
      sep_ac_rfl))
    (hcont _
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
       by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩ hinvm)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 600000 in
set_option linter.unusedSimpArgs false in
private theorem e2p_tag3_step_dom_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyDecoderMergeGhost → List AllocEvent → Prop}
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim)))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {cap ptr : BitVec 64} {m : PolynomialDecoder}
    {rest v rest' : List (BitVec 8)} {limit : Nat}
    {evs_acc : List AllocEvent}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hpts_bound : m.pts.length + rest.length < 2 ^ 56) (hrest_suf : IsDropSuffix x.bs rest)
    (hmb : mergeBytes .lengthDelimited rest = some (v, rest'))
    (hv_le : v.length ≤ 2560) (hpts_lt16 : m.pts.length < 16)
    (hv_cap : e2p_ValidPolyVecCap cap.toNat)
    (hevs_acc : SpqrTightEvs (e2p_doneOps cap.toNat m.pts.length)
      (e2p_doneOps cap.toNat m.pts.length * 9789) 2560 evs_acc)
    (hst_cur : st_cur = M.stepEvents evs_acc st0)
    (hfits_rem : FitsEnv M lim st_cur
      (SpqrTightEvs (e2p_remOps cap.toNat m.pts.length)
        (e2p_remOps cap.toNat m.pts.length * 9789) 2560))
    (hcont : ∀ (cap' ptr' : BitVec 64) (st_next : M.σ) (evs_step : List AllocEvent) (s' : State),
      e2p_ValidPolyVecCap cap'.toNat →
      SpqrTightEvs (e2p_doneOps cap'.toNat (m.pts.length + 1))
        (e2p_doneOps cap'.toNat (m.pts.length + 1) * 9789) 2560 (evs_acc ++ evs_step) →
      st_next = M.stepEvents (evs_acc ++ evs_step) st0 →
      s'.pc = (blkPl_296).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (e2p_polyDecoderPinnedLoopPre A lim st_next s0 s' ⟨⟨cap', ptr'⟩⟩
          x.msgPtr x.bufRef x.slot x.ptr { m with pts := m.pts ++ [v] } x.bs rest')
        (WppPost (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_296).base + 376#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (e2p_polyDecoderPinnedLoopPre A lim st_cur s0 s ⟨⟨cap, ptr⟩⟩
        x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  dsimp [WireType.toNat] at hx0
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hrem_ge2 : 2 ≤ e2p_remOps cap.toNat m.pts.length := by
    unfold e2p_remOps; omega
  have hfits_mb : FitsEnv M lim st_cur
      (BytesMerge3Env ⟨.lengthDelimited, s0.sp - 152#64, 0#64, 1#64, [], x.bufRef, x.slot, restPtr, rest⟩) :=
    FitsEnv.mono (fun _ hb => (e2p_bytesMerge3_tight hmb hv_le hb).mono hrem_ge2
      (Nat.mul_le_mul_right 9789 hrem_ge2) (Nat.le_refl _)) hfits_rem
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
  conv => arg 4; rw [e2p_polyDecoderPinnedLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    memRegion_32_cells160 s0.sp, polyBelow_bytesMerge3 s0.sp]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_stk3; apply SepWP.exists_elim; intro v_stk2
  apply SepWP.exists_elim; intro v_stk1; apply SepWP.exists_elim; intro v_stk0
  wp_steps_sync_pool (lsmpl.base 290)
  simp only [State.setMem_setMem]
  apply SepWP.fold (Entails.of_eq (vecU8At_zero_eq_cells A.repAlloc s0.sp).symm) (by sep_focus)
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := bytesMerge3RawBudgetSpec A lim)
    (x := (⟨.lengthDelimited, s0.sp - 152#64, 0#64, 1#64, [], x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_296).base + 404#64) hBytesCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl
    ⟨by simp only [arm64_norm, hsp, hx0], by simp only [arm64_norm, hsp],
     by simp only [arm64_norm, hsp, hx19], show rest.length < 2 ^ 63 by omega, Or.inl rfl, hfits_mb⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
  have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
  conv => arg 4; dsimp only [bytesMerge3RawBudgetSpec]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro evs_mb
  conv => arg 4; simp only [hmb, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap_e; apply SepWPp.exists_elim; intro ptr_e
  conv => arg 4; rw [e2p_protoPolynomialDecoderPinnedAt_unfold_pts]
  conv => arg 4; simp only [sepConj_assoc]
  apply sepWPp_focus_pure (by sep_focus); intro htrm
  apply sepWPp_focus_pure (by sep_focus); intro hevs_mb
  apply sepWPp_focus_pure (by sep_focus); intro hsm0
  apply sepWPp_focus_pure (by sep_focus); intro _hcap_ok
  apply sepWPp_focus_pure (by sep_focus); rintro ⟨hlen_le, hcap_bound, hptr_ne⟩
  conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp]
  have hmb_tight : SpqrTightEvs 2 (2 * 9789) 2560 evs_mb :=
    e2p_bytesMerge3_tight hmb hv_le hevs_mb
  by_cases hcap_eq : m.pts.length = cap.toNat
  · have hcap_lt16 : cap.toNat < 16 := by omega
    obtain ⟨hv_new, _, hrem_grow, hdone_new⟩ := e2p_validPolyVecCap_step hv_cap hcap_lt16
    have hrem_ge3 : 3 ≤ e2p_remOps cap.toNat m.pts.length := by
      unfold e2p_remOps; omega
    have hseq_mb : FitsEnv M lim st_cur
        (SeqEnv (SpqrTightEvs 2 (2 * 9789) 2560) (SpqrTightEvs 1 9789 2560)) :=
      FitsEnv.mono (fun _ h => (SpqrTightEvs.seq h).mono hrem_ge3
        (by have := Nat.mul_le_mul_right 9789 hrem_ge3; omega) (by decide)) hfits_rem
    have hfits_mb_tail : FitsEnv M lim (M.stepEvents evs_mb st_cur) (SpqrTightEvs 1 9789 2560) :=
      hseq_mb.seq_right hmb_tight
    have hbne : (BitVec.ofNat 64 m.pts.length != cap) = false := len_eq_cap_bne_false hcap_eq
    have hgrow_bound : max (2 * cap.toNat) 4 * 24 + 8 ≤ 2 ^ 63 := by omega
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 621) hinvm
    apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecBuf_vecU8_entails_grow_pre A.repAlloc cap ptr m.pts hcap_eq) (by sep_focus)
    conv => arg 4; rw [polyBelow_extHook s0.sp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro pins
    wp_focus_pure; rintro ⟨hpins_len, hbytes_len⟩
    wp_steps_sync_pool (lsmpl.base 621)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    have hfits_grow : FitsEnv M lim (M.stepEvents evs_mb st_cur)
        (GrowOneVecU8Env ⟨x.msgPtr, cap, ptr, vecU8ArrayBytes pins m.pts⟩) :=
      FitsEnv.mono (fun _ hg => e2p_growOneVecU8_tight hv_cap hcap_lt16 hg) hfits_mb_tail
    refine SepWPp.call_frame_lscro (spec := growOneVecU8BudgetSpec M A lim)
      (x := (⟨x.msgPtr, cap, ptr, vecU8ArrayBytes pins m.pts⟩, M.stepEvents evs_mb st_cur))
      (ret_pc := (blkPl_296).base + 432#64) hGrowCall hinvm'
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      rfl
      ⟨by simp only [arm64_norm, hspm, hx20_m], hbytes_len, hptr_ne,
       by dsimp only [rawVecNewCap]; exact hgrow_bound, hfits_grow⟩
      (by dsimp only [RustCliAllocBudget.live]; sep_focus)
      (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
      (fun _ _ => wppBudgetPanic_false) ?_
    intro sm2 hpcm2 hrunm2 hspm2 hcsm2 hinvm2; simp only [CalleeSavedPreserved] at hcsm2
    obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, hvregs_2⟩ := hcsm2
    simp (config := { decide := true }) only [arm64_norm, hspm, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx26_m, hx27_m, hx28_m, hvregs_m]
      at hpcm2 hrunm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hvregs_2
    conv => arg 4; dsimp only [growOneVecU8BudgetSpec, rawVecGrowBudgetSpec]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro evs_g
    apply SepWPp.exists_elim; intro p'
    apply sepWPp_focus_pure (by sep_focus); rintro ⟨htrm2, hevs_g⟩
    apply sepWPp_focus_pure (by sep_focus); rintro ⟨hp'_ne, _⟩
    conv => arg 4; simp only [sepConj_assoc, arm64_norm, hspm]
    have hnew_toNat : (newCapVecU8 cap).toNat = max (2 * cap.toNat) 4 := by
      unfold newCapVecU8; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt_new : m.pts.length < (newCapVecU8 cap).toNat := by rw [hnew_toNat]; omega
    have hbound_new : (newCapVecU8 cap).toNat * 24 < 2 ^ 63 := by rw [hnew_toNat]; omega
    have hg_tight : SpqrTightEvs 1 9789 2560 evs_g :=
      e2p_growOneVecU8_tight hv_cap hcap_lt16 hevs_g
    have hdone_eq : e2p_doneOps (newCapVecU8 cap).toNat (m.pts.length + 1) =
        e2p_doneOps cap.toNat m.pts.length + 3 := by
      unfold e2p_doneOps; rw [hnew_toNat, hdone_new]; omega
    have hevs_next : SpqrTightEvs (e2p_doneOps (newCapVecU8 cap).toNat (m.pts.length + 1))
        (e2p_doneOps (newCapVecU8 cap).toNat (m.pts.length + 1) * 9789) 2560
        (evs_acc ++ (evs_mb ++ evs_g)) :=
      (hevs_acc.append (hmb_tight.append hg_tight)).mono (by omega)
        (by rw [hdone_eq, Nat.add_mul]) (by decide)
    have hst_next : M.stepEvents evs_g (M.stepEvents evs_mb st_cur) =
        M.stepEvents (evs_mb ++ evs_g) st_cur :=
      (AllocCostModel.stepEvents_append M evs_mb evs_g st_cur).symm
    have hst_tot : M.stepEvents (evs_mb ++ evs_g) st_cur =
        M.stepEvents (evs_acc ++ (evs_mb ++ evs_g)) st0 := by
      rw [hst_cur, ← AllocCostModel.stepEvents_append]
    conv => arg 4; dsimp only [rawVecNewCap]
    conv => arg 4; rw [show A.live p' (max (2 * cap.toNat) 4 * 24) 8 =
      A.repAlloc.live p' (max (2 * cap.toNat) 4 * 24) 8 from rfl,
      show BitVec.ofNat 64 (max (2 * cap.toNat) 4) = newCapVecU8 cap from rfl, hst_next]
    apply sepWPp_fold
      (grow_post_entails_ready A.repAlloc cap p' pins m.pts hcap_eq hpins_len hgrow_bound)
      (by sep_focus)
    apply sepWPp_fold (polyBelow_extHook_entails s0.sp) (by sep_focus)
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (e2p_tag3_copy_step_cro (st_next := M.stepEvents (evs_mb ++ evs_g) st_cur)
        (v_stk0 := v_stk0) (cap' := newCapVecU8 cap) (ptr' := p')
        (cap_e := cap_e) (ptr_e := ptr_e) hsp_align hlt_new hbound_new hp'_ne
        (fun s' => hcont (newCapVecU8 cap) p' _ (evs_mb ++ evs_g) s'
          (hnew_toNat ▸ hv_new) hevs_next hst_tot)
        hpcm2 hrunm2 hspm2 (htrm2.trans (htrm.trans htr))
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2
        (hx25_2.trans (by rw [hcap_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]))
        ⟨hx26_2, hx27_2, hx28_2, hvregs_2⟩ hinvm2)
  · have hlt : m.pts.length < cap.toNat := Nat.lt_of_le_of_ne hlen_le hcap_eq
    have hbne : (BitVec.ofNat 64 m.pts.length != cap) = true := len_lt_cap_bne_true hlt
    have hcap_ne0 : cap ≠ 0 := by intro h0; subst h0; change m.pts.length < 0 at hlt; omega
    have hdone_eq : e2p_doneOps cap.toNat (m.pts.length + 1) =
        e2p_doneOps cap.toNat m.pts.length + 2 := by
      unfold e2p_doneOps; omega
    have hevs_next : SpqrTightEvs (e2p_doneOps cap.toNat (m.pts.length + 1))
        (e2p_doneOps cap.toNat (m.pts.length + 1) * 9789) 2560 (evs_acc ++ evs_mb) :=
      (hevs_acc.append hmb_tight).mono (by omega)
        (by rw [hdone_eq, Nat.add_mul]) (by decide)
    have hst_tot : M.stepEvents evs_mb st_cur = M.stepEvents (evs_acc ++ evs_mb) st0 := by
      rw [hst_cur, ← AllocCostModel.stepEvents_append]
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 432#64) hinvm
    (conv => arg 4; simp only [hcap_ne0, ↓reduceIte, sepConj_assoc])
    apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps_sync_pool ((blkPl_296).base + 432#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre
      (Entails.of_eq (by
        rw [show A.live ptr (cap.toNat * 24) 8 = A.repAlloc.live ptr (cap.toNat * 24) 8 from rfl]
        sep_ac_rfl))
      (e2p_tag3_copy_step_cro (st_next := M.stepEvents evs_mb st_cur)
        (v_stk0 := v_stk0) (cap' := cap) (ptr' := ptr) (cap_e := cap_e) (ptr_e := ptr_e)
        hsp_align hlt hcap_bound hptr_ne
        (fun s' => hcont cap ptr _ evs_mb s' hv_cap hevs_next hst_tot)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
        (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
         by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')

set_option maxRecDepth 200000 in
set_option maxHeartbeats 600000 in
set_option linter.unusedSimpArgs false in
private theorem e2p_loop_dom_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {maxOps : Nat}
    (hOps : 35 ≤ maxOps)
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim)))
    {x : PolyDecoderMergeGhost} {st0 : M.σ} {R : SepProp} {s0 : State}
    {pb : PolynomialDecoder} {rest_fin : List (BitVec 8)} {limit : Nat}
    (hDom : tlb_PolyDecoderDom x)
    (hpb : tlb_ValidPolyDecoderPB pb)
    (hsome_top : (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      some (pb, rest_fin))
    (hFit0 : FitsEnv M lim st0 (SpqrTightEvs maxOps 342615 2560))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    ∀ (n : Nat) (cap ptr : BitVec 64) (m : PolynomialDecoder) (cur : List (BitVec 8))
        (st_cur : M.σ) (evs_acc : List AllocEvent) (s : State),
      cur.length ≤ n →
      cur.length ≤ x.bs.length →
      m.pts.length + cur.length < 2 ^ 56 →
      IsDropSuffix x.bs cur →
      e2p_ValidPolyVecCap cap.toNat →
      SpqrTightEvs (e2p_doneOps cap.toNat m.pts.length)
        (e2p_doneOps cap.toNat m.pts.length * 9789) 2560 evs_acc →
      st_cur = M.stepEvents evs_acc st0 →
      (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        (mergeLoopBin PolynomialDecoder.mergeField (cur.length - limit) m cur limit 97).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (blkPl_296).base + 164#64 →
      s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
        (e2p_polyDecoderPinnedLoopPre A lim st_cur s0 s ⟨⟨cap, ptr⟩⟩
          x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (polyDecoderMergeSpecOfEnv A lim
          (tlb_PolyDecoderGuardedEnvOf maxOps) (tlb_PolyDecoderGuardedEnvOf maxOps)) (x, st0) R s0)
        (WppBudgetPanic (polyDecoderMergeSpecOfEnv A lim
          (tlb_PolyDecoderGuardedEnvOf maxOps) (tlb_PolyDecoderGuardedEnvOf maxOps)) (x, st0) R s0) := by
  intro n; induction n with
  | zero =>
    intro cap ptr m cur st_cur evs_acc s hcur_n hcur_le _ hcur_suf _ hevs_acc hst_cur hres_cur
      hpc hrun hsp htr _ _ hx21 hx22 _ _ hcs hinv
    have hle_lim : cur.length ≤ limit := by omega
    have heq_lim : cur.length = limit := by
      by_contra hne
      have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim hne
      rw [hsome_top, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim, Option.map_none] at hres_cur
      cases hres_cur
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by
      rw [← heq_lim]; exact hcur_suf.symm
    have hsome :
        (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
          some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    have hm_eq : m = pb := by
      rw [hsome_top] at hsome; exact (Prod.mk.inj (Option.some.inj hsome.symm)).1
    have hpts_le16 : m.pts.length ≤ 16 := hm_eq ▸ hpb.1
    have hdone_le : e2p_doneOps cap.toNat m.pts.length ≤ 35 := by
      have := e2p_doneOps_add_remOps cap.toNat hpts_le16; omega
    have hevs_post : tlb_PolyDecoderGuardedEnvOf maxOps x evs_acc :=
      Or.inl ⟨hDom, hevs_acc.mono (Nat.le_trans hdone_le hOps)
        (Nat.le_trans (Nat.mul_le_mul_right 9789 hdone_le) (by decide : 35 * 9789 ≤ 342615))
        (Nat.le_refl _)⟩
    obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
    subst hst_cur
    apply SepWPp.of_sepWP_ret
    unfold WppPost polyDecoderMergeSpecOfEnv
    simp only [hsome, e2p_polyDecoderPinnedLoopPre, polySavedRegsAny, polySavedRegs,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp]
    apply SepWP.exists_elim; intro v_pad
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    apply SepWP.fold (e2p_pinned_entails_unpinned A.repAlloc ⟨⟨cap, ptr⟩⟩ x.msgPtr (polyDecoderToProto m))
      (by sep_focus)
    apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
    wp_done
  | succ n ih =>
    intro cap ptr m cur st_cur evs_acc s hcur_n hcur_le hpts_bound hcur_suf hv_cap hevs_acc hst_cur
      hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs hinv
    have hloop_some : mergeLoopBin PolynomialDecoder.mergeField (cur.length - limit) m cur limit 97 = some pb := by
      have h1 := hsome_top.symm.trans hres_cur
      rcases hml : mergeLoopBin PolynomialDecoder.mergeField (cur.length - limit) m cur limit 97 with _ | m'
      · simp [hml] at h1
      · simp only [hml, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
        exact congrArg some h1.1.symm
    obtain ⟨sfx_cur, hsfx_cur⟩ := e2p_mergeLoopBin_pts_prefix hloop_some
    have hpts_le16 : m.pts.length ≤ 16 := by
      have hlen := congrArg List.length hsfx_cur
      simp only [List.length_append] at hlen
      have := hpb.1; omega
    have hfits_rem := e2p_fitsEnv_rem_tight hOps hpts_le16 hFit0 hevs_acc hst_cur
    by_cases hle_lim : cur.length ≤ limit
    · have heq_lim : cur.length = limit := by
        by_contra hne
        have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim hne
        rw [mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim] at hloop_some
        cases hloop_some
      obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
      have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by
        rw [← heq_lim]; exact hcur_suf.symm
      have hsome :
          (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
            some (m, cur) := by
        rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
      have hdone_le : e2p_doneOps cap.toNat m.pts.length ≤ 35 := by
        have := e2p_doneOps_add_remOps cap.toNat hpts_le16; omega
      have hevs_post : tlb_PolyDecoderGuardedEnvOf maxOps x evs_acc :=
        Or.inl ⟨hDom, hevs_acc.mono (Nat.le_trans hdone_le hOps)
          (Nat.le_trans (Nat.mul_le_mul_right 9789 hdone_le) (by decide : 35 * 9789 ≤ 342615))
          (Nat.le_refl _)⟩
      obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
      subst hst_cur
      apply SepWPp.of_sepWP_ret
      unfold WppPost polyDecoderMergeSpecOfEnv
      simp only [hsome, e2p_polyDecoderPinnedLoopPre, polySavedRegsAny, polySavedRegs,
        sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp]
      apply SepWP.exists_elim; intro v_pad
      wp_steps_sync_pool (s0.readReg64 Reg.lr)
      simp only [State.setMem_setMem]
      apply SepWP.fold (e2p_pinned_entails_unpinned A.repAlloc ⟨⟨cap, ptr⟩⟩ x.msgPtr (polyDecoderToProto m))
        (by sep_focus)
      apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
      wp_done
    · have hcur_lt : cur.length < 2 ^ 63 := by omega
      obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
      let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
      obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hle_lim hcur_lt
      obtain ⟨⟨key, rest⟩, hd⟩ : ∃ p, decodeVarint cur = some p := by
        cases hd' : decodeVarint cur with
        | none =>
          rw [mergeLoopBin_of_decodeVarint_none protoPrefixStep_polynomialDecoder_mergeField hle_lim hd'] at hloop_some
          cases hloop_some
        | some p => exact ⟨p, rfl⟩
      have hk_ge : ¬ 2 ^ 32 ≤ key.toNat := by
        intro hge
        rw [mergeLoopBin_of_key_ge protoPrefixStep_polynomialDecoder_mergeField hle_lim hd hge] at hloop_some
        cases hloop_some
      obtain ⟨iwt, hwt⟩ : ∃ w, WireType.ofNat? (key.toNat % 8) = some w := by
        cases hw : WireType.ofNat? (key.toNat % 8) with
        | none =>
          rw [mergeLoopBin_of_wt_none protoPrefixStep_polynomialDecoder_mergeField hle_lim hd hk_ge hw] at hloop_some
          cases hloop_some
        | some w => exact ⟨w, rfl⟩
      have hitag0 : ¬ key.toNat / 8 < 1 := by
        intro h0
        rw [mergeLoopBin_of_tag_zero protoPrefixStep_polynomialDecoder_mergeField hle_lim hd hk_ge hwt h0] at hloop_some
        cases hloop_some
      have hfits_dv : FitsEnv M lim st_cur (DecodeVarint2Env cur) :=
        e2p_fitsEnv_decodeVarint2_of_some hd hfits_rem
      apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
      conv => arg 4; rw [e2p_polyDecoderPinnedLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
        sliceCursorAt, polyBelow_decodeVarint2 s0.sp]
      conv => arg 4; simp only [sepConj_assoc]
      wp_steps_sync_pool (lsmpl.base 291)
      simp only [State.setMem_setMem]
      wp_reach; intro hinv_k
      refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
        (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, st_cur))
        (ret_pc := (blkPl_296).base + 184#64) hVarintCall hinv_k
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
        rfl ⟨by simp only [arm64_norm, hsp, hx19], hcur_lt, hfits_dv⟩
        (by dsimp only [sliceCursorAt, curPtr]; rw [decodeVarint2Stack_eq]; sep_focus)
        (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
        (fun _ _ => wppBudgetPanic_false) ?_
      intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := by omega
      have hrest_suf : IsDropSuffix x.bs rest :=
        suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hshr := key_shr32_of_lt hk_ge
      obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
      obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
      obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
      obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
      have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
        rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 97)
        protoPrefixStep_polynomialDecoder_mergeField hle_lim hd hk_ge hwt hitag0
      let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hloop_ok; rw [polynomialDecoder_mergeField_tag1] at hloop_ok
        have hiwt : iwt = .varint := by
          by_contra hne; simp only [hloop_ok, hne, ↓reduceIte] at hloop_some; cases hloop_some
        subst hiwt
        obtain ⟨⟨v, rest'⟩, hdv⟩ : ∃ p, decodeVarint rest = some p := by
          cases hd' : decodeVarint rest with
          | none => simp only [hloop_ok, ↓reduceIte, hd', Option.map_none] at hloop_some; cases hloop_some
          | some p => exact ⟨p, rfl⟩
        have hfits_dv1 : FitsEnv M lim st_cur (DecodeVarint2Env rest) :=
          e2p_fitsEnv_decodeVarint2_of_some hdv hfits_rem
        apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinvm
        conv => arg 4; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
        conv => arg 4; rw [decodeVarint2_pool_of_some A lim hd, decodeVarint2Stack_eq]
        conv => arg 4; simp only [hd, sepConj_assoc]
        wp_focus_pure; rintro ⟨hsm0, hsm1⟩; wp_focus_pure; intro htrm
        conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp]
        apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, polyBelow_decodeVarint2 s0.sp]
        conv => arg 4; simp only [sepConj_assoc, hsm1, hand_wt, hw1, hw1_2, hw1_zext1, hw1_zext2, htag1]
        wp_steps_sync_pool (lsmpl.base 291)
        simp only [State.setMem_setMem]; wp_reach; intro hinvm2
        refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
          (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, st_cur))
          (ret_pc := (blkPl_296).base + 356#64) hVarintCall hinvm2
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
          rfl ⟨by simp only [arm64_norm, hspm, hx19_m], hrest_lt, hfits_dv1⟩
          (by rw [decodeVarint2Stack_eq]; sep_focus)
          (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
          (fun _ _ => wppBudgetPanic_false) ?_
        intro sm2 hpcm2 hrunm2 hspm2 hcsm2 hinvm3; simp only [CalleeSavedPreserved] at hcsm2
        obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, _, hx26_2, hx27_2, hx28_2, _, hvregs_2⟩ := hcsm2
        simp (config := { decide := true }) only [arm64_norm, hspm, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx26_m, hx27_m, hx28_m, hvregs_m]
          at hpcm2 hrunm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx26_2 hx27_2 hx28_2 hvregs_2
        have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv
        have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 164#64) hinvm3
        conv => arg 4; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
        conv => arg 4; rw [decodeVarint2_pool_of_some A lim hdv, decodeVarint2Stack_eq]
        conv => arg 4; simp only [hdv, sepConj_assoc]
        wp_focus_pure; rintro ⟨hsm2_0, hsm2_1⟩; wp_focus_pure; intro htrm2
        conv => arg 4; simp only [protoPolynomialDecoderPinnedAt, protoPolynomialDecoderPtsNeededOff,
          sepConj_assoc, arm64_norm, hspm2]
        apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        wp_steps_sync_pool ((blkPl_296).base + 164#64)
        simp only [State.setMem_setMem]; wp_reach; intro hinvm4
        have hres_next :
            (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
              (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit)
                { m with ptsNeeded := v.truncate 32 } rest' limit 97).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
          simp only [hres_cur, hloop_ok, ↓reduceIte, hdv, Option.map_some]
        refine SepWPp.weaken_pre
          (Entails.of_eq (by
            dsimp only [e2p_polyDecoderPinnedLoopPre, protoPolynomialDecoderPinnedAt,
              protoPolynomialDecoderPtsNeededOff]
            sep_ac_rfl))
          (ih cap ptr { m with ptsNeeded := v.truncate 32 } rest' st_cur evs_acc _
            (by omega) (by omega) (by dsimp; omega)
            (suffix_trans hrest_le hrest_suf hrest'_le (decodeVarint_suffix hdv))
            hv_cap hevs_acc hst_cur hres_next
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm2]) (by simp only [arm64_norm, hspm2])
            (by simp only [arm64_norm, htrm2, htrm, htr])
            (by simp only [arm64_norm, hx19_2]) (by simp only [arm64_norm, hx20_2])
            (by simp only [arm64_norm, hx21_2]) (by simp only [arm64_norm, hx22_2])
            (by simp only [arm64_norm, hx23_2]) (by simp only [arm64_norm, hx24_2])
            ⟨by simp only [arm64_norm, hx26_2], by simp only [arm64_norm, hx27_2],
             by simp only [arm64_norm, hx28_2], by simp only [arm64_norm, hvregs_2]⟩ hinvm4)
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hloop_ok; rw [polynomialDecoder_mergeField_tag2] at hloop_ok
          have hiwt : iwt = .varint := by
            by_contra hne; simp only [hloop_ok, hne, ↓reduceIte] at hloop_some; cases hloop_some
          subst hiwt
          obtain ⟨⟨v, rest'⟩, hdv⟩ : ∃ p, decodeVarint rest = some p := by
            cases hd' : decodeVarint rest with
            | none => simp only [hloop_ok, ↓reduceIte, hd', Option.map_none] at hloop_some; cases hloop_some
            | some p => exact ⟨p, rfl⟩
          have hfits_dv2 : FitsEnv M lim st_cur (DecodeVarint2Env rest) :=
            e2p_fitsEnv_decodeVarint2_of_some hdv hfits_rem
          apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinvm
          conv => arg 4; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
          conv => arg 4; rw [decodeVarint2_pool_of_some A lim hd, decodeVarint2Stack_eq]
          conv => arg 4; simp only [hd, sepConj_assoc]
          wp_focus_pure; rintro ⟨hsm0, hsm1⟩; wp_focus_pure; intro htrm
          conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp]
          apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, polyBelow_decodeVarint2 s0.sp]
          conv => arg 4; simp only [sepConj_assoc, hsm1, hand_wt, hw1, hw1_2, hw1_zext1, hw1_zext2, htag2]
          wp_steps_sync_pool (lsmpl.base 291)
          simp only [State.setMem_setMem]; wp_reach; intro hinvm2
          refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
            (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, st_cur))
            (ret_pc := (blkPl_296).base + 252#64) hVarintCall hinvm2
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
            (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
            rfl ⟨by simp only [arm64_norm, hspm, hx19_m], hrest_lt, hfits_dv2⟩
            (by rw [decodeVarint2Stack_eq]; sep_focus)
            (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
            (fun _ _ => wppBudgetPanic_false) ?_
          intro sm2 hpcm2 hrunm2 hspm2 hcsm2 hinvm3; simp only [CalleeSavedPreserved] at hcsm2
          obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, _, hx26_2, hx27_2, hx28_2, _, hvregs_2⟩ := hcsm2
          simp (config := { decide := true }) only [arm64_norm, hspm, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx26_m, hx27_m, hx28_m, hvregs_m]
            at hpcm2 hrunm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx26_2 hx27_2 hx28_2 hvregs_2
          have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv
          have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 164#64) hinvm3
          conv => arg 4; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
          conv => arg 4; rw [decodeVarint2_pool_of_some A lim hdv, decodeVarint2Stack_eq]
          conv => arg 4; simp only [hdv, sepConj_assoc]
          wp_focus_pure; rintro ⟨hsm2_0, hsm2_1⟩; wp_focus_pure; intro htrm2
          conv => arg 4; simp only [protoPolynomialDecoderPinnedAt, protoPolynomialDecoderPolysOff,
            sepConj_assoc, arm64_norm, hspm2]
          apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
          wp_steps_sync_pool ((blkPl_296).base + 164#64)
          simp only [State.setMem_setMem]; wp_reach; intro hinvm4
          have hres_next :
              (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit)
                  { m with polys := v.truncate 32 } rest' limit 97).map
                    (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, ↓reduceIte, hdv, Option.map_some]
          refine SepWPp.weaken_pre
            (Entails.of_eq (by
              dsimp only [e2p_polyDecoderPinnedLoopPre, protoPolynomialDecoderPinnedAt,
                protoPolynomialDecoderPolysOff]
              sep_ac_rfl))
            (ih cap ptr { m with polys := v.truncate 32 } rest' st_cur evs_acc _
              (by omega) (by omega) (by dsimp; omega)
              (suffix_trans hrest_le hrest_suf hrest'_le (decodeVarint_suffix hdv))
              hv_cap hevs_acc hst_cur hres_next
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm2]) (by simp only [arm64_norm, hspm2])
              (by simp only [arm64_norm, htrm2, htrm, htr])
              (by simp only [arm64_norm, hx19_2]) (by simp only [arm64_norm, hx20_2])
              (by simp only [arm64_norm, hx21_2]) (by simp only [arm64_norm, hx22_2])
              (by simp only [arm64_norm, hx23_2]) (by simp only [arm64_norm, hx24_2])
              ⟨by simp only [arm64_norm, hx26_2], by simp only [arm64_norm, hx27_2],
               by simp only [arm64_norm, hx28_2], by simp only [arm64_norm, hvregs_2]⟩ hinvm4)
        · by_cases htag3 : key.toNat / 8 = 3
          · rw [htag3] at hloop_ok; rw [polynomialDecoder_mergeField_tag3] at hloop_ok
            have hiwt : iwt = .lengthDelimited := by
              by_contra hne
              rw [mergeBytes_eq_none_of_ne_len hne] at hloop_ok
              simp only [hloop_ok, Option.map_none] at hloop_some; cases hloop_some
            subst hiwt
            obtain ⟨⟨v, rest'⟩, hmb⟩ : ∃ p, mergeBytes .lengthDelimited rest = some p := by
              cases hm' : mergeBytes .lengthDelimited rest with
              | none => simp only [hloop_ok, hm', Option.map_none] at hloop_some; cases hloop_some
              | some p => exact ⟨p, rfl⟩
            have hloop_next : mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit)
                { m with pts := m.pts ++ [v] } rest' limit 97 = some pb := by
              simpa only [hloop_ok, hmb, Option.map_some] using hloop_some
            obtain ⟨sfx_next, hsfx_next⟩ := e2p_mergeLoopBin_pts_prefix hloop_next
            have hv_le : v.length ≤ 2560 := by
              apply hpb.2 v
              rw [hsfx_next]; simp
            have hpts_lt16 : m.pts.length < 16 := by
              have hlen := congrArg List.length hsfx_next
              simp only [List.length_append, List.length_singleton] at hlen
              have := hpb.1; omega
            have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
            have hmb_len := mergeBytes_len_bound hmb
            apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 376#64) hinvm
            conv => arg 4; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
            conv => arg 4; rw [decodeVarint2_pool_of_some A lim hd, decodeVarint2Stack_eq]
            conv => arg 4; simp only [hd, sepConj_assoc]
            wp_focus_pure; rintro ⟨hsm0, hsm1⟩; wp_focus_pure; intro htrm
            conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp, hsm1, hand_wt, hw1, hw1_2,
              hw1_zext1, hw1_zext2, htag3]
            apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
            apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
            wp_steps_sync_pool ((blkPl_296).base + 376#64)
            simp only [State.setMem_setMem]; wp_reach; intro hinvm2
            have hres_next :
                (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                  (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit)
                    { m with pts := m.pts ++ [v] } rest' limit 97).map
                      (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              simp only [hres_cur, hloop_ok, hmb, Option.map_some]
            refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [e2p_polyDecoderPinnedLoopPre]; sep_ac_rfl))
              (e2p_tag3_step_dom_cro (limit := limit) hBytesCall hGrowCall
                hsp_align hrest_le (by omega) hrest_suf hmb hv_le hpts_lt16 hv_cap
                hevs_acc hst_cur hfits_rem
                (fun cap' ptr' st_next evs_step s'' hv_cap' hevs_next hst_next
                    hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' =>
                  ih cap' ptr' { m with pts := m.pts ++ [v] } rest' st_next (evs_acc ++ evs_step) s''
                    (by omega) (by omega) (by simp; omega)
                    (suffix_trans hrest_le hrest_suf hrest'_le (mergeBytes_suffix hmb))
                    hv_cap' (by simpa only [List.length_append, List.length_singleton] using hevs_next)
                    hst_next hres_next
                    hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'')
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
                (by simp only [arm64_norm, htrm, htr])
                (by simp only [arm64_norm, hsm1, hand_wt])
                (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
                (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
                (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
                ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
                 by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm2)
          · by_cases htag4 : key.toNat / 8 = 4
            · rw [htag4] at hloop_ok; rw [polynomialDecoder_mergeField_tag4] at hloop_ok
              have hiwt : iwt = .varint := by
                by_contra hne; simp only [hloop_ok, hne, ↓reduceIte] at hloop_some; cases hloop_some
              subst hiwt
              obtain ⟨⟨v, rest'⟩, hdv⟩ : ∃ p, decodeVarint rest = some p := by
                cases hd' : decodeVarint rest with
                | none => simp only [hloop_ok, ↓reduceIte, hd', Option.map_none] at hloop_some; cases hloop_some
                | some p => exact ⟨p, rfl⟩
              have hfits_dv4 : FitsEnv M lim st_cur (DecodeVarint2Env rest) :=
                e2p_fitsEnv_decodeVarint2_of_some hdv hfits_rem
              apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinvm
              conv => arg 4; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
              conv => arg 4; rw [decodeVarint2_pool_of_some A lim hd, decodeVarint2Stack_eq]
              conv => arg 4; simp only [hd, sepConj_assoc]
              wp_focus_pure; rintro ⟨hsm0, hsm1⟩; wp_focus_pure; intro htrm
              conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp]
              apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
              conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, polyBelow_decodeVarint2 s0.sp]
              conv => arg 4; simp only [sepConj_assoc, hsm1, hand_wt, hw1, hw1_2, hw1_zext1, hw1_zext2, htag4]
              wp_steps_sync_pool (lsmpl.base 291)
              simp only [State.setMem_setMem]; wp_reach; intro hinvm2
              refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
                (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, st_cur))
                (ret_pc := (blkPl_296).base + 300#64) hVarintCall hinvm2
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
                (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
                rfl ⟨by simp only [arm64_norm, hspm, hx19_m], hrest_lt, hfits_dv4⟩
                (by rw [decodeVarint2Stack_eq]; sep_focus)
                (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
                (fun _ _ => wppBudgetPanic_false) ?_
              intro sm2 hpcm2 hrunm2 hspm2 hcsm2 hinvm3; simp only [CalleeSavedPreserved] at hcsm2
              obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, _, hx26_2, hx27_2, hx28_2, _, hvregs_2⟩ := hcsm2
              simp (config := { decide := true }) only [arm64_norm, hspm, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx26_m, hx27_m, hx28_m, hvregs_m]
                at hpcm2 hrunm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx26_2 hx27_2 hx28_2 hvregs_2
              have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv
              have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
              apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 164#64) hinvm3
              conv => arg 4; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
              conv => arg 4; rw [decodeVarint2_pool_of_some A lim hdv, decodeVarint2Stack_eq]
              conv => arg 4; simp only [hdv, sepConj_assoc]
              wp_focus_pure; rintro ⟨hsm2_0, hsm2_1⟩; wp_focus_pure; intro htrm2
              conv => arg 4; simp only [protoPolynomialDecoderPinnedAt,
                protoPolynomialDecoderIsCompleteOff, sepConj_assoc, arm64_norm, hspm2]
              apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
              wp_steps_sync_pool ((blkPl_296).base + 164#64)
              simp only [State.setMem_setMem]; wp_reach; intro hinvm4
              have hres_next :
                  (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                    (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit)
                      { m with isComplete := v != 0#64 } rest' limit 97).map
                        (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
                simp only [hres_cur, hloop_ok, ↓reduceIte, hdv, Option.map_some]
              refine SepWPp.weaken_pre
                (Entails.of_eq (by
                  dsimp only [e2p_polyDecoderPinnedLoopPre, protoPolynomialDecoderPinnedAt,
                    protoPolynomialDecoderIsCompleteOff]
                  sep_ac_rfl))
                (ih cap ptr { m with isComplete := v != 0#64 } rest' st_cur evs_acc _
                  (by omega) (by omega) (by dsimp; omega)
                  (suffix_trans hrest_le hrest_suf hrest'_le (decodeVarint_suffix hdv))
                  hv_cap hevs_acc hst_cur hres_next
                  (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm2]) (by simp only [arm64_norm, hspm2])
                  (by simp only [arm64_norm, htrm2, htrm, htr])
                  (by simp only [arm64_norm, hx19_2]) (by simp only [arm64_norm, hx20_2])
                  (by simp only [arm64_norm, hx21_2]) (by simp only [arm64_norm, hx22_2])
                  (by simp only [arm64_norm, hx23_2]) (by simp only [arm64_norm, hx24_2])
                  ⟨by simp only [arm64_norm, hx26_2], by simp only [arm64_norm, hx27_2],
                   by simp only [arm64_norm, hx28_2], by simp only [arm64_norm, hvregs_2]⟩ hinvm4)
            · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
              obtain ⟨hslt1, hslt2⟩ := slt_two_ofNat32_true (n := key.toNat / 8) (by omega) (by omega)
              obtain ⟨hb3_1, _⟩ := itag_beq_tag_false htag3 hitag_lt (by decide : 3 < 2 ^ 32)
              obtain ⟨hb4_1, _⟩ := itag_beq_tag_false htag4 hitag_lt (by decide : 4 < 2 ^ 32)
              have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 3#32) = false := by
                rw [sf_truncate32_ofNat64]; exact hb3_1
              have hb4_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 4#32) = false := by
                rw [sf_truncate32_ofNat64]; exact hb4_1
              have hb4_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 4#32) = true := by
                simp only [bne, hb4_1, Bool.not_false]
              have hb4_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 4#32) = true := by
                simp only [bne, hb4_2, Bool.not_false]
              rw [polynomialDecoder_mergeField_other m iwt rest 97 hitag_lt htag1 htag2 htag3 htag4] at hloop_ok
              obtain ⟨rest', hsf⟩ : ∃ r, skipField (2 * rest.length + 2) 97 (key.toNat / 8) iwt rest = some r := by
                cases hs' : skipField (2 * rest.length + 2) 97 (key.toNat / 8) iwt rest with
                | none => rw [hloop_ok, hs', Option.map_none] at hloop_some; cases hloop_some
                | some r => exact ⟨r, rfl⟩
              have hfits_sf := e2p_fitsEnv_skipField3_of_some (bufRef := x.bufRef) (slot := x.slot)
                (ptr := restPtr) hsf hfits_rem
              apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 263) hinvm
              conv => arg 4; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
              conv => arg 4; rw [decodeVarint2_pool_of_some A lim hd, decodeVarint2Stack_eq]
              conv => arg 4; simp only [hd, sepConj_assoc]
              wp_focus_pure; rintro ⟨hsm0, hsm1⟩; wp_focus_pure; intro htrm
              conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp]
              apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
              conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf]
              conv => arg 4; simp only [sepConj_assoc, hsm1, hand_wt, hw1, hw1_2, hw1_zext1, hw1_zext2]
              wp_steps_sync_pool (lsmpl.base 263)
              simp only [State.setMem_setMem]; wp_reach; intro hinvm2
              refine SepWPp.call_frame_lscro (spec := skipField3Spec A lim)
                (x := (⟨iwt, key.toNat / 8, 97, x.bufRef, x.slot, restPtr, rest⟩, st_cur))
                (ret_pc := (blkPl_296).base + 332#64) hSkipCall hinvm2
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
                (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
                rfl
                ⟨by simp only [arm64_norm, hspm, hsm1, hand_wt, setWidth8_ofNat64_wt],
                 by simp only [arm64_norm, hspm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2, sf_truncate32_ofNat64],
                 hitag_lt, by simp only [arm64_norm, hspm, hx19_m],
                 by simp only [arm64_norm, hspm], (by decide : 97 < 2 ^ 32), hrest_lt, hfits_sf⟩
                (by sep_focus)
                (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
                (fun _ _ => wppBudgetPanic_false) ?_
              intro sm2 hpcm2 hrunm2 hspm2 hcsm2 hinvm3; simp only [CalleeSavedPreserved] at hcsm2
              obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, _, hx26_2, hx27_2, hx28_2, _, hvregs_2⟩ := hcsm2
              simp (config := { decide := true }) only [arm64_norm, hspm, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx26_m, hx27_m, hx28_m, hvregs_m]
                at hpcm2 hrunm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx26_2 hx27_2 hx28_2 hvregs_2
              have hrest'_le : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
              apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 164#64) hinvm3
              (conv => arg 4; simp only [skipField3Spec, hsf, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
              apply SepWP.exists_elim; intro evs_sf
              wp_focus_pure; intro htrm2; wp_focus_pure; intro hevs_sf; wp_focus_pure; intro _hsm0_sf
              have hevs_nil : evs_sf = [] := by
                change SkipFieldEnv _ evs_sf at hevs_sf
                simpa [SkipFieldEnv, skipFieldEventsCore, hsf] using hevs_sf
              subst hevs_nil
              conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hspm2]
              apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
              wp_steps_sync_pool ((blkPl_296).base + 164#64)
              simp only [State.setMem_setMem]; wp_reach; intro hinvm4
              have hres_next :
                  (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                    (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit)
                      m rest' limit 97).map (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
                simp only [hres_cur, hloop_ok, hsf, Option.map_some]
              refine SepWPp.weaken_pre
                (Entails.of_eq (by
                  dsimp only [e2p_polyDecoderPinnedLoopPre, polyBelowStack]
                  rw [hspm]
                  sep_ac_rfl))
                (ih cap ptr m rest' st_cur evs_acc _
                  (by omega) (by omega) (by omega)
                  (suffix_trans hrest_le hrest_suf hrest'_le ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
                  hv_cap hevs_acc hst_cur hres_next
                  (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm2]) (by simp only [arm64_norm, hspm2])
                  (by simp only [arm64_norm, htrm2, htrm, htr])
                  (by simp only [arm64_norm, hx19_2]) (by simp only [arm64_norm, hx20_2])
                  (by simp only [arm64_norm, hx21_2]) (by simp only [arm64_norm, hx22_2])
                  (by simp only [arm64_norm, hx23_2]) (by simp only [arm64_norm, hx24_2])
                  ⟨by simp only [arm64_norm, hx26_2], by simp only [arm64_norm, hx27_2],
                   by simp only [arm64_norm, hx28_2], by simp only [arm64_norm, hvregs_2]⟩ hinvm4)

/-! ## 4. Top-Level Canonical-Domain (`tlb_PolyDecoderDom`) Entry Theorem -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 600000 in
set_option linter.unusedSimpArgs false in
theorem e2p_polyDecoderMerge_dom_sepWPp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {maxOps : Nat}
    (hOps : 35 ≤ maxOps)
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim)))
    {x : PolyDecoderMergeGhost} {st0 : M.σ} {R : SepProp} {s0 : State}
    {ptr0 : BitVec 64} {pb : PolynomialDecoder} {rest_fin : List (BitVec 8)}
    (hDom : tlb_PolyDecoderDom x)
    (hwt_ld : x.wt = .lengthDelimited)
    (hmsg0 : x.msg = default)
    (hpb : tlb_ValidPolyDecoderPB pb)
    (hsome_top : (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      some (pb, rest_fin))
    (hpc : s0.pc = (blkPl_296).base) (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (h_1 : (s0.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat)
    (h_2 : s0.readReg64 .x1 = x.msgPtr) (h_3 : s0.readReg64 .x2 = x.bufRef)
    (h_bound : x.msg.pts.length + x.bs.length < 2 ^ 56)
    (hFit0 : FitsEnv M lim st0 (SpqrTightEvs maxOps 342615 2560))
    (hinv0 : LibsignalCodeRoLoaded lsmpl s0.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s0
      (protoPolynomialDecoderPinnedAt A.repAlloc ⟨⟨0#64, ptr0⟩⟩ x.msgPtr (polyDecoderToProto x.msg) ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
        A.pool lim st0 s0 ∗ stackAt s0.sp polyMergeStack)
      (WppPost (polyDecoderMergeSpecOfEnv A lim
        (tlb_PolyDecoderGuardedEnvOf maxOps) (tlb_PolyDecoderGuardedEnvOf maxOps)) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpecOfEnv A lim
        (tlb_PolyDecoderGuardedEnvOf maxOps) (tlb_PolyDecoderGuardedEnvOf maxOps)) (x, st0) R s0) := by
  have hbs_lt : x.bs.length < 2 ^ 63 := by omega
  have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
  have hbeq := wt_beq_two_of_lengthDelimited h_1'
  have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
    simp only [bne, hbeq, Bool.not_true]
  have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
    rw [truncate32_zeroExtend64_and_255_eq, h_1']; decide
  have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
    revert h_1'; bv_bits
  obtain ⟨⟨len, rest0⟩, hdv0⟩ : ∃ p, decodeVarint x.bs = some p := by
    cases hd' : decodeVarint x.bs with
    | none =>
      have hnone : (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialDecoder_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hd']
      rw [hnone] at hsome_top; cases hsome_top
    | some p => exact ⟨p, rfl⟩
  have hlt_len : ¬ rest0.length < len.toNat := by
    intro hlt
    have hnone : (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialDecoder_mergeField]
      simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0, hlt]
    rw [hnone] at hsome_top; cases hsome_top
  have hfits_dv0 : FitsEnv M lim st0 (DecodeVarint2Env x.bs) :=
    e2p_fitsEnv_decodeVarint2_of_some hdv0 hFit0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv0
  conv => arg 4; rw [stackAt_polyMerge_prologue s0.sp, polyBelow_decodeVarint2 s0.sp]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2
  apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v8
  apply SepWP.exists_elim; intro v9
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  apply SepWP.fold (polySavedRegs_entails_any s0.sp s0 v3) (by unfold polySavedRegs; sep_focus)
  wp_reach; intro hinv0'
  refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, x.ptr, x.bs⟩, st0))
    (ret_pc := (blkPl_296).base + 56#64) hVarintCall hinv0'
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, h_3], hbs_lt, hfits_dv0⟩
    (by rw [decodeVarint2Stack_eq]; sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, h_2, h_3]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
  have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
  have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt hbs_lt)
  have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
  have hule := ule_len_of_ge hlt_len hrest0_lt
  have hsub := bv_len_sub_limit hlt_len
  have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
    have hsuf := hrest0_suf; unfold IsDropSuffix at hsuf; conv => rhs; rw [hsuf, List.drop_drop]
    exact congrArg (List.drop · x.bs) (by omega)
  have hres0 :
      (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        (mergeLoopBin PolynomialDecoder.mergeField
          (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97).map
            (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
    rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialDecoder_mergeField]
    simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte, proto_decodeVarint_toOption, hdv0, hlt_len, hdrop_eq]
    rcases mergeLoopBin PolynomialDecoder.mergeField
      (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97 with _ | m' <;> rfl
  apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 164#64) hinvm
  conv => arg 4; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
  conv => arg 4; rw [decodeVarint2_pool_of_some A lim hdv0, decodeVarint2Stack_eq]
  conv => arg 4; simp only [hdv0, sepConj_assoc]
  wp_focus_pure; rintro ⟨hsm0, hsm1⟩
  wp_focus_pure; intro htrm
  conv => arg 4; simp only [sepConj_assoc, arm64_norm]
  apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
  conv => arg 4; simp only [sepConj_assoc]
  wp_steps_sync_pool ((blkPl_296).base + 164#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinvm'
  have hpts0 : x.msg.pts.length = 0 := by rw [hmsg0]; rfl
  have hevs_init : SpqrTightEvs (e2p_doneOps (0#64).toNat x.msg.pts.length)
      (e2p_doneOps (0#64).toNat x.msg.pts.length * 9789) 2560 [] :=
    SpqrTightEvs.nil _ _ _
  refine SepWPp.weaken_pre
    (Entails.of_eq (by
      rw [e2p_polyDecoderPinnedLoopPre, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
      sep_ac_rfl))
    (e2p_loop_dom_cro hOps hVarintCall hSkipCall hBytesCall hGrowCall
      hDom hpb hsome_top hFit0 hsp_align rest0.length 0#64 ptr0 x.msg rest0 st0 [] _
      (Nat.le_refl _) hrest0_le (by omega) hrest0_suf (Or.inl rfl) hevs_init rfl hres0
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderTightPlacedBudgetAux
