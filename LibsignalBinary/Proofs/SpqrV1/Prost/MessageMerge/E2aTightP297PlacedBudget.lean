/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderClPlacedBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbLeaf
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Loop
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderBudget
import ProofLib.Hoare.SubroutineOk
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Guarded-Tight Placed Budget Proof for `PolynomialEncoder::merge` (Block `297`)

Proves `tlb_PolyEncoderMergePlacedTightOkOf` on Block `297` within
`SpqrTightEvs maxOps 342615 2560` (`35 ≤ maxOps`: at most `3` `Vec<Vec<u8>>` `grow_one` operations
up to `384` B plus `16 × 2` `bytes::merge` allocations up to `2,560` B) under zero-initial-capacity
`pts.cap = 0#64` and `polys.cap = 0#64` on canonical `tlb_PolyEncoderDom` inputs.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightP297PlacedBudget

open Arm64 ProofLib SepProp
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalSessionLib lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_encodeVarint decodeVarint_length mergeBytes
   mergeBytes_encode)
open CryptoVerification.LibsignalSpqrV1
  (Bytes PolynomialEncoder ProtoPolynomialEncoder growOneVecU8Name newCapVecU8)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeBytesUncond encodeKey encodeRepeatedBytes encodeUint32Field encodeVarint encodeVarintAux
   mergeMessage)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded decodeErrorAtStackLen reserveCap withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix bv32_zeroExtend_ofNat decodeVarint_suffix key_shr32_of_lt key_wt_some
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt suffix_trans
   tag_cbz_false ule_len_of_ge w1_tag_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.RustHeap
  (RustAlloc arrayAt vecAt vecBuf vecHeader vecOf vecU8 vecU8At)
open CryptoVerification.SpqrV1.Poly
  (ProtoPolynomialEncoderGhost protoPolynomialEncoderAt protoPolynomialEncoderIdxOff
   protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize protoPolynomialEncoderPinnedAt
   protoPolynomialEncoderPolysOff vecHeaderBytes vecVecU8At vecVecU8PinnedAt)
open CryptoVerification.SpqrV1.Prost.MessageEncode (protoPolynomialEncoderAt_eq_exists_pinned)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (PolyCalleeSaved PolyEncoderMergeGhost SepWPp.call_frame_lscro SepWPp.elim_lscroProp
   SepWPp.of_sepWP_lscro WppPost arrayAt_append_singleton blkPC_297 blkPl_297 bv64_add24_add8
   bv64_add24_add16 bv64_add_zero bv64_ofNat_add_one bv_len_sub_limit cells160_entails_memRegion32
   cmp_len_limit_of_eq cmp_len_limit_of_gt codecWireTypeToProto extractLsb'_append64_0
   extractLsb'_append64_64 grow_post_entails_ready len_eq_cap_bne_false len_lt_cap_bne_true
   madd_24_eq madd_24_eq' memRegion_32_cells160 memRegion_split_24_cells mergeBytes_length
   mergeBytes_suffix polyBelowStack polyBelow_bytesMerge3 polyBelow_bytesMerge3_entails
   polyBelow_decodeVarint2 polyBelow_decodeVarint2_entails polyBelow_extHook
   polyBelow_extHook_entails polyEncoderToProto polyMergeStack polySavedRegs polySavedRegsAny
   polySavedRegs_entails_any stackAt_polyMerge_epilogue stackAt_polyMerge_prologue
   subroutine_ok_withLsCodeRoLoaded_of_withLscroProp vecBuf_vecU8_entails_grow_pre
   vecU8ArrayBytes vecU8At_eq_header_sep_buf vecU8At_stack_to_cells vecU8At_zero_eq_cells
   vecU8Buf withLscroProp wt_beq_two_of_lengthDelimited)
open CryptoVerification.SpqrV1Sync.Codec (loopsTo_polyEncoder mergeMessage_encode)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget fitsEvents_append
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (GrowOneVecU8Env RawVecGrowEnv growOneVecU8BudgetSpec rawVecGrowBudgetSpec rawVecNewCap)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs spqrAllocTightCost)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_GuardedEnv tlb_PolyEncoderDom tlb_PolyEncoderGuardedEnvOf
   tlb_PolyEncoderMergePlacedTightOk tlb_PolyEncoderMergePlacedTightOkOf tlb_PolyEncoderTightEnvOf
   tlb_ValidPolyEncoderPB tlb_domHeap tlb_domHeap_of_dom tlb_domHeap_of_not_dom
   tlb_fitsEnv_fallback_of_not_dom tlb_lenPrefixed tlb_polyEncoderMergeTightSpecOfEnv
   tlb_polyEncoderZeroCapAt tlb_polyEncoderZeroCapAt_entails_unpinned
   tlb_polyEncoderZeroCapAt_of_ptrs)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (BytesMerge3EnvCore decodeErrorPushMergeBudgetSpec mergeBytes_len_bound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env PolyEncoderMergeEnv PolyEncoderMergePostEnv WppBudgetPanic
   bytesMerge3RawBudgetSpec polyEncoderMergePostEnv_imp_pre polyEncoderMergeSpec
   polyEncoderMergeSpecOfEnv wppBudgetPanic_false)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderBudgetAux
  (decodeVarint2Stack_eq decodeVarint2_pool_of_some sepWPp_focus_pure sepWPp_fold)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderClPlacedBudget
  (polyEncoderMerge_cro_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (DecodeVarint2Env decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv decodeVarintSliceEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)

/-! ## 1. Parametric Per-Field Domain & Zero-Initial-Capacity Guarded Contract (`e2p297_`) -/

/-- Derived minimum tight constants for Block `297` under `(maxSlices = 16, maxSliceBytes = 2560)`:
`35` non-free ops (`3` `Vec<Vec<u8>>` grows + `16 × 2` `bytes::merge` ops), `334,823` B exact tight
cost (`21,575 + 16 × 19,578 ≤ 342,615`), and `2,560` B max single request. -/
abbrev e2p297_derivedMaxOps : Nat := 35
abbrev e2p297_derivedCumCap : Nat := 334823
abbrev e2p297_derivedMaxReq : Nat := 2560

/-- Per-field length-bounded `PolynomialEncoder` predicate parameterized by `(maxSlices, maxSliceBytes)`
(definitionally `tlb_ValidPolyEncoderPB` at `(16, 2560)`). -/
def e2p297_ValidPolyEncoderPBOf (maxSlices maxSliceBytes : Nat) (m : PolynomialEncoder) : Prop :=
  (m.pts = [] ∨ m.polys = []) ∧
  m.pts.length + m.polys.length ≤ maxSlices ∧
  (∀ s ∈ m.pts, s.length ≤ maxSliceBytes) ∧
  (∀ s ∈ m.polys, s.length ≤ maxSliceBytes)

/-- Canonical wire-domain guard parameterized by `(maxSlices, maxSliceBytes)`. At `(16, 2560)` this
is definitionally equal to `tlb_PolyEncoderDom`. -/
def e2p297_PolyEncoderDomOf (maxSlices maxSliceBytes : Nat) (x : PolyEncoderMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, e2p297_ValidPolyEncoderPBOf maxSlices maxSliceBytes pb ∧
      x.bs = tlb_lenPrefixed (PolynomialEncoder.encodeRaw pb) rest

/-- Guarded tight allocation envelope for Block `297` parameterized by `(maxOps, cumCap, maxReq)`.
At `(maxOps, 342615, 2560)` this is definitionally equal to `tlb_PolyEncoderGuardedEnvOf maxOps`. -/
def e2p297_PolyEncoderGuardedEnvOf (maxOps cumCap maxReq : Nat) :
    PolyEncoderMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_PolyEncoderDom (SpqrTightEvs maxOps cumCap maxReq) PolyEncoderMergeEnv

/-- Domain-guarded `PolynomialEncoder` input representation at `a`: requires zero initial capacities
(`g.pts.cap = 0#64 ∧ g.polys.cap = 0#64`) when `Dom x` holds, and reduces to unpinned
`protoPolynomialEncoderAt` on `¬ Dom x`. Every `Chunked*` caller initializing
`Option<ProtoPolynomialEncoder>::None → Some(default)` has literal `0#64` capacities and satisfies
this predicate unconditionally without splitting on `Dom x`. -/
def e2p297_protoPolynomialEncoderDomAt (Dom : PolyEncoderMergeGhost → Prop) (A : RustAlloc)
    (x : PolyEncoderMergeGhost) : SepProp :=
  ∃∗ g : ProtoPolynomialEncoderGhost,
    ⌜Dom x → g.pts.cap = 0#64 ∧ g.polys.cap = 0#64⌝ ∗
      protoPolynomialEncoderPinnedAt A g x.msgPtr (polyEncoderToProto x.msg)

/-- Envelope-parameterized budget contract of `PolynomialEncoder::merge` (Block `297`) with
zero-initial-capacity guard on `Dom` in `pre` and standard unpinned `post` matching
`polyEncoderMergeSpecOfEnv`. -/
def e2p297_polyEncoderMergeZeroCapSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (Dom : PolyEncoderMergeGhost → Prop)
    (PreEnv PostEnv : PolyEncoderMergeGhost → List AllocEvent → Prop) :
    Spec (PolyEncoderMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.msg.pts.length + x.bs.length < 2 ^ 56 ∧
      x.msg.polys.length + x.bs.length < 2 ^ 56 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      e2p297_protoPolynomialEncoderDomAt Dom A.repAlloc x ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp polyMergeStack
  post := (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv).post

/-- Sharded `libsignalSessionLib.blockProgram` proposition for Block `297` with zero-initial-cap
guard on `tlb_PolyEncoderDom`, parameterized by `(maxOps, cumCap, maxReq)`. -/
def e2p297_PolyEncoderMergePlacedTightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps cumCap maxReq : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
    (lsmpl.base 297)
    (withLsCodeRoLoaded lsmpl
      (e2p297_polyEncoderMergeZeroCapSpecOfEnv A lim tlb_PolyEncoderDom
        (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)
        (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)))


open CryptoVerification (IsLsBlockProg libsignalSessionLib ls_blockPlacement_base)
open CryptoVerification.LibsignalProtoCodec (skipField skip_length)
open CryptoVerification.LibsignalSpqrV1 (GrowOneCall)
open CryptoVerification.LibsignalTripleRatchet (extract_withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (itag_beq_tag_false sf_truncate32_ofNat64 skip_suffix)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_decodeVarint_toOption)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (mergeBytes_eq_none_of_ne_len mergeLoopBin mergeLoopBin_eq_limit mergeLoopBin_lt_limit
   mergeLoopBin_of_decodeVarint_none mergeLoopBin_of_key_ge mergeLoopBin_of_key_ok
   mergeLoopBin_of_tag_zero mergeLoopBin_of_wt_none mergeMessageBin
   mergeMessageBin_eq_proto_mergeMessage polynomialEncoder_mergeField_other
   polynomialEncoder_mergeField_tag1 polynomialEncoder_mergeField_tag2
   polynomialEncoder_mergeField_tag3 protoPrefixStep_polynomialEncoder_mergeField
   setWidth8_ofNat64_wt)
open LibsignalBinary.Heap (SeqEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (SkipField3Env)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (SkipFieldEnv skipFieldEventsCore)

/-! ## 2. Local State Simp Rules, Doubling-Capacity Invariant, & Tight Callee Lemmas -/

private theorem e2p297_sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl
private theorem e2p297_pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl
private theorem e2p297_status_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).status = s.status := by cases s; rfl
private theorem e2p297_pstate_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).pstate = s.pstate := by cases s; rfl
private theorem e2p297_trace_setMem_pre' (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := by cases s; rfl
private theorem e2p297_readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem e2p297_readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem e2p297_readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem e2p297_calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm]
  bv_sub_add_lit BitVec.toNat_zero growOneVecU8Name bv64_add_zero bv64_ofNat_add_one
  madd_24_eq madd_24_eq' extractLsb'_append64_0 extractLsb'_append64_64
attribute [local arm64_norm ↓, local wp_norm ↓]
  e2p297_sp_setMem_pre e2p297_pc_setMem_pre e2p297_status_setMem_pre e2p297_pstate_setMem_pre
  e2p297_trace_setMem_pre' e2p297_readReg64_setMem_pre e2p297_readReg32_setMem_pre
  e2p297_readReg_setMem_pre e2p297_calleeSavedVRegs_setMem_pre

private def e2p297_ValidVecCap (cap : Nat) : Prop :=
  cap = 0 ∨ cap = 4 ∨ cap = 8 ∨ cap = 16

private def e2p297_growOps (c : Nat) : Nat :=
  if c = 0 then 0 else if c = 4 then 1 else if c = 8 then 2 else 3

private def e2p297_growCost (c : Nat) : Nat :=
  if c = 0 then 0 else if c = 4 then 1997 else if c = 8 then 11786 else 21575

private def e2p297_doneOps (c1 c2 k : Nat) : Nat :=
  e2p297_growOps c1 + e2p297_growOps c2 + 2 * k

private def e2p297_doneCost (c1 c2 k : Nat) : Nat :=
  e2p297_growCost c1 + e2p297_growCost c2 + k * 19578

private def e2p297_remOps (c1 c2 k : Nat) : Nat :=
  (3 - (e2p297_growOps c1 + e2p297_growOps c2)) + 2 * (16 - k)

private def e2p297_remCost (c1 c2 k : Nat) : Nat :=
  (21575 - (e2p297_growCost c1 + e2p297_growCost c2)) + (16 - k) * 19578

private def e2p297_CapPairInv (pb m : PolynomialEncoder) (capPts capPolys : BitVec 64) : Prop :=
  (pb.pts = [] ∧ m.pts = [] ∧ capPts = 0#64 ∧ e2p297_ValidVecCap capPolys.toNat) ∨
    (pb.polys = [] ∧ m.polys = [] ∧ capPolys = 0#64 ∧ e2p297_ValidVecCap capPts.toNat)

private theorem e2p297_done_add_rem {pb m : PolynomialEncoder} {capPts capPolys : BitVec 64}
    {k : Nat} (hinv : e2p297_CapPairInv pb m capPts capPolys) (hk : k ≤ 16) :
    e2p297_doneOps capPts.toNat capPolys.toNat k +
        e2p297_remOps capPts.toNat capPolys.toNat k = 35 ∧
      e2p297_doneCost capPts.toNat capPolys.toNat k +
        e2p297_remCost capPts.toNat capPolys.toNat k = 334823 := by
  have hle : e2p297_growOps capPts.toNat + e2p297_growOps capPolys.toNat ≤ 3 ∧
      e2p297_growCost capPts.toNat + e2p297_growCost capPolys.toNat ≤ 21575 := by
    rcases hinv with ⟨_, _, rfl, hc⟩ | ⟨_, _, rfl, hc⟩ <;>
      rcases hc with h | h | h | h <;>
      simp [e2p297_growOps, e2p297_growCost, h]
  unfold e2p297_doneOps e2p297_remOps e2p297_doneCost e2p297_remCost
  omega

private theorem e2p297_validVecCap_step {cap : Nat} (hv : e2p297_ValidVecCap cap) (hlt : cap < 16) :
    e2p297_ValidVecCap (max (2 * cap) 4) ∧
      max (2 * cap) 4 * 24 ≤ 384 ∧
      e2p297_growOps (max (2 * cap) 4) = e2p297_growOps cap + 1 ∧
      e2p297_growCost (max (2 * cap) 4) =
        e2p297_growCost cap + (if cap = 0 then 1997 else 9789) := by
  rcases hv with rfl | rfl | rfl | rfl
  · refine ⟨Or.inr (Or.inl rfl), by decide, by decide, by decide⟩
  · refine ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, by decide, by decide⟩
  · refine ⟨Or.inr (Or.inr (Or.inr rfl)), by decide, by decide, by decide⟩
  · omega

private theorem e2p297_mergeField_prefix {m m' : PolynomialEncoder} {tag : BitVec 32}
    {wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType} {rest rest' : List (BitVec 8)}
    {depth : Nat}
    (h : PolynomialEncoder.mergeField m tag wt rest depth = .ok (m', rest')) :
    (∃ s1, m'.pts = m.pts ++ s1) ∧ (∃ s2, m'.polys = m.polys ++ s2) := by
  unfold PolynomialEncoder.mergeField at h
  split at h
  · rcases h1 : CryptoVerification.LibsignalSpqrV1.Proto.mergeUint32 wt rest with _ | ⟨v, bs'⟩ <;>
      simp [h1, Bind.bind, Except.bind] at h
    rcases h with ⟨rfl, rfl⟩; exact ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩
  · split at h
    · unfold CryptoVerification.LibsignalSpqrV1.Proto.mergeRepeatedBytes at h
      rcases h1 : CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes wt rest with _ | ⟨v, bs'⟩ <;>
        simp [h1, Bind.bind, Except.bind] at h
      rcases h with ⟨rfl, rfl⟩; exact ⟨⟨[v], rfl⟩, ⟨[], by simp⟩⟩
    · split at h
      · unfold CryptoVerification.LibsignalSpqrV1.Proto.mergeRepeatedBytes at h
        rcases h1 : CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes wt rest with _ | ⟨v, bs'⟩ <;>
          simp [h1, Bind.bind, Except.bind] at h
        rcases h with ⟨rfl, rfl⟩; exact ⟨⟨[], by simp⟩, ⟨[v], rfl⟩⟩
      · rcases h1 : CryptoVerification.LibsignalSpqrV1.Proto.skipField wt tag rest depth with _ | bs' <;>
          simp [h1, Bind.bind, Except.bind] at h
        rcases h with ⟨rfl, rfl⟩; exact ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩

private theorem e2p297_mergeLoopBin_prefix {fuel : Nat} {m m' : PolynomialEncoder}
    {cur : List (BitVec 8)} {limit depth : Nat}
    (h : mergeLoopBin PolynomialEncoder.mergeField fuel m cur limit depth = some m') :
    (∃ s1, m'.pts = m.pts ++ s1) ∧ (∃ s2, m'.polys = m.polys ++ s2) := by
  induction fuel generalizing m cur with
  | zero =>
    unfold mergeLoopBin at h; split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩
      · contradiction
    · contradiction
  | succ fuel ih =>
    unfold mergeLoopBin at h; split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩
      · contradiction
    · rcases hdk : CryptoVerification.LibsignalSpqrV1.Proto.decodeKey cur with _ | ⟨⟨tag, wt⟩, rest⟩
      · simp [hdk, Except.toOption] at h
      · simp only [hdk, Except.toOption] at h
        rcases hmf : PolynomialEncoder.mergeField m tag wt rest depth with _ | ⟨m1, rest'⟩
        · simp [hmf] at h
        · simp only [hmf] at h
          obtain ⟨⟨s1, hs1⟩, ⟨t1, ht1⟩⟩ := e2p297_mergeField_prefix hmf
          obtain ⟨⟨s2, hs2⟩, ⟨t2, ht2⟩⟩ := ih h
          exact ⟨⟨s1 ++ s2, by rw [hs2, hs1, List.append_assoc]⟩,
                 ⟨t1 ++ t2, by rw [ht2, ht1, List.append_assoc]⟩⟩

private theorem e2p297_bytesMerge3_tight {bs v rest' : List (BitVec 8)} {evs : List AllocEvent}
    (hmb : mergeBytes .lengthDelimited bs = some (v, rest'))
    (hv : v.length ≤ 2560)
    (hb : BytesMerge3EnvCore .lengthDelimited 0#64 bs evs) :
    SpqrTightEvs 2 19578 2560 evs := by
  unfold BytesMerge3EnvCore bytesMergeEventsCore at hb
  rw [hmb] at hb
  by_cases hv0 : v.length = 0
  · simp only [hv0, ↓reduceIte] at hb
    subst hb
    exact SpqrTightEvs.nil 2 19578 2560
  · simp only [hv0, ↓reduceIte] at hb
    subst hb
    have hdrc : doReserveClearEvents (0#64).toNat v.length =
        rustAllocEvents (reserveCap 0 0 v.length) 1 := by
      unfold doReserveClearEvents
      change (if v.length ≤ 0 then [] else if 0 = 0 then rustAllocEvents (reserveCap 0 0 v.length) 1 else _) = _
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

private theorem e2p297_growOneVecU8_tight {g : GrowOneCall} {evs : List AllocEvent}
    (hv : e2p297_ValidVecCap g.cap.toNat) (hlt : g.cap.toNat < 16)
    (hg : GrowOneVecU8Env g evs) :
    SpqrTightEvs 1 (if g.cap.toNat = 0 then 1997 else 9789) 2560 evs := by
  unfold GrowOneVecU8Env RawVecGrowEnv at hg
  rcases hg with ⟨hz, rfl⟩ | ⟨hnz, rfl⟩
  · have hz0 : g.cap.toNat = 0 := by rw [hz]; rfl
    rw [hz0]; simp only [↓reduceIte]
    exact (SpqrTightEvs.rustAlloc (R := 96) (by decide) (by decide)).mono
      (Nat.le_refl _) (by decide) (by decide)
  · have hcap_ne0 : g.cap.toNat ≠ 0 := by
      intro h0
      exact hnz (BitVec.eq_of_toNat_eq (by simpa using h0))
    simp only [hcap_ne0, ↓reduceIte]
    rcases hv with h0 | h4 | h8 | h16
    · exact False.elim (hcap_ne0 h0)
    · rw [h4]
      exact (SpqrTightEvs.rustRealloc384 (by decide) (by decide) (by decide)).mono
        (Nat.le_refl _) (Nat.le_refl _) (by decide)
    · rw [h8]
      exact (SpqrTightEvs.rustRealloc384 (by decide) (by decide) (by decide)).mono
        (Nat.le_refl _) (Nat.le_refl _) (by decide)
    · omega

private theorem e2p297_fitsEnv_rem_tight {M : AllocCostModel} {lim : BudgetLimits} {st0 st_cur : M.σ}
    {maxOps cumCap maxReq : Nat} {pb m : PolynomialEncoder} {capPts capPolys : BitVec 64}
    {evs_acc : List AllocEvent}
    (hOps : 35 ≤ maxOps) (hCum : 334823 ≤ cumCap) (hReq : 2560 ≤ maxReq)
    (hinv : e2p297_CapPairInv pb m capPts capPolys)
    (hk : m.pts.length + m.polys.length ≤ 16)
    (hFit0 : FitsEnv M lim st0 (SpqrTightEvs maxOps cumCap maxReq))
    (hevs_acc : SpqrTightEvs
      (e2p297_doneOps capPts.toNat capPolys.toNat (m.pts.length + m.polys.length))
      (e2p297_doneCost capPts.toNat capPolys.toNat (m.pts.length + m.polys.length))
      2560 evs_acc)
    (hst_cur : st_cur = M.stepEvents evs_acc st0) :
    FitsEnv M lim st_cur (SpqrTightEvs
      (e2p297_remOps capPts.toNat capPolys.toNat (m.pts.length + m.polys.length))
      (e2p297_remCost capPts.toNat capPolys.toNat (m.pts.length + m.polys.length))
      2560) := by
  obtain ⟨hops_sum, hcost_sum⟩ := e2p297_done_add_rem hinv hk
  have hseq : FitsEnv M lim st0
      (SeqEnv
        (SpqrTightEvs
          (e2p297_doneOps capPts.toNat capPolys.toNat (m.pts.length + m.polys.length))
          (e2p297_doneCost capPts.toNat capPolys.toNat (m.pts.length + m.polys.length)) 2560)
        (SpqrTightEvs
          (e2p297_remOps capPts.toNat capPolys.toNat (m.pts.length + m.polys.length))
          (e2p297_remCost capPts.toNat capPolys.toNat (m.pts.length + m.polys.length)) 2560)) :=
    FitsEnv.mono (fun _ h => (SpqrTightEvs.seq h).mono (by omega) (by omega) (by omega)) hFit0
  exact hst_cur ▸ hseq.seq_right hevs_acc

private theorem e2p297_fitsEnv_decodeVarint2_of_some {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {bs : List (BitVec 8)} {p : BitVec 64 × List (BitVec 8)} {n c r : Nat}
    (hd : decodeVarint bs = some p) (hFit : FitsEnv M lim st (SpqrTightEvs n c r)) :
    FitsEnv M lim st (DecodeVarint2Env bs) :=
  FitsEnv.mono (fun evs h => by
    have hnil : evs = [] := by
      simpa [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hd] using h
    subst hnil; exact SpqrTightEvs.nil n c r) hFit

private theorem e2p297_fitsEnv_skipField3_of_some {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {iwt : WireType} {tag : Nat} {bufRef slot ptr : BitVec 64}
    {rest rest' : List (BitVec 8)} {n c r : Nat}
    (hsf : skipField (2 * rest.length + 2) 97 tag iwt rest = some rest')
    (hFit : FitsEnv M lim st (SpqrTightEvs n c r)) :
    FitsEnv M lim st (SkipField3Env ⟨iwt, tag, 97, bufRef, slot, ptr, rest⟩) :=
  FitsEnv.mono (fun evs h => by
    have hnil : evs = [] := by
      change SkipFieldEnv _ evs at h
      simpa [SkipFieldEnv, skipFieldEventsCore, hsf] using h
    subst hnil; exact SpqrTightEvs.nil n c r) hFit


/-! ## 3. Pinned `PolynomialEncoder` Unfolding, Push Fold, Loop Bundle, & Round-Trip -/

private theorem e2p297_pinned_unfold_pts (A : RustAlloc)
    (capPts ptrPts capPolys ptrPolys a : BitVec 64) (m : PolynomialEncoder) :
    protoPolynomialEncoderPinnedAt A ⟨⟨capPts, ptrPts⟩, ⟨capPolys, ptrPolys⟩⟩ a
        (polyEncoderToProto m) =
      ((a ↦₆₄ capPts) ∗ ((a + 8#64) ↦₆₄ ptrPts) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 m.pts.length) ∗
        ⌜m.pts.length ≤ capPts.toNat ∧ capPts.toNat * 24 < 2 ^ 63 ∧ ptrPts ≠ 0⌝ ∗
        (if capPts = 0 then emp
         else A.live ptrPts (capPts.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptrPts m.pts ∗
           memRegion (ptrPts + BitVec.ofNat 64 (m.pts.length * 24))
             ((capPts.toNat - m.pts.length) * 24))) ∗
      vecVecU8PinnedAt A ⟨capPolys, ptrPolys⟩ (a + protoPolynomialEncoderPolysOff) m.polys ∗
      ((a + protoPolynomialEncoderIdxOff) ↦₃₂ m.idx) ∗
      memRegion (a + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize := by
  unfold protoPolynomialEncoderPinnedAt polyEncoderToProto
  conv => lhs; arg 1; unfold vecVecU8PinnedAt vecHeaderBytes vecAt vecHeader vecBuf
  simp only [sepConj_assoc]

private theorem e2p297_pinned_unfold_polys (A : RustAlloc)
    (capPts ptrPts capPolys ptrPolys a : BitVec 64) (m : PolynomialEncoder) :
    protoPolynomialEncoderPinnedAt A ⟨⟨capPts, ptrPts⟩, ⟨capPolys, ptrPolys⟩⟩ a
        (polyEncoderToProto m) =
      vecVecU8PinnedAt A ⟨capPts, ptrPts⟩ a m.pts ∗
      (((a + 24#64) ↦₆₄ capPolys) ∗ ((a + 32#64) ↦₆₄ ptrPolys) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 m.polys.length) ∗
        ⌜m.polys.length ≤ capPolys.toNat ∧ capPolys.toNat * 24 < 2 ^ 63 ∧ ptrPolys ≠ 0⌝ ∗
        (if capPolys = 0 then emp
         else A.live ptrPolys (capPolys.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptrPolys m.polys ∗
           memRegion (ptrPolys + BitVec.ofNat 64 (m.polys.length * 24))
             ((capPolys.toNat - m.polys.length) * 24))) ∗
      ((a + protoPolynomialEncoderIdxOff) ↦₃₂ m.idx) ∗
      memRegion (a + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize := by
  unfold protoPolynomialEncoderPinnedAt polyEncoderToProto protoPolynomialEncoderPolysOff
  conv => lhs; arg 2; arg 1; unfold vecVecU8PinnedAt vecHeaderBytes vecAt vecHeader vecBuf
  rw [bv64_add24_add8, bv64_add24_add16]
  simp only [sepConj_assoc]

private theorem e2p297_vecVecU8PinnedAt_after_push (A : RustAlloc)
    (vecAddr cap' ptr' cap_e ptr_e : BitVec 64) (bss : List (List (BitVec 8))) (v : List (BitVec 8))
    (hlt : bss.length < cap'.toNat) (hbound : cap'.toNat * 24 < 2 ^ 63) (hptr : ptr' ≠ 0) :
    (vecAddr ↦₆₄ cap') ∗ ((vecAddr + 8#64) ↦₆₄ ptr') ∗
      ((vecAddr + 16#64) ↦₆₄ BitVec.ofNat 64 (bss.length + 1)) ∗
      A.live ptr' (cap'.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr' bss ∗
      ((ptr' + BitVec.ofNat 64 (bss.length * 24)) ↦₆₄ cap_e) ∗
      ((ptr' + BitVec.ofNat 64 (bss.length * 24) + 8#64) ↦₆₄ ptr_e) ∗
      ((ptr' + BitVec.ofNat 64 (bss.length * 24) + 16#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗
      vecU8Buf A cap_e ptr_e v ∗
      memRegion (ptr' + BitVec.ofNat 64 ((bss.length + 1) * 24))
        ((cap'.toNat - (bss.length + 1)) * 24) ⊢
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
      rw [vecU8At_eq_header_sep_buf]; unfold vecHeader; sep_ac_rfl
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
        memRegion (ptr' + BitVec.ofNat 64 ((bss.length + 1) * 24))
          ((cap'.toNat - (bss.length + 1)) * 24) =
      ((elemAddr ↦₆₄ cap_e) ∗ ((elemAddr + 8#64) ↦₆₄ ptr_e) ∗
        ((elemAddr + 16#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗ vecU8Buf A cap_e ptr_e v) ∗
      ((vecAddr ↦₆₄ cap') ∗ ((vecAddr + 8#64) ↦₆₄ ptr') ∗
        ((vecAddr + 16#64) ↦₆₄ BitVec.ofNat 64 (bss.length + 1)) ∗
        A.live ptr' (cap'.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr' bss ∗
        memRegion (ptr' + BitVec.ofNat 64 ((bss.length + 1) * 24))
          ((cap'.toNat - (bss.length + 1)) * 24)) := by
    sep_ac_rfl
  have hpull2 :
      ((vecAddr ↦₆₄ cap') ∗ ((vecAddr + 8#64) ↦₆₄ ptr') ∗
        ((vecAddr + 16#64) ↦₆₄ BitVec.ofNat 64 (bss.length + 1))) ∗
        (A.live ptr' (cap'.toNat * 24) 8 ∗
          (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr' bss ∗ vecU8 A elemAddr v) ∗
          memRegion (ptr' + BitVec.ofNat 64 ((bss.length + 1) * 24))
            ((cap'.toNat - (bss.length + 1)) * 24)) =
      vecU8 A elemAddr v ∗
        ((vecAddr ↦₆₄ cap') ∗ ((vecAddr + 8#64) ↦₆₄ ptr') ∗
          ((vecAddr + 16#64) ↦₆₄ BitVec.ofNat 64 (bss.length + 1)) ∗
          A.live ptr' (cap'.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr' bss ∗
          memRegion (ptr' + BitVec.ofNat 64 ((bss.length + 1) * 24))
            ((cap'.toNat - (bss.length + 1)) * 24)) := by
    sep_ac_rfl
  rw [hpull1]; refine Entails.trans (sepConj_mono_left helem) (Entails.of_eq hpull2.symm)

private theorem e2p297_vecVecU8PinnedAt_after_push_24 (A : RustAlloc)
    (a cap' ptr' cap_e ptr_e : BitVec 64) (bss : List (List (BitVec 8))) (v : List (BitVec 8))
    (hlt : bss.length < cap'.toNat) (hbound : cap'.toNat * 24 < 2 ^ 63) (hptr : ptr' ≠ 0) :
    ((a + 24#64) ↦₆₄ cap') ∗ ((a + 32#64) ↦₆₄ ptr') ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 (bss.length + 1)) ∗
      A.live ptr' (cap'.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr' bss ∗
      ((ptr' + BitVec.ofNat 64 (bss.length * 24)) ↦₆₄ cap_e) ∗
      ((ptr' + BitVec.ofNat 64 (bss.length * 24) + 8#64) ↦₆₄ ptr_e) ∗
      ((ptr' + BitVec.ofNat 64 (bss.length * 24) + 16#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗
      vecU8Buf A cap_e ptr_e v ∗
      memRegion (ptr' + BitVec.ofNat 64 ((bss.length + 1) * 24))
        ((cap'.toNat - (bss.length + 1)) * 24) ⊢
    vecVecU8PinnedAt A ⟨cap', ptr'⟩ (a + protoPolynomialEncoderPolysOff) (bss ++ [v]) := by
  unfold protoPolynomialEncoderPolysOff
  rw [← bv64_add24_add8, ← bv64_add24_add16]
  exact e2p297_vecVecU8PinnedAt_after_push A (a + 24#64) cap' ptr' cap_e ptr_e bss v
    hlt hbound hptr

private theorem e2p297_pinned_entails_unpinned (A : RustAlloc) (g : ProtoPolynomialEncoderGhost)
    (a : BitVec 64) (pb : ProtoPolynomialEncoder) :
    protoPolynomialEncoderPinnedAt A g a pb ⊢ protoPolynomialEncoderAt A a pb := by
  rw [protoPolynomialEncoderAt_eq_exists_pinned]
  exact Entails.sepExists_right g (Entails.refl _)

private def e2p297_polyEncoderPinnedLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State) (g : ProtoPolynomialEncoderGhost)
    (msgPtr bufRef slot ptr : BitVec 64)
    (m : PolynomialEncoder) (bs cur : List (BitVec 8)) : SepProp :=
  stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗
    memRegion (s0.sp - 128#64) 48 ∗ polySavedRegsAny s0.sp s0 ∗
    protoPolynomialEncoderPinnedAt A.repAlloc g msgPtr (polyEncoderToProto m) ∗
    (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗ A.pool lim st s

private theorem e2p297_encodeVarint_len_le_11 (v : BitVec 64) : (encodeVarint v).length ≤ 11 := by
  unfold encodeVarint
  suffices ∀ k (w : BitVec 64), (encodeVarintAux k w).length ≤ k + 1 from this 10 v
  intro k
  induction k with
  | zero => intro _; simp [encodeVarintAux]
  | succ k ih =>
    intro w
    simp only [encodeVarintAux]
    split
    · simp
    · simp only [List.length_cons]
      have := ih (w >>> 7)
      omega

private theorem e2p297_encodeRepeatedBytes_len_bound (tag : BitVec 32) {xs : List Bytes}
    (hxs : ∀ s ∈ xs, s.length ≤ 2560) :
    (encodeRepeatedBytes tag xs).length ≤ xs.length * 2582 := by
  induction xs with
  | nil => simp [encodeRepeatedBytes]
  | cons x xs ih =>
    have hx : x.length ≤ 2560 := hxs x List.mem_cons_self
    have hih := ih (fun s hs => hxs s (List.mem_cons_of_mem _ hs))
    have hcons : encodeRepeatedBytes tag (x :: xs) =
        encodeBytesUncond tag x ++ encodeRepeatedBytes tag xs := rfl
    rw [hcons, List.length_append, List.length_cons]
    have hk : (encodeKey tag .lengthDelimited).length ≤ 11 := e2p297_encodeVarint_len_le_11 _
    have hl : (encodeVarint (BitVec.ofNat 64 x.length)).length ≤ 11 :=
      e2p297_encodeVarint_len_le_11 _
    simp only [encodeBytesUncond, List.length_append]
    omega

private theorem e2p297_polyEncoder_encodeRaw_len_lt {pb : PolynomialEncoder}
    (hpb : tlb_ValidPolyEncoderPB pb) :
    (PolynomialEncoder.encodeRaw pb).length < 2 ^ 63 := by
  rcases hpb with ⟨_, hsum, hpts, hpolys⟩
  unfold PolynomialEncoder.encodeRaw
  simp only [List.length_append]
  have h1 : (encodeUint32Field 1#32 pb.idx).length ≤ 22 := by
    unfold encodeUint32Field
    split
    · simp
    · simp only [List.length_append]
      have hk : (encodeKey 1#32 .varint).length ≤ 11 := e2p297_encodeVarint_len_le_11 _
      have hv : (encodeVarint (pb.idx.zeroExtend 64)).length ≤ 11 := e2p297_encodeVarint_len_le_11 _
      omega
  have h2 := e2p297_encodeRepeatedBytes_len_bound 2#32 hpts
  have h3 := e2p297_encodeRepeatedBytes_len_bound 3#32 hpolys
  omega

private theorem e2p297_mergeMessage_polyEncoder_of_valid {pb : PolynomialEncoder} (rest : Bytes)
    (hpb : tlb_ValidPolyEncoderPB pb) :
    mergeMessage PolynomialEncoder.mergeField .lengthDelimited default
        (tlb_lenPrefixed (PolynomialEncoder.encodeRaw pb) rest) 98 =
      .ok (pb, rest) := by
  have hlt63 := e2p297_polyEncoder_encodeRaw_len_lt hpb
  have hlt64 : (PolynomialEncoder.encodeRaw pb).length < 2 ^ 64 := by omega
  unfold tlb_lenPrefixed
  rw [List.append_assoc]
  exact mergeMessage_encode PolynomialEncoder.mergeField 0 PolynomialEncoder.encodeRaw default pb
    98 rest (loopsTo_polyEncoder pb hlt64) hlt64 (by decide)


/-! ## 4. Canonical-Domain Tag-2 & Tag-3 Step Lemmas -/

private theorem e2p297_rem_bounds_push {c_act k : Nat}
    (hv : e2p297_ValidVecCap c_act) (hk1 : k + 1 ≤ 16) :
    2 ≤ (3 - e2p297_growOps c_act) + 2 * (16 - k) ∧
      19578 ≤ (21575 - e2p297_growCost c_act) + (16 - k) * 19578 ∧
      (c_act < 16 →
        3 ≤ (3 - e2p297_growOps c_act) + 2 * (16 - k) ∧
          19578 + (if c_act = 0 then 1997 else 9789) ≤
            (21575 - e2p297_growCost c_act) + (16 - k) * 19578) := by
  rcases hv with rfl | rfl | rfl | rfl <;>
    simp only [e2p297_growOps, e2p297_growCost, Nat.reduceEqDiff, ↓reduceIte] <;>
    refine ⟨by omega, by omega, fun hlt => ⟨by omega, by omega⟩⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem e2p297_tag2_copy_step_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyEncoderMergeGhost → List AllocEvent → Prop}
    {x : PolyEncoderMergeGhost} {st0 st_next : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder}
    {v rest' : List (BitVec 8)} {limit : Nat}
    {v_stk0 cap' ptr' capPolys ptrPolys cap_e ptr_e : BitVec 64}
    (_hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlt : m.pts.length < cap'.toNat) (hbound : cap'.toNat * 24 < 2 ^ 63) (hptr : ptr' ≠ 0)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (e2p297_polyEncoderPinnedLoopPre A lim st_next s0 s' ⟨⟨cap', ptr'⟩, ⟨capPolys, ptrPolys⟩⟩
          x.msgPtr x.bufRef x.slot x.ptr { m with pts := m.pts ++ [v] } x.bs rest')
        (WppPost (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_297).base + 392#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 m.pts.length)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 160#64) ↦₆₄ v_stk0) ∗ vecU8At A.repAlloc (s0.sp - 152#64) cap_e ptr_e v ∗
        (x.msgPtr ↦₆₄ cap') ∗ ((x.msgPtr + 8#64) ↦₆₄ ptr') ∗
        ((x.msgPtr + 16#64) ↦₆₄ BitVec.ofNat 64 m.pts.length) ∗
        A.repAlloc.live ptr' (cap'.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptr' m.pts ∗
        memRegion (ptr' + BitVec.ofNat 64 (m.pts.length * 24)) ((cap'.toNat - m.pts.length) * 24) ∗
        vecVecU8PinnedAt A.repAlloc ⟨capPolys, ptrPolys⟩
          (x.msgPtr + protoPolynomialEncoderPolysOff) m.polys ∗
        ((x.msgPtr + protoPolynomialEncoderIdxOff) ↦₃₂ m.idx) ∗
        memRegion (x.msgPtr + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize ∗
        stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
        polySavedRegsAny s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest' ∗ A.pool lim st_next s)
      (WppPost (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 164#64) hinv
  conv => arg 4; rw [vecU8At_stack_to_cells A.repAlloc s0.sp cap_e ptr_e v,
    memRegion_split_24_cells ptr' m.pts.length cap'.toNat hlt hbound]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w0
  wp_steps_sync_pool ((blkPl_297).base + 164#64)
  simp only [State.setMem_setMem]
  apply SepWP.fold (cells160_entails_memRegion32 s0.sp v_stk0 cap_e ptr_e
    (BitVec.ofNat 64 v.length)) (by sep_focus)
  apply SepWP.fold (e2p297_vecVecU8PinnedAt_after_push A.repAlloc x.msgPtr cap' ptr' cap_e ptr_e
    m.pts v hlt hbound hptr) (by sep_focus)
  wp_reach; intro hinvm
  refine SepWPp.weaken_pre
    (Entails.of_eq (by
      dsimp only [e2p297_polyEncoderPinnedLoopPre, protoPolynomialEncoderPinnedAt, polyEncoderToProto]
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
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem e2p297_tag2_step_dom_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyEncoderMergeGhost → List AllocEvent → Prop}
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {pb m : PolynomialEncoder}
    {rest v rest' : List (BitVec 8)} {limit : Nat}
    {capPts ptrPts capPolys ptrPolys : BitVec 64} {evs_acc : List AllocEvent}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hpts_bound : m.pts.length + rest.length < 2 ^ 56)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hmb : mergeBytes .lengthDelimited rest = some (v, rest'))
    (hv_le : v.length ≤ 2560)
    (hk1 : (m.pts.length + m.polys.length) + 1 ≤ 16)
    (hpolys0 : pb.polys = [] ∧ m.polys = [] ∧ capPolys = 0#64)
    (hv_cap : e2p297_ValidVecCap capPts.toNat)
    (hevs_acc : SpqrTightEvs
      (e2p297_doneOps capPts.toNat capPolys.toNat (m.pts.length + m.polys.length))
      (e2p297_doneCost capPts.toNat capPolys.toNat (m.pts.length + m.polys.length))
      2560 evs_acc)
    (hst_cur : st_cur = M.stepEvents evs_acc st0)
    (hfits_rem : FitsEnv M lim st_cur (SpqrTightEvs
      (e2p297_remOps capPts.toNat capPolys.toNat (m.pts.length + m.polys.length))
      (e2p297_remCost capPts.toNat capPolys.toNat (m.pts.length + m.polys.length))
      2560))
    (hcont : ∀ (cap' ptr' : BitVec 64) (st_next : M.σ) (evs_step : List AllocEvent) (s' : State),
      e2p297_CapPairInv pb { m with pts := m.pts ++ [v] } cap' capPolys →
      SpqrTightEvs
        (e2p297_doneOps cap'.toNat capPolys.toNat ((m.pts.length + 1) + m.polys.length))
        (e2p297_doneCost cap'.toNat capPolys.toNat ((m.pts.length + 1) + m.polys.length))
        2560 (evs_acc ++ evs_step) →
      st_next = M.stepEvents (evs_acc ++ evs_step) st0 →
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (e2p297_polyEncoderPinnedLoopPre A lim st_next s0 s' ⟨⟨cap', ptr'⟩, ⟨capPolys, ptrPolys⟩⟩
          x.msgPtr x.bufRef x.slot x.ptr { m with pts := m.pts ++ [v] } x.bs rest')
        (WppPost (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_297).base + 336#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 2#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (e2p297_polyEncoderPinnedLoopPre A lim st_cur s0 s ⟨⟨capPts, ptrPts⟩, ⟨capPolys, ptrPolys⟩⟩
        x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hpb_p0, hm_p0, hcapPolys0⟩ := hpolys0
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  obtain ⟨hrem_ops2, hrem_cost2, hrem_grow⟩ := e2p297_rem_bounds_push hv_cap hk1
  have hrem_ops_ge2 : 2 ≤ e2p297_remOps capPts.toNat capPolys.toNat (m.pts.length + m.polys.length) := by
    subst hcapPolys0; simpa [e2p297_remOps, e2p297_growOps] using hrem_ops2
  have hrem_cost_ge2 :
      19578 ≤ e2p297_remCost capPts.toNat capPolys.toNat (m.pts.length + m.polys.length) := by
    subst hcapPolys0; simpa [e2p297_remCost, e2p297_growCost] using hrem_cost2
  have hfits_mb : FitsEnv M lim st_cur
      (BytesMerge3Env ⟨.lengthDelimited, s0.sp - 152#64, 0#64, 1#64, [], x.bufRef, x.slot, restPtr, rest⟩) :=
    FitsEnv.mono (fun _ hb => (e2p297_bytesMerge3_tight hmb hv_le hb).mono hrem_ops_ge2
      hrem_cost_ge2 (Nat.le_refl _)) hfits_rem
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
  conv => arg 4; rw [e2p297_polyEncoderPinnedLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
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
    (ret_pc := (blkPl_297).base + 364#64) hBytesCall hinv
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
  conv => arg 4; rw [e2p297_pinned_unfold_pts]
  conv => arg 4; simp only [sepConj_assoc]
  apply sepWPp_focus_pure (by sep_focus); intro htrm
  apply sepWPp_focus_pure (by sep_focus); intro hevs_mb
  apply sepWPp_focus_pure (by sep_focus); intro hsm0
  apply sepWPp_focus_pure (by sep_focus); intro _hcap_ok
  apply sepWPp_focus_pure (by sep_focus); rintro ⟨hlen_le, hcap_bound, hptr_ne⟩
  conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp]
  have hmb_tight : SpqrTightEvs 2 19578 2560 evs_mb :=
    e2p297_bytesMerge3_tight hmb hv_le hevs_mb
  by_cases hcap_eq : m.pts.length = capPts.toNat
  · have hcap_lt16 : capPts.toNat < 16 := by omega
    obtain ⟨hv_new, _, hops_new, hcost_new⟩ := e2p297_validVecCap_step hv_cap hcap_lt16
    obtain ⟨hrem3, hrem_cost3⟩ := hrem_grow hcap_lt16
    have hseq_mb : FitsEnv M lim st_cur
        (SeqEnv (SpqrTightEvs 2 19578 2560)
          (SpqrTightEvs 1 (if capPts.toNat = 0 then 1997 else 9789) 2560)) :=
      FitsEnv.mono (fun _ h => (SpqrTightEvs.seq h).mono
        (by subst hcapPolys0; simpa [e2p297_remOps, e2p297_growOps] using hrem3)
        (by subst hcapPolys0; simpa [e2p297_remCost, e2p297_growCost] using hrem_cost3)
        (by decide)) hfits_rem
    have hfits_mb_tail : FitsEnv M lim (M.stepEvents evs_mb st_cur)
        (SpqrTightEvs 1 (if capPts.toNat = 0 then 1997 else 9789) 2560) :=
      hseq_mb.seq_right hmb_tight
    have hbne : (BitVec.ofNat 64 m.pts.length != capPts) = false := len_eq_cap_bne_false hcap_eq
    have hgrow_bound : max (2 * capPts.toNat) 4 * 24 + 8 ≤ 2 ^ 63 := by omega
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 621) hinvm
    apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecBuf_vecU8_entails_grow_pre A.repAlloc capPts ptrPts m.pts hcap_eq)
      (by sep_focus)
    conv => arg 4; rw [polyBelow_extHook s0.sp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro pins
    wp_focus_pure; rintro ⟨hpins_len, hbytes_len⟩
    wp_steps_sync_pool (lsmpl.base 621)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    have hfits_grow : FitsEnv M lim (M.stepEvents evs_mb st_cur)
        (GrowOneVecU8Env ⟨x.msgPtr, capPts, ptrPts, vecU8ArrayBytes pins m.pts⟩) :=
      FitsEnv.mono (fun _ hg => e2p297_growOneVecU8_tight hv_cap hcap_lt16 hg) hfits_mb_tail
    refine SepWPp.call_frame_lscro (spec := growOneVecU8BudgetSpec M A lim)
      (x := (⟨x.msgPtr, capPts, ptrPts, vecU8ArrayBytes pins m.pts⟩, M.stepEvents evs_mb st_cur))
      (ret_pc := (blkPl_297).base + 392#64) hGrowCall hinvm'
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
    have hnew_toNat : (newCapVecU8 capPts).toNat = max (2 * capPts.toNat) 4 := by
      unfold newCapVecU8; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt_new : m.pts.length < (newCapVecU8 capPts).toNat := by rw [hnew_toNat]; omega
    have hbound_new : (newCapVecU8 capPts).toNat * 24 < 2 ^ 63 := by rw [hnew_toNat]; omega
    have hg_tight : SpqrTightEvs 1 (if capPts.toNat = 0 then 1997 else 9789) 2560 evs_g :=
      e2p297_growOneVecU8_tight hv_cap hcap_lt16 hevs_g
    have hevs_next : SpqrTightEvs
        (e2p297_doneOps (newCapVecU8 capPts).toNat capPolys.toNat ((m.pts.length + 1) + m.polys.length))
        (e2p297_doneCost (newCapVecU8 capPts).toNat capPolys.toNat ((m.pts.length + 1) + m.polys.length))
        2560 (evs_acc ++ (evs_mb ++ evs_g)) := by
      refine (hevs_acc.append (hmb_tight.append hg_tight)).mono ?_ ?_ (by decide)
      · unfold e2p297_doneOps; rw [hnew_toNat, hops_new]; omega
      · unfold e2p297_doneCost; rw [hnew_toNat, hcost_new, Nat.add_right_comm m.pts.length 1 m.polys.length,
          Nat.add_mul]; omega
    have hst_next : M.stepEvents evs_g (M.stepEvents evs_mb st_cur) =
        M.stepEvents (evs_mb ++ evs_g) st_cur :=
      (AllocCostModel.stepEvents_append M evs_mb evs_g st_cur).symm
    have hst_tot : M.stepEvents (evs_mb ++ evs_g) st_cur =
        M.stepEvents (evs_acc ++ (evs_mb ++ evs_g)) st0 := by
      rw [hst_cur, ← AllocCostModel.stepEvents_append]
    conv => arg 4; dsimp only [rawVecNewCap]
    conv => arg 4; rw [show A.live p' (max (2 * capPts.toNat) 4 * 24) 8 =
      A.repAlloc.live p' (max (2 * capPts.toNat) 4 * 24) 8 from rfl,
      show BitVec.ofNat 64 (max (2 * capPts.toNat) 4) = newCapVecU8 capPts from rfl, hst_next]
    apply sepWPp_fold
      (grow_post_entails_ready A.repAlloc capPts p' pins m.pts hcap_eq hpins_len hgrow_bound)
      (by sep_focus)
    apply sepWPp_fold (polyBelow_extHook_entails s0.sp) (by sep_focus)
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (e2p297_tag2_copy_step_cro (st_next := M.stepEvents (evs_mb ++ evs_g) st_cur)
        (v_stk0 := v_stk0) (cap' := newCapVecU8 capPts) (ptr' := p')
        (capPolys := capPolys) (ptrPolys := ptrPolys)
        (cap_e := cap_e) (ptr_e := ptr_e) hsp_align hlt_new hbound_new hp'_ne
        (fun s' => hcont (newCapVecU8 capPts) p' _ (evs_mb ++ evs_g) s'
          (Or.inr ⟨hpb_p0, hm_p0, hcapPolys0, hnew_toNat ▸ hv_new⟩) hevs_next hst_tot)
        hpcm2 hrunm2 hspm2 (htrm2.trans (htrm.trans htr))
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2
        (hx25_2.trans (by rw [hcap_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]))
        ⟨hx26_2, hx27_2, hx28_2, hvregs_2⟩ hinvm2)
  · have hlt : m.pts.length < capPts.toNat := Nat.lt_of_le_of_ne hlen_le hcap_eq
    have hbne : (BitVec.ofNat 64 m.pts.length != capPts) = true := len_lt_cap_bne_true hlt
    have hcap_ne0 : capPts ≠ 0 := by intro h0; subst h0; change m.pts.length < 0 at hlt; omega
    have hevs_next : SpqrTightEvs
        (e2p297_doneOps capPts.toNat capPolys.toNat ((m.pts.length + 1) + m.polys.length))
        (e2p297_doneCost capPts.toNat capPolys.toNat ((m.pts.length + 1) + m.polys.length))
        2560 (evs_acc ++ evs_mb) := by
      refine (hevs_acc.append hmb_tight).mono ?_ ?_ (by decide)
      · unfold e2p297_doneOps; omega
      · unfold e2p297_doneCost; rw [Nat.add_right_comm m.pts.length 1 m.polys.length, Nat.add_mul]; omega
    have hst_tot : M.stepEvents evs_mb st_cur = M.stepEvents (evs_acc ++ evs_mb) st0 := by
      rw [hst_cur, ← AllocCostModel.stepEvents_append]
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 392#64) hinvm
    (conv => arg 4; simp only [hcap_ne0, ↓reduceIte, sepConj_assoc])
    apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps_sync_pool ((blkPl_297).base + 392#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre
      (Entails.of_eq (by
        rw [show A.live ptrPts (capPts.toNat * 24) 8 = A.repAlloc.live ptrPts (capPts.toNat * 24) 8 from rfl]
        sep_ac_rfl))
      (e2p297_tag2_copy_step_cro (st_next := M.stepEvents evs_mb st_cur)
        (v_stk0 := v_stk0) (cap' := capPts) (ptr' := ptrPts)
        (capPolys := capPolys) (ptrPolys := ptrPolys)
        (cap_e := cap_e) (ptr_e := ptr_e) hsp_align hlt hcap_bound hptr_ne
        (fun s' => hcont capPts ptrPts _ evs_mb s'
          (Or.inr ⟨hpb_p0, hm_p0, hcapPolys0, hv_cap⟩) hevs_next hst_tot)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
        (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
         by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')


set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem e2p297_tag3_copy_step_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyEncoderMergeGhost → List AllocEvent → Prop}
    {x : PolyEncoderMergeGhost} {st0 st_next : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder}
    {v rest' : List (BitVec 8)} {limit : Nat}
    {v_stk0 capPts ptrPts cap' ptr' cap_e ptr_e : BitVec 64}
    (_hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlt : m.polys.length < cap'.toNat) (hbound : cap'.toNat * 24 < 2 ^ 63) (hptr : ptr' ≠ 0)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (e2p297_polyEncoderPinnedLoopPre A lim st_next s0 s' ⟨⟨capPts, ptrPts⟩, ⟨cap', ptr'⟩⟩
          x.msgPtr x.bufRef x.slot x.ptr { m with polys := m.polys ++ [v] } x.bs rest')
        (WppPost (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_297).base + 296#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 m.polys.length)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 160#64) ↦₆₄ v_stk0) ∗ vecU8At A.repAlloc (s0.sp - 152#64) cap_e ptr_e v ∗
        vecVecU8PinnedAt A.repAlloc ⟨capPts, ptrPts⟩ x.msgPtr m.pts ∗
        ((x.msgPtr + 24#64) ↦₆₄ cap') ∗ ((x.msgPtr + 32#64) ↦₆₄ ptr') ∗
        ((x.msgPtr + 40#64) ↦₆₄ BitVec.ofNat 64 m.polys.length) ∗
        A.repAlloc.live ptr' (cap'.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptr' m.polys ∗
        memRegion (ptr' + BitVec.ofNat 64 (m.polys.length * 24)) ((cap'.toNat - m.polys.length) * 24) ∗
        ((x.msgPtr + protoPolynomialEncoderIdxOff) ↦₃₂ m.idx) ∗
        memRegion (x.msgPtr + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize ∗
        stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
        polySavedRegsAny s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest' ∗ A.pool lim st_next s)
      (WppPost (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 164#64) hinv
  conv => arg 4; rw [vecU8At_stack_to_cells A.repAlloc s0.sp cap_e ptr_e v,
    memRegion_split_24_cells ptr' m.polys.length cap'.toNat hlt hbound]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w0
  wp_steps_sync_pool ((blkPl_297).base + 164#64)
  simp only [State.setMem_setMem]
  apply SepWP.fold (cells160_entails_memRegion32 s0.sp v_stk0 cap_e ptr_e
    (BitVec.ofNat 64 v.length)) (by sep_focus)
  apply SepWP.fold (e2p297_vecVecU8PinnedAt_after_push_24 A.repAlloc x.msgPtr cap' ptr' cap_e ptr_e
    m.polys v hlt hbound hptr) (by sep_focus)
  wp_reach; intro hinvm
  refine SepWPp.weaken_pre
    (Entails.of_eq (by
      dsimp only [e2p297_polyEncoderPinnedLoopPre, protoPolynomialEncoderPinnedAt, polyEncoderToProto]
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
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem e2p297_tag3_step_dom_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyEncoderMergeGhost → List AllocEvent → Prop}
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {pb m : PolynomialEncoder}
    {rest v rest' : List (BitVec 8)} {limit : Nat}
    {capPts ptrPts capPolys ptrPolys : BitVec 64} {evs_acc : List AllocEvent}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hpolys_bound : m.polys.length + rest.length < 2 ^ 56)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hmb : mergeBytes .lengthDelimited rest = some (v, rest'))
    (hv_le : v.length ≤ 2560)
    (hk1 : (m.pts.length + m.polys.length) + 1 ≤ 16)
    (hpts0 : pb.pts = [] ∧ m.pts = [] ∧ capPts = 0#64)
    (hv_cap : e2p297_ValidVecCap capPolys.toNat)
    (hevs_acc : SpqrTightEvs
      (e2p297_doneOps capPts.toNat capPolys.toNat (m.pts.length + m.polys.length))
      (e2p297_doneCost capPts.toNat capPolys.toNat (m.pts.length + m.polys.length))
      2560 evs_acc)
    (hst_cur : st_cur = M.stepEvents evs_acc st0)
    (hfits_rem : FitsEnv M lim st_cur (SpqrTightEvs
      (e2p297_remOps capPts.toNat capPolys.toNat (m.pts.length + m.polys.length))
      (e2p297_remCost capPts.toNat capPolys.toNat (m.pts.length + m.polys.length))
      2560))
    (hcont : ∀ (cap' ptr' : BitVec 64) (st_next : M.σ) (evs_step : List AllocEvent) (s' : State),
      e2p297_CapPairInv pb { m with polys := m.polys ++ [v] } capPts cap' →
      SpqrTightEvs
        (e2p297_doneOps capPts.toNat cap'.toNat (m.pts.length + (m.polys.length + 1)))
        (e2p297_doneCost capPts.toNat cap'.toNat (m.pts.length + (m.polys.length + 1)))
        2560 (evs_acc ++ evs_step) →
      st_next = M.stepEvents (evs_acc ++ evs_step) st0 →
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (e2p297_polyEncoderPinnedLoopPre A lim st_next s0 s' ⟨⟨capPts, ptrPts⟩, ⟨cap', ptr'⟩⟩
          x.msgPtr x.bufRef x.slot x.ptr { m with polys := m.polys ++ [v] } x.bs rest')
        (WppPost (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_297).base + 240#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 2#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (e2p297_polyEncoderPinnedLoopPre A lim st_cur s0 s ⟨⟨capPts, ptrPts⟩, ⟨capPolys, ptrPolys⟩⟩
        x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hpb_p0, hm_p0, hcapPts0⟩ := hpts0
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  obtain ⟨hrem_ops2, hrem_cost2, hrem_grow⟩ := e2p297_rem_bounds_push hv_cap hk1
  have hrem_ops_ge2 : 2 ≤ e2p297_remOps capPts.toNat capPolys.toNat (m.pts.length + m.polys.length) := by
    subst hcapPts0; simpa [e2p297_remOps, e2p297_growOps] using hrem_ops2
  have hrem_cost_ge2 :
      19578 ≤ e2p297_remCost capPts.toNat capPolys.toNat (m.pts.length + m.polys.length) := by
    subst hcapPts0; simpa [e2p297_remCost, e2p297_growCost] using hrem_cost2
  have hfits_mb : FitsEnv M lim st_cur
      (BytesMerge3Env ⟨.lengthDelimited, s0.sp - 152#64, 0#64, 1#64, [], x.bufRef, x.slot, restPtr, rest⟩) :=
    FitsEnv.mono (fun _ hb => (e2p297_bytesMerge3_tight hmb hv_le hb).mono hrem_ops_ge2
      hrem_cost_ge2 (Nat.le_refl _)) hfits_rem
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
  conv => arg 4; rw [e2p297_polyEncoderPinnedLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
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
    (ret_pc := (blkPl_297).base + 268#64) hBytesCall hinv
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
  conv => arg 4; rw [e2p297_pinned_unfold_polys]
  conv => arg 4; simp only [sepConj_assoc]
  apply sepWPp_focus_pure (by sep_focus); intro htrm
  apply sepWPp_focus_pure (by sep_focus); intro hevs_mb
  apply sepWPp_focus_pure (by sep_focus); intro hsm0
  apply sepWPp_focus_pure (by sep_focus); intro _hcap_ok
  apply sepWPp_focus_pure (by sep_focus); rintro ⟨hlen_le, hcap_bound, hptr_ne⟩
  conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp]
  have hmb_tight : SpqrTightEvs 2 19578 2560 evs_mb :=
    e2p297_bytesMerge3_tight hmb hv_le hevs_mb
  by_cases hcap_eq : m.polys.length = capPolys.toNat
  · have hcap_lt16 : capPolys.toNat < 16 := by omega
    obtain ⟨hv_new, _, hops_new, hcost_new⟩ := e2p297_validVecCap_step hv_cap hcap_lt16
    obtain ⟨hrem3, hrem_cost3⟩ := hrem_grow hcap_lt16
    have hseq_mb : FitsEnv M lim st_cur
        (SeqEnv (SpqrTightEvs 2 19578 2560)
          (SpqrTightEvs 1 (if capPolys.toNat = 0 then 1997 else 9789) 2560)) :=
      FitsEnv.mono (fun _ h => (SpqrTightEvs.seq h).mono
        (by subst hcapPts0; simpa [e2p297_remOps, e2p297_growOps] using hrem3)
        (by subst hcapPts0; simpa [e2p297_remCost, e2p297_growCost] using hrem_cost3)
        (by decide)) hfits_rem
    have hfits_mb_tail : FitsEnv M lim (M.stepEvents evs_mb st_cur)
        (SpqrTightEvs 1 (if capPolys.toNat = 0 then 1997 else 9789) 2560) :=
      hseq_mb.seq_right hmb_tight
    have hbne : (BitVec.ofNat 64 m.polys.length != capPolys) = false := len_eq_cap_bne_false hcap_eq
    have hgrow_bound : max (2 * capPolys.toNat) 4 * 24 + 8 ≤ 2 ^ 63 := by omega
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 621) hinvm
    apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecBuf_vecU8_entails_grow_pre A.repAlloc capPolys ptrPolys m.polys hcap_eq)
      (by sep_focus)
    conv => arg 4; rw [polyBelow_extHook s0.sp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro pins
    wp_focus_pure; rintro ⟨hpins_len, hbytes_len⟩
    wp_steps_sync_pool (lsmpl.base 621)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    have hfits_grow : FitsEnv M lim (M.stepEvents evs_mb st_cur)
        (GrowOneVecU8Env ⟨x.msgPtr + 24#64, capPolys, ptrPolys, vecU8ArrayBytes pins m.polys⟩) :=
      FitsEnv.mono (fun _ hg => e2p297_growOneVecU8_tight hv_cap hcap_lt16 hg) hfits_mb_tail
    refine SepWPp.call_frame_lscro (spec := growOneVecU8BudgetSpec M A lim)
      (x := (⟨x.msgPtr + 24#64, capPolys, ptrPolys, vecU8ArrayBytes pins m.polys⟩,
        M.stepEvents evs_mb st_cur))
      (ret_pc := (blkPl_297).base + 296#64) hGrowCall hinvm'
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      rfl
      ⟨by simp only [arm64_norm, hspm, hx20_m], hbytes_len, hptr_ne,
       by dsimp only [rawVecNewCap]; exact hgrow_bound, hfits_grow⟩
      (by dsimp only [RustCliAllocBudget.live]; rw [bv64_add24_add8]; sep_focus)
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
    have hnew_toNat : (newCapVecU8 capPolys).toNat = max (2 * capPolys.toNat) 4 := by
      unfold newCapVecU8; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt_new : m.polys.length < (newCapVecU8 capPolys).toNat := by rw [hnew_toNat]; omega
    have hbound_new : (newCapVecU8 capPolys).toNat * 24 < 2 ^ 63 := by rw [hnew_toNat]; omega
    have hg_tight : SpqrTightEvs 1 (if capPolys.toNat = 0 then 1997 else 9789) 2560 evs_g :=
      e2p297_growOneVecU8_tight hv_cap hcap_lt16 hevs_g
    have hevs_next : SpqrTightEvs
        (e2p297_doneOps capPts.toNat (newCapVecU8 capPolys).toNat (m.pts.length + (m.polys.length + 1)))
        (e2p297_doneCost capPts.toNat (newCapVecU8 capPolys).toNat (m.pts.length + (m.polys.length + 1)))
        2560 (evs_acc ++ (evs_mb ++ evs_g)) := by
      refine (hevs_acc.append (hmb_tight.append hg_tight)).mono ?_ ?_ (by decide)
      · unfold e2p297_doneOps; rw [hnew_toNat, hops_new]; omega
      · unfold e2p297_doneCost
        rw [hnew_toNat, hcost_new, ← Nat.add_assoc m.pts.length m.polys.length 1, Nat.add_mul]
        omega
    have hst_next : M.stepEvents evs_g (M.stepEvents evs_mb st_cur) =
        M.stepEvents (evs_mb ++ evs_g) st_cur :=
      (AllocCostModel.stepEvents_append M evs_mb evs_g st_cur).symm
    have hst_tot : M.stepEvents (evs_mb ++ evs_g) st_cur =
        M.stepEvents (evs_acc ++ (evs_mb ++ evs_g)) st0 := by
      rw [hst_cur, ← AllocCostModel.stepEvents_append]
    conv => arg 4; dsimp only [rawVecNewCap]
    conv => arg 4; rw [show A.live p' (max (2 * capPolys.toNat) 4 * 24) 8 =
      A.repAlloc.live p' (max (2 * capPolys.toNat) 4 * 24) 8 from rfl,
      show BitVec.ofNat 64 (max (2 * capPolys.toNat) 4) = newCapVecU8 capPolys from rfl, hst_next]
    apply sepWPp_fold
      (grow_post_entails_ready A.repAlloc capPolys p' pins m.polys hcap_eq hpins_len hgrow_bound)
      (by sep_focus)
    apply sepWPp_fold (polyBelow_extHook_entails s0.sp) (by sep_focus)
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (e2p297_tag3_copy_step_cro (st_next := M.stepEvents (evs_mb ++ evs_g) st_cur)
        (v_stk0 := v_stk0) (capPts := capPts) (ptrPts := ptrPts)
        (cap' := newCapVecU8 capPolys) (ptr' := p')
        (cap_e := cap_e) (ptr_e := ptr_e) hsp_align hlt_new hbound_new hp'_ne
        (fun s' => hcont (newCapVecU8 capPolys) p' _ (evs_mb ++ evs_g) s'
          (Or.inl ⟨hpb_p0, hm_p0, hcapPts0, hnew_toNat ▸ hv_new⟩) hevs_next hst_tot)
        hpcm2 hrunm2 hspm2 (htrm2.trans (htrm.trans htr))
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2
        (hx25_2.trans (by rw [hcap_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]))
        ⟨hx26_2, hx27_2, hx28_2, hvregs_2⟩ hinvm2)
  · have hlt : m.polys.length < capPolys.toNat := Nat.lt_of_le_of_ne hlen_le hcap_eq
    have hbne : (BitVec.ofNat 64 m.polys.length != capPolys) = true := len_lt_cap_bne_true hlt
    have hcap_ne0 : capPolys ≠ 0 := by intro h0; subst h0; change m.polys.length < 0 at hlt; omega
    have hevs_next : SpqrTightEvs
        (e2p297_doneOps capPts.toNat capPolys.toNat (m.pts.length + (m.polys.length + 1)))
        (e2p297_doneCost capPts.toNat capPolys.toNat (m.pts.length + (m.polys.length + 1)))
        2560 (evs_acc ++ evs_mb) := by
      refine (hevs_acc.append hmb_tight).mono ?_ ?_ (by decide)
      · unfold e2p297_doneOps; omega
      · unfold e2p297_doneCost
        rw [← Nat.add_assoc m.pts.length m.polys.length 1, Nat.add_mul]; omega
    have hst_tot : M.stepEvents evs_mb st_cur = M.stepEvents (evs_acc ++ evs_mb) st0 := by
      rw [hst_cur, ← AllocCostModel.stepEvents_append]
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 296#64) hinvm
    (conv => arg 4; simp only [hcap_ne0, ↓reduceIte, sepConj_assoc])
    apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps_sync_pool ((blkPl_297).base + 296#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre
      (Entails.of_eq (by
        rw [show A.live ptrPolys (capPolys.toNat * 24) 8 = A.repAlloc.live ptrPolys (capPolys.toNat * 24) 8 from rfl]
        sep_ac_rfl))
      (e2p297_tag3_copy_step_cro (st_next := M.stepEvents evs_mb st_cur)
        (v_stk0 := v_stk0) (capPts := capPts) (ptrPts := ptrPts)
        (cap' := capPolys) (ptr' := ptrPolys)
        (cap_e := cap_e) (ptr_e := ptr_e) hsp_align hlt hcap_bound hptr_ne
        (fun s' => hcont capPolys ptrPolys _ evs_mb s'
          (Or.inl ⟨hpb_p0, hm_p0, hcapPts0, hv_cap⟩) hevs_next hst_tot)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
        (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
         by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')


/-! ## 5. Canonical-Domain Tag-1, Skip, Key-Decode, Loop, & Entry Lemmas -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem e2p297_tag1_step_dom_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyEncoderMergeGhost → List AllocEvent → Prop}
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {g : ProtoPolynomialEncoderGhost} {m : PolynomialEncoder}
    {rest rest' : List (BitVec 8)} {v : BitVec 64} {limit n_rem c_rem : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hdv : decodeVarint rest = some (v, rest'))
    (hfits_rem : FitsEnv M lim st_cur (SpqrTightEvs n_rem c_rem 2560))
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (e2p297_polyEncoderPinnedLoopPre A lim st_cur s0 s' g
          x.msgPtr x.bufRef x.slot x.ptr { m with idx := v.truncate 32 } x.bs rest')
        (WppPost (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_297).base + 432#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (e2p297_polyEncoderPinnedLoopPre A lim st_cur s0 s g
        x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfits_dv : FitsEnv M lim st_cur (DecodeVarint2Env rest) :=
    e2p297_fitsEnv_decodeVarint2_of_some hdv hfits_rem
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
  conv => arg 4; rw [e2p297_polyEncoderPinnedLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    sliceCursorAt, polyBelow_decodeVarint2 s0.sp]
  conv => arg 4; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_297).base + 444#64) hVarintCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp, hx19], hrest_lt, hfits_dv⟩
    (by dsimp only [sliceCursorAt, restPtr]; rw [decodeVarint2Stack_eq]; sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
  have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
  apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 164#64) hinvm
  conv => arg 4; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
  conv => arg 4; rw [decodeVarint2_pool_of_some A lim hdv, decodeVarint2Stack_eq]
  conv => arg 4; simp only [hdv, sepConj_assoc]
  wp_focus_pure; rintro ⟨hsm0, hsm1⟩
  wp_focus_pure; intro htrm
  conv => arg 4; simp only [protoPolynomialEncoderPinnedAt, protoPolynomialEncoderIdxOff,
    polyEncoderToProto, sepConj_assoc, arm64_norm, hsp]
  apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
  apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
  wp_steps_sync_pool ((blkPl_297).base + 164#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinvm'
  refine SepWPp.weaken_pre
    (Entails.of_eq (by
      dsimp only [e2p297_polyEncoderPinnedLoopPre, protoPolynomialEncoderPinnedAt,
        protoPolynomialEncoderIdxOff, polyEncoderToProto]
      sep_ac_rfl))
    (hcont _
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem e2p297_skip_step_dom_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyEncoderMergeGhost → List AllocEvent → Prop}
    (hSkipCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {g : ProtoPolynomialEncoderGhost} {m : PolynomialEncoder}
    {rest rest' : List (BitVec 8)} {iwt : WireType} {tag limit n_rem c_rem : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hsf : skipField (2 * rest.length + 2) 97 tag iwt rest = some rest')
    (hfits_rem : FitsEnv M lim st_cur (SpqrTightEvs n_rem c_rem 2560))
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (e2p297_polyEncoderPinnedLoopPre A lim st_cur s0 s' g
          x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_297).base + 464#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (e2p297_polyEncoderPinnedLoopPre A lim st_cur s0 s g
        x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfits_sf : FitsEnv M lim st_cur
      (SkipField3Env ⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩) :=
    e2p297_fitsEnv_skipField3_of_some hsf hfits_rem
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 263) hinv
  conv => arg 4; rw [e2p297_polyEncoderPinnedLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf]
  conv => arg 4; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 263)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := skipField3Spec A lim)
    (x := (⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_297).base + 476#64) hSkipCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl
    ⟨by simp only [arm64_norm, hsp, hx0, setWidth8_ofNat64_wt],
     by simp only [arm64_norm, hsp, hx1], htag_lt,
     by simp only [arm64_norm, hsp, hx19],
     by simp only [arm64_norm, hsp], (by decide : 97 < 2 ^ 32), hrest_lt, hfits_sf⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
  have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
  apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 164#64) hinvm
  (conv => arg 4; simp only [skipField3Spec, hsf, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro evs_sf
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_sf
  wp_focus_pure; intro hsm0
  have hevs_nil : evs_sf = [] := by
    change SkipFieldEnv _ evs_sf at hevs_sf
    simpa [SkipFieldEnv, skipFieldEventsCore, hsf] using hevs_sf
  subst hevs_nil
  conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
  apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
  wp_steps_sync_pool ((blkPl_297).base + 164#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinvm'
  refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [e2p297_polyEncoderPinnedLoopPre]; sep_ac_rfl))
    (hcont _
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem e2p297_decode_key_dom_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyEncoderMergeGhost → List AllocEvent → Prop}
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {g : ProtoPolynomialEncoderGhost} {m : PolynomialEncoder}
    {cur rest : List (BitVec 8)} {key : BitVec 64} {iwt : WireType} {limit n_rem c_rem : Nat}
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_ge : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (hitag0 : ¬ key.toNat / 8 < 1)
    (hfits_rem : FitsEnv M lim st_cur (SpqrTightEvs n_rem c_rem 2560))
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_297).base + 216#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (e2p297_polyEncoderPinnedLoopPre A lim st_cur s0 s' g
          x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_297).base + 164#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (e2p297_polyEncoderPinnedLoopPre A lim st_cur s0 s g
        x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  have hfits_dv : FitsEnv M lim st_cur (DecodeVarint2Env cur) :=
    e2p297_fitsEnv_decodeVarint2_of_some hd hfits_rem
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
  conv => arg 4; rw [e2p297_polyEncoderPinnedLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, polyBelow_decodeVarint2 s0.sp]
  conv => arg 4; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, st_cur))
    (ret_pc := (blkPl_297).base + 184#64) hVarintCall hinv
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
  have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
  have hshr := key_shr32_of_lt hk_ge
  obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
  obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
  obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
  obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
  have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
  apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 216#64) hinvm
  conv => arg 4; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
  conv => arg 4; rw [decodeVarint2_pool_of_some A lim hd, decodeVarint2Stack_eq]
  conv => arg 4; simp only [hd, sepConj_assoc]
  wp_focus_pure; rintro ⟨hsm0, hsm1⟩
  wp_focus_pure; intro htrm
  conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp]
  apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
  apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
  wp_steps_sync_pool ((blkPl_297).base + 216#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinvm'
  refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [e2p297_polyEncoderPinnedLoopPre]; sep_ac_rfl))
    (hcont _
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm1, hand_wt])
      (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')


set_option maxRecDepth 200000 in
set_option maxHeartbeats 600000 in
set_option linter.unusedSimpArgs false in
private theorem e2p297_loop_dom_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {maxOps cumCap maxReq : Nat}
    (hOps : 35 ≤ maxOps) (hCum : 334823 ≤ cumCap) (hReq : 2560 ≤ maxReq)
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim)))
    {x : PolyEncoderMergeGhost} {st0 : M.σ} {R : SepProp}
    {s0 : State} {pb : PolynomialEncoder} {rest_fin : List (BitVec 8)} {limit : Nat}
    (hDom : tlb_PolyEncoderDom x)
    (hpb : tlb_ValidPolyEncoderPB pb)
    (hsome_top : (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      some (pb, rest_fin))
    (hFit0 : FitsEnv M lim st0 (SpqrTightEvs maxOps cumCap maxReq))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    ∀ (n : Nat) (capPts ptrPts capPolys ptrPolys : BitVec 64) (m : PolynomialEncoder)
      (cur : List (BitVec 8)) (st_cur : M.σ) (evs_acc : List AllocEvent) (s : State),
      cur.length ≤ limit + n → cur.length ≤ x.bs.length →
      m.pts.length + cur.length < 2 ^ 56 → m.polys.length + cur.length < 2 ^ 56 →
      IsDropSuffix x.bs cur →
      e2p297_CapPairInv pb m capPts capPolys →
      SpqrTightEvs
        (e2p297_doneOps capPts.toNat capPolys.toNat (m.pts.length + m.polys.length))
        (e2p297_doneCost capPts.toNat capPolys.toNat (m.pts.length + m.polys.length))
        2560 evs_acc →
      st_cur = M.stepEvents evs_acc st0 →
      (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        (mergeLoopBin PolynomialEncoder.mergeField (cur.length - limit) m cur limit 97).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (blkPl_297).base + 164#64 →
      s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
        (e2p297_polyEncoderPinnedLoopPre A lim st_cur s0 s
          ⟨⟨capPts, ptrPts⟩, ⟨capPolys, ptrPolys⟩⟩
          x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (polyEncoderMergeSpecOfEnv A lim
          (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)
          (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim
          (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)
          (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)) (x, st0) R s0) := by
  intro n
  induction n with
  | zero =>
    intro capPts ptrPts capPolys ptrPolys m cur st_cur evs_acc s hcur_n hcur_le _ _ hcur_suf hinv_c
      hevs_acc hst_cur hres_cur hpc hrun hsp htr _ _ hx21 hx22 _ _ hcs hinv
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
        (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
          some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    have hm_eq : m = pb := by
      rw [hsome_top] at hsome; exact (Prod.mk.inj (Option.some.inj hsome.symm)).1
    have hk_le : m.pts.length + m.polys.length ≤ 16 := hm_eq ▸ hpb.2.1
    obtain ⟨hops_sum, hcost_sum⟩ := e2p297_done_add_rem hinv_c hk_le
    have hevs_post : e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq x evs_acc :=
      Or.inl ⟨hDom, hevs_acc.mono (by omega) (by omega) hReq⟩
    obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
    subst hst_cur
    apply SepWPp.of_sepWP_ret
    unfold WppPost polyEncoderMergeSpecOfEnv
    simp only [hsome, e2p297_polyEncoderPinnedLoopPre, polySavedRegsAny, polySavedRegs,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp]
    apply SepWP.exists_elim; intro v_pad
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    apply SepWP.fold (e2p297_pinned_entails_unpinned A.repAlloc
      ⟨⟨capPts, ptrPts⟩, ⟨capPolys, ptrPolys⟩⟩ x.msgPtr (polyEncoderToProto m)) (by sep_focus)
    apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
    wp_done
  | succ n ih =>
    intro capPts ptrPts capPolys ptrPolys m cur st_cur evs_acc s hcur_n hcur_le hpts_bound
      hpolys_bound hcur_suf hinv_c hevs_acc hst_cur hres_cur hpc hrun hsp htr
      hx19 hx20 hx21 hx22 hx23 hx24 hcs hinv
    have hloop_some :
        mergeLoopBin PolynomialEncoder.mergeField (cur.length - limit) m cur limit 97 = some pb := by
      have h1 := hsome_top.symm.trans hres_cur
      rcases hml : mergeLoopBin PolynomialEncoder.mergeField (cur.length - limit) m cur limit 97 with _ | m'
      · simp [hml] at h1
      · simp only [hml, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
        exact congrArg some h1.1.symm
    obtain ⟨⟨sfx_pts, hsfx_pts⟩, ⟨sfx_polys, hsfx_polys⟩⟩ := e2p297_mergeLoopBin_prefix hloop_some
    have hk_le : m.pts.length + m.polys.length ≤ 16 := by
      have h1 := congrArg List.length hsfx_pts
      have h2 := congrArg List.length hsfx_polys
      simp only [List.length_append] at h1 h2
      have := hpb.2.1; omega
    have hfits_rem := e2p297_fitsEnv_rem_tight hOps hCum hReq hinv_c hk_le hFit0 hevs_acc hst_cur
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
          (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
            some (m, cur) := by
        rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
      obtain ⟨hops_sum, hcost_sum⟩ := e2p297_done_add_rem hinv_c hk_le
      have hevs_post : e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq x evs_acc :=
        Or.inl ⟨hDom, hevs_acc.mono (by omega) (by omega) hReq⟩
      obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
      subst hst_cur
      apply SepWPp.of_sepWP_ret
      unfold WppPost polyEncoderMergeSpecOfEnv
      simp only [hsome, e2p297_polyEncoderPinnedLoopPre, polySavedRegsAny, polySavedRegs,
        sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp]
      apply SepWP.exists_elim; intro v_pad
      wp_steps_sync_pool (s0.readReg64 Reg.lr)
      simp only [State.setMem_setMem]
      apply SepWP.fold (e2p297_pinned_entails_unpinned A.repAlloc
        ⟨⟨capPts, ptrPts⟩, ⟨capPolys, ptrPolys⟩⟩ x.msgPtr (polyEncoderToProto m)) (by sep_focus)
      apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
      wp_done
    · have hcur_lt : cur.length < 2 ^ 63 := by omega
      obtain ⟨⟨key, rest⟩, hd⟩ : ∃ p, decodeVarint cur = some p := by
        cases hd' : decodeVarint cur with
        | none =>
          rw [mergeLoopBin_of_decodeVarint_none protoPrefixStep_polynomialEncoder_mergeField
            hle_lim hd'] at hloop_some
          cases hloop_some
        | some p => exact ⟨p, rfl⟩
      have hk_ge : ¬ 2 ^ 32 ≤ key.toNat := by
        intro hge
        rw [mergeLoopBin_of_key_ge protoPrefixStep_polynomialEncoder_mergeField
          hle_lim hd hge] at hloop_some
        cases hloop_some
      obtain ⟨iwt, hwt⟩ : ∃ w, WireType.ofNat? (key.toNat % 8) = some w := by
        cases hw : WireType.ofNat? (key.toNat % 8) with
        | none =>
          rw [mergeLoopBin_of_wt_none protoPrefixStep_polynomialEncoder_mergeField
            hle_lim hd hk_ge hw] at hloop_some
          cases hloop_some
        | some w => exact ⟨w, rfl⟩
      have hitag0 : ¬ key.toNat / 8 < 1 := by
        intro h0
        rw [mergeLoopBin_of_tag_zero protoPrefixStep_polynomialEncoder_mergeField
          hle_lim hd hk_ge hwt h0] at hloop_some
        cases hloop_some
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := by omega
      have hrest_suf : IsDropSuffix x.bs rest :=
        suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 97)
        protoPrefixStep_polynomialEncoder_mergeField hle_lim hd hk_ge hwt hitag0
      refine e2p297_decode_key_dom_cro hVarintCall hle_lim hsp_align hcur_le hcur_lt hcur_suf
        hd hk_ge hwt hitag0 hfits_rem
        (fun s' hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hcs' hinv' => ?_)
        hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs hinv
      obtain ⟨hx26', hx27', hx28', hvregs'⟩ := hcs'
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hloop_ok; rw [polynomialEncoder_mergeField_tag1] at hloop_ok
        have hiwt : iwt = .varint := by
          by_contra hne; simp only [hloop_ok, hne, ↓reduceIte] at hloop_some; cases hloop_some
        subst hiwt; dsimp [WireType.toNat] at hx0'
        obtain ⟨⟨v, rest'⟩, hdv⟩ : ∃ p, decodeVarint rest = some p := by
          cases hd' : decodeVarint rest with
          | none =>
            simp only [hloop_ok, ↓reduceIte, hd', Option.map_none] at hloop_some; cases hloop_some
          | some p => exact ⟨p, rfl⟩
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 432#64) hinv'
        conv => arg 4; dsimp only [e2p297_polyEncoderPinnedLoopPre]
        wp_steps_sync_pool ((blkPl_297).base + 432#64); simp only [State.setMem_setMem]
        wp_reach; intro hinvm'
        refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [e2p297_polyEncoderPinnedLoopPre]; sep_ac_rfl))
          (e2p297_tag1_step_dom_cro (limit := limit) hVarintCall hsp_align hrest_le hrest_lt hrest_suf hdv hfits_rem
            (fun s'' hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp'])
            (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0'])
            (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
            (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24'])
            ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
             by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinvm')
        have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv
        have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
        have hres_next :
            (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
              (mergeLoopBin PolynomialEncoder.mergeField (rest'.length - limit)
                { m with idx := v.truncate 32 } rest' limit 97).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
          simp only [hres_cur, hloop_ok, ↓reduceIte, hdv, Option.map_some]
        exact ih capPts ptrPts capPolys ptrPolys { m with idx := v.truncate 32 } rest' st_cur evs_acc s''
          (by omega) (by omega) (by dsimp; omega) (by dsimp; omega)
          (suffix_trans hrest_le hrest_suf hrest'_le_rest (decodeVarint_suffix hdv))
          hinv_c hevs_acc hst_cur hres_next
          hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv''
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hloop_ok; rw [polynomialEncoder_mergeField_tag2] at hloop_ok
          obtain ⟨⟨v, rest'⟩, hmb⟩ : ∃ p, mergeBytes iwt rest = some p := by
            cases hm' : mergeBytes iwt rest with
            | none => simp only [hloop_ok, hm'] at hloop_some; cases hloop_some
            | some p => exact ⟨p, rfl⟩
          have hiwt : iwt = .lengthDelimited := by
            by_contra hne; rw [mergeBytes_eq_none_of_ne_len hne] at hmb; cases hmb
          subst hiwt; dsimp [WireType.toNat] at hx0'
          have hloop_next :
              mergeLoopBin PolynomialEncoder.mergeField (rest'.length - limit)
                { m with pts := m.pts ++ [v] } rest' limit 97 = some pb := by
            simpa only [hloop_ok, hmb, Option.map_some] using hloop_some
          obtain ⟨⟨sfx1, hsfx1⟩, ⟨sfx2, hsfx2⟩⟩ := e2p297_mergeLoopBin_prefix hloop_next
          have hv_in : v ∈ pb.pts := by
            rw [hsfx1]; simp
          have hv_le : v.length ≤ 2560 := hpb.2.2.1 v hv_in
          have hk1 : (m.pts.length + m.polys.length) + 1 ≤ 16 := by
            have h1 := congrArg List.length hsfx1
            have h2 := congrArg List.length hsfx2
            simp only [List.length_append, List.length_singleton] at h1 h2
            have := hpb.2.1; omega
          have ⟨hpolys0, hv_capPts⟩ :
              (pb.polys = [] ∧ m.polys = [] ∧ capPolys = 0#64) ∧ e2p297_ValidVecCap capPts.toNat := by
            rcases hinv_c with ⟨hpb_pts0, _, _, _⟩ | ⟨hp0, hm0, hc0, hv_c⟩
            · exfalso
              have hlen1 := congrArg List.length hsfx1
              simp [hpb_pts0] at hlen1
            · exact ⟨⟨hp0, hm0, hc0⟩, hv_c⟩
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 336#64) hinv'
          conv => arg 4; dsimp only [e2p297_polyEncoderPinnedLoopPre]
          wp_steps_sync_pool ((blkPl_297).base + 336#64); simp only [State.setMem_setMem]
          wp_reach; intro hinvm'
          refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [e2p297_polyEncoderPinnedLoopPre]; sep_ac_rfl))
            (e2p297_tag2_step_dom_cro (limit := limit) hBytesCall hGrowCall hsp_align hrest_le (by omega) hrest_suf
              hmb hv_le hk1 hpolys0 hv_capPts hevs_acc hst_cur hfits_rem
              (fun cap' ptr' st_next evs_step s'' hinv_next hevs_next hst_next
                  hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp'])
              (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0'])
              (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
              (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
              (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24'])
              ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
               by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinvm')
          have hrest'_le_rest : rest'.length ≤ rest.length := mergeBytes_length hmb
          have hmb_len := mergeBytes_len_bound hmb
          have hres_next :
              (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                (mergeLoopBin PolynomialEncoder.mergeField (rest'.length - limit)
                  { m with pts := m.pts ++ [v] } rest' limit 97).map
                    (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, hmb, Option.map_some]
          have hlen_pts' : (m.pts ++ [v]).length = m.pts.length + 1 := by simp
          exact ih cap' ptr' capPolys ptrPolys { m with pts := m.pts ++ [v] } rest' st_next
            (evs_acc ++ evs_step) s''
            (by omega) (by omega) (by simp; omega) (by dsimp; omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
            hinv_next (by simpa only [hlen_pts'] using hevs_next) hst_next hres_next
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv''
        · by_cases htag3 : key.toNat / 8 = 3
          · rw [htag3] at hx1' hloop_ok; rw [polynomialEncoder_mergeField_tag3] at hloop_ok
            obtain ⟨⟨v, rest'⟩, hmb⟩ : ∃ p, mergeBytes iwt rest = some p := by
              cases hm' : mergeBytes iwt rest with
              | none => simp only [hloop_ok, hm'] at hloop_some; cases hloop_some
              | some p => exact ⟨p, rfl⟩
            have hiwt : iwt = .lengthDelimited := by
              by_contra hne; rw [mergeBytes_eq_none_of_ne_len hne] at hmb; cases hmb
            subst hiwt; dsimp [WireType.toNat] at hx0'
            have hloop_next :
                mergeLoopBin PolynomialEncoder.mergeField (rest'.length - limit)
                  { m with polys := m.polys ++ [v] } rest' limit 97 = some pb := by
              simpa only [hloop_ok, hmb, Option.map_some] using hloop_some
            obtain ⟨⟨sfx1, hsfx1⟩, ⟨sfx2, hsfx2⟩⟩ := e2p297_mergeLoopBin_prefix hloop_next
            have hv_in : v ∈ pb.polys := by
              rw [hsfx2]; simp
            have hv_le : v.length ≤ 2560 := hpb.2.2.2 v hv_in
            have hk1 : (m.pts.length + m.polys.length) + 1 ≤ 16 := by
              have h1 := congrArg List.length hsfx1
              have h2 := congrArg List.length hsfx2
              simp only [List.length_append, List.length_singleton] at h1 h2
              have := hpb.2.1; omega
            have ⟨hpts0, hv_capPolys⟩ :
                (pb.pts = [] ∧ m.pts = [] ∧ capPts = 0#64) ∧ e2p297_ValidVecCap capPolys.toNat := by
              rcases hinv_c with ⟨hp0, hm0, hc0, hv_c⟩ | ⟨hpb_polys0, _, _, _⟩
              · exact ⟨⟨hp0, hm0, hc0⟩, hv_c⟩
              · exfalso
                have hlen2 := congrArg List.length hsfx2
                simp [hpb_polys0] at hlen2
            apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 240#64) hinv'
            conv => arg 4; dsimp only [e2p297_polyEncoderPinnedLoopPre]
            wp_steps_sync_pool ((blkPl_297).base + 240#64); simp only [State.setMem_setMem]
            wp_reach; intro hinvm'
            refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [e2p297_polyEncoderPinnedLoopPre]; sep_ac_rfl))
              (e2p297_tag3_step_dom_cro (limit := limit) hBytesCall hGrowCall hsp_align hrest_le (by omega) hrest_suf
                hmb hv_le hk1 hpts0 hv_capPolys hevs_acc hst_cur hfits_rem
                (fun cap' ptr' st_next evs_step s'' hinv_next hevs_next hst_next
                    hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' => ?_)
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp'])
                (by simp only [arm64_norm, htr'])
                (by simp only [arm64_norm, hx0'])
                (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
                (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
                (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24'])
                ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
                 by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinvm')
            have hrest'_le_rest : rest'.length ≤ rest.length := mergeBytes_length hmb
            have hmb_len := mergeBytes_len_bound hmb
            have hres_next :
                (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                  (mergeLoopBin PolynomialEncoder.mergeField (rest'.length - limit)
                    { m with polys := m.polys ++ [v] } rest' limit 97).map
                      (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              simp only [hres_cur, hloop_ok, hmb, Option.map_some]
            have hlen_polys' : (m.polys ++ [v]).length = m.polys.length + 1 := by simp
            exact ih capPts ptrPts cap' ptr' { m with polys := m.polys ++ [v] } rest' st_next
              (evs_acc ++ evs_step) s''
              (by omega) (by omega) (by dsimp; omega) (by simp; omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
              hinv_next (by simpa only [hlen_polys'] using hevs_next) hst_next hres_next
              hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv''
          · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
            obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 hitag_lt (by decide : 1 < 2 ^ 32)
            obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 hitag_lt (by decide : 2 < 2 ^ 32)
            obtain ⟨hb3_1, _⟩ := itag_beq_tag_false htag3 hitag_lt (by decide : 3 < 2 ^ 32)
            have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by
              rw [sf_truncate32_ofNat64]; exact hb1_1
            have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by
              rw [sf_truncate32_ofNat64]; exact hb2_1
            have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 3#32) = false := by
              rw [sf_truncate32_ofNat64]; exact hb3_1
            have hb3_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 3#32) = true := by
              simp only [bne, hb3_1, Bool.not_false]
            have hb3_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 3#32) = true := by
              simp only [bne, hb3_2, Bool.not_false]
            rw [polynomialEncoder_mergeField_other m iwt rest 97 hitag_lt htag1 htag2 htag3] at hloop_ok
            obtain ⟨rest', hsf⟩ : ∃ r, skipField (2 * rest.length + 2) 97 (key.toNat / 8) iwt rest = some r := by
              cases hs' : skipField (2 * rest.length + 2) 97 (key.toNat / 8) iwt rest with
              | none => rw [hloop_ok, hs'] at hloop_some; cases hloop_some
              | some r => exact ⟨r, rfl⟩
            apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 464#64) hinv'
            conv => arg 4; dsimp only [e2p297_polyEncoderPinnedLoopPre]
            wp_steps_sync_pool ((blkPl_297).base + 464#64); simp only [State.setMem_setMem]
            wp_reach; intro hinvm'
            refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [e2p297_polyEncoderPinnedLoopPre]; sep_ac_rfl))
              (e2p297_skip_step_dom_cro (limit := limit) hSkipCall hsp_align hrest_le hrest_lt hrest_suf hitag_lt
                hsf hfits_rem
                (fun s'' hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' => ?_)
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp'])
                (by simp only [arm64_norm, htr'])
                (by simp only [arm64_norm, hx0'])
                (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64])
                (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
                (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
                (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24'])
                ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
                 by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinvm')
            have hrest'_le_rest : rest'.length ≤ rest.length :=
              (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
            have hres_next :
                (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                  (mergeLoopBin PolynomialEncoder.mergeField (rest'.length - limit)
                    m rest' limit 97).map
                      (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              simp only [hres_cur, hloop_ok, hsf, Option.map_some]
            exact ih capPts ptrPts capPolys ptrPolys m rest' st_cur evs_acc s''
              (by omega) (by omega) (by omega) (by omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest
                ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
              hinv_c hevs_acc hst_cur hres_next
              hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv''


set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem e2p297_polyEncoderMerge_dom_sepWPp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {maxOps cumCap maxReq : Nat}
    (hOps : 35 ≤ maxOps) (hCum : 334823 ≤ cumCap) (hReq : 2560 ≤ maxReq)
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim)))
    {x : PolyEncoderMergeGhost} {st0 : M.σ} {R : SepProp} {s0 : State}
    {ptrPts0 ptrPolys0 : BitVec 64} {pb : PolynomialEncoder} {rest_fin : List (BitVec 8)}
    (hDom : tlb_PolyEncoderDom x)
    (hwt_ld : x.wt = .lengthDelimited)
    (hmsg0 : x.msg = default)
    (hpb : tlb_ValidPolyEncoderPB pb)
    (hsome_top : (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      some (pb, rest_fin))
    (hpc : s0.pc = (blkPl_297).base) (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (h_1 : (s0.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat)
    (h_2 : s0.readReg64 .x1 = x.msgPtr) (h_3 : s0.readReg64 .x2 = x.bufRef)
    (h_pts_bound : x.msg.pts.length + x.bs.length < 2 ^ 56)
    (h_polys_bound : x.msg.polys.length + x.bs.length < 2 ^ 56)
    (hFit0 : FitsEnv M lim st0 (SpqrTightEvs maxOps cumCap maxReq))
    (hinv0 : LibsignalCodeRoLoaded lsmpl s0.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s0
      (protoPolynomialEncoderPinnedAt A.repAlloc ⟨⟨0#64, ptrPts0⟩, ⟨0#64, ptrPolys0⟩⟩
          x.msgPtr (polyEncoderToProto x.msg) ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
        A.pool lim st0 s0 ∗ stackAt s0.sp polyMergeStack)
      (WppPost (polyEncoderMergeSpecOfEnv A lim
        (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)
        (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim
        (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)
        (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)) (x, st0) R s0) := by
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
      have hnone :
          (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialEncoder_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hd']
      rw [hnone] at hsome_top; cases hsome_top
    | some p => exact ⟨p, rfl⟩
  have hlt_len : ¬ rest0.length < len.toNat := by
    intro hlt
    have hnone :
        (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialEncoder_mergeField]
      simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0, hlt]
    rw [hnone] at hsome_top; cases hsome_top
  have hfits_dv0 : FitsEnv M lim st0 (DecodeVarint2Env x.bs) :=
    e2p297_fitsEnv_decodeVarint2_of_some hdv0 hFit0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv0
  conv => arg 4; rw [stackAt_polyMerge_prologue s0.sp, polyBelow_decodeVarint2 s0.sp]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v9
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  apply SepWP.fold (polySavedRegs_entails_any s0.sp s0 v3) (by unfold polySavedRegs; sep_focus)
  wp_reach; intro hinv0'
  refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, x.ptr, x.bs⟩, st0))
    (ret_pc := (blkPl_297).base + 56#64) hVarintCall hinv0'
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
      (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        (mergeLoopBin PolynomialEncoder.mergeField
          (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97).map
            (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
    rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialEncoder_mergeField]
    simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte, proto_decodeVarint_toOption, hdv0, hlt_len, hdrop_eq]
    rcases mergeLoopBin PolynomialEncoder.mergeField
      (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97 with _ | m' <;> rfl
  apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 164#64) hinvm
  conv => arg 4; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
  conv => arg 4; rw [decodeVarint2_pool_of_some A lim hdv0, decodeVarint2Stack_eq]
  conv => arg 4; simp only [hdv0, sepConj_assoc]
  wp_focus_pure; rintro ⟨hsm0, hsm1⟩
  wp_focus_pure; intro htrm
  conv => arg 4; simp only [sepConj_assoc, arm64_norm]
  apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
  conv => arg 4; simp only [sepConj_assoc]
  wp_steps_sync_pool ((blkPl_297).base + 164#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinvm'
  have hinv_init : e2p297_CapPairInv pb x.msg 0#64 0#64 := by
    have hm_pts0 : x.msg.pts = [] := by rw [hmsg0]; rfl
    have hm_polys0 : x.msg.polys = [] := by rw [hmsg0]; rfl
    rcases hpb.1 with hp0 | hp0
    · exact Or.inl ⟨hp0, hm_pts0, rfl, Or.inl rfl⟩
    · exact Or.inr ⟨hp0, hm_polys0, rfl, Or.inl rfl⟩
  have hevs_init : SpqrTightEvs
      (e2p297_doneOps (0#64).toNat (0#64).toNat (x.msg.pts.length + x.msg.polys.length))
      (e2p297_doneCost (0#64).toNat (0#64).toNat (x.msg.pts.length + x.msg.polys.length))
      2560 [] :=
    SpqrTightEvs.nil _ _ _
  refine SepWPp.weaken_pre
    (Entails.of_eq (by
      rw [e2p297_polyEncoderPinnedLoopPre, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
      sep_ac_rfl))
    (e2p297_loop_dom_cro hOps hCum hReq hVarintCall hSkipCall hBytesCall hGrowCall
      hDom hpb hsome_top hFit0 hsp_align rest0.length 0#64 ptrPts0 0#64 ptrPolys0
      x.msg rest0 st0 [] _
      (by omega) hrest0_le (by omega) (by omega) hrest0_suf hinv_init hevs_init rfl hres0
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')

/-! ## 6. Guarded `Dom` / `¬ Dom` Glue & Exported Tight Contracts (`Block 297`) -/

private theorem e2p297_rebase_to_blockProgram [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee : IsLsBlockProg calleeProg j H] {spec : Spec α}
    (h : subroutine_ok calleeProg (libsignalSessionLib.blockPlacement lsmpl j).base spec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j) spec := by
  have h' : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H)
      (libsignalSessionLib.blockPlacement lsmpl j).base spec :=
    hcallee.eq_blockProgram ▸ h
  rwa [ls_blockPlacement_base (i := j)] at h'

private theorem e2p297_domAt_entails_tlb_domHeap (A : RustAlloc) (x : PolyEncoderMergeGhost) :
    e2p297_protoPolynomialEncoderDomAt tlb_PolyEncoderDom A x ⊢
      tlb_domHeap tlb_PolyEncoderDom
        (fun x => tlb_polyEncoderZeroCapAt A x.msgPtr (polyEncoderToProto x.msg))
        (fun x => protoPolynomialEncoderAt A x.msgPtr (polyEncoderToProto x.msg)) x := by
  classical
  unfold e2p297_protoPolynomialEncoderDomAt
  refine Entails.sepExists_elim fun g => Entails.pure_left fun hcap => ?_
  by_cases hDom : tlb_PolyEncoderDom x
  · rw [tlb_domHeap_of_dom hDom]
    rcases g with ⟨⟨capPts, ptrPts⟩, ⟨capPolys, ptrPolys⟩⟩
    obtain ⟨hc1, hc2⟩ := hcap hDom
    subst hc1; subst hc2
    exact tlb_polyEncoderZeroCapAt_of_ptrs A ptrPts ptrPolys x.msgPtr (polyEncoderToProto x.msg)
  · rw [tlb_domHeap_of_not_dom hDom, protoPolynomialEncoderAt_eq_exists_pinned]
    exact Entails.sepExists_right g (Entails.refl _)

private noncomputable def e2p297_polyEncoderDomOnlySpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (maxOps cumCap maxReq : Nat) :
    Spec (PolyEncoderMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜tlb_PolyEncoderDom x⌝ ∗
      (tlb_polyEncoderMergeTightSpecOfEnv A lim
        (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)
        (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)).pre (x, st) s
  post := (tlb_polyEncoderMergeTightSpecOfEnv A lim
    (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)
    (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)).post

private theorem e2p297_polyEncoderDomOnly_cro_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {maxOps cumCap maxReq : Nat}
    (hOps : 35 ≤ maxOps) (hCum : 334823 ≤ cumCap) (hReq : 2560 ≤ maxReq)
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (blkPl_297).base
      (withLsCodeRoLoaded lsmpl (e2p297_polyEncoderDomOnlySpec A lim maxOps cumCap maxReq)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp e2p297_polyEncoderDomOnlySpec
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp_align
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply SepWPp.elim_lscroProp; intro hinv0
  change SepWPp _ _ _ _
    (WppPost (polyEncoderMergeSpecOfEnv A lim
      (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)
      (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)) (x, st0) R s0)
    (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim
      (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)
      (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)) (x, st0) R s0)
  unfold tlb_polyEncoderMergeTightSpecOfEnv
  dsimp only
  apply SepWPp.pure_elim; intro hDom
  apply SepWPp.pure_elim; rintro ⟨h_1, h_2, h_3, h_pts_bound, h_polys_bound, hFit0⟩
  rcases hDom with ⟨hwt_p, hmsg0, pb, rest_fin, hpb, hbs_eq⟩
  have hwt_ld : x.wt = .lengthDelimited := by
    cases hx : x.wt <;> simp [hx, codecWireTypeToProto] at hwt_p
    rfl
  have hDom' : tlb_PolyEncoderDom x := ⟨hwt_p, hmsg0, pb, rest_fin, hpb, hbs_eq⟩
  have hsome_top :
      (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        some (pb, rest_fin) := by
    rw [hwt_p, hmsg0, hbs_eq, e2p297_mergeMessage_polyEncoder_of_valid rest_fin hpb]
    rfl
  have hFit_tight : FitsEnv M lim st0 (SpqrTightEvs maxOps cumCap maxReq) :=
    FitsEnv.mono (fun _ ht => Or.inl ⟨hDom', ht⟩) hFit0
  rw [tlb_domHeap_of_dom hDom']
  unfold tlb_polyEncoderZeroCapAt
  conv => arg 4; simp only [sepExists_sepConj_left]
  apply SepWPp.exists_elim; intro ptrPts0
  apply SepWPp.exists_elim; intro ptrPolys0
  exact e2p297_polyEncoderMerge_dom_sepWPp hOps hCum hReq
    hVarintCall hSkipCall hBytesCall hGrowCall
    hDom' hwt_ld hmsg0 hpb hsome_top hpc hrun hsp_align'
    h_1 h_2 h_3 h_pts_bound h_polys_bound hFit_tight hinv0

/-- Parametric guarded-tight contract for Block `297` (`PolynomialEncoder::merge`) on
`tlb_polyEncoderMergeTightSpecOfEnv` (`35 ≤ maxOps`, `334823 ≤ cumCap`, `2560 ≤ maxReq`). -/
theorem e2p297_tlb_polyEncoderMerge_cro_placed_tight_ok_of_bounds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {maxOps cumCap maxReq : Nat}
    (hOps : 35 ≤ maxOps) (hCum : 334823 ≤ cumCap) (hReq : 2560 ≤ maxReq)
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (blkPl_297).base
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)
          (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq))) := by
  classical
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp_align _hcl
  by_cases hDom : tlb_PolyEncoderDom x
  · refine (e2p297_polyEncoderDomOnly_cro_ok hOps hCum hReq
      hVarintCall hSkipCall hBytesCall hGrowCall).mono_outcome
      (x, st0) R s0 hpc hrun ?_ hsp_align (fun _ hout => hout)
    obtain ⟨hcro, hp⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [withLsCodeRoLoaded, e2p297_polyEncoderDomOnlySpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hDom, hp⟩
  · have hpre_fb :
        s0.mem ⊨ (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)).pre (x, st0) s0 ∗ R := by
      obtain ⟨hcro, hp⟩ := extract_withLsCodeRoLoaded hpre
      unfold tlb_polyEncoderMergeTightSpecOfEnv at hp
      unfold withLsCodeRoLoaded polyEncoderMergeSpec polyEncoderMergeSpecOfEnv
      dsimp only at hp ⊢
      rw [tlb_domHeap_of_not_dom hDom] at hp
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcro, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1, hp.1.2.2.2.2.1,
        tlb_fitsEnv_fallback_of_not_dom hDom hp.1.2.2.2.2.2⟩, hp.2⟩
    refine (polyEncoderMerge_cro_placed_ok_of_contracts
      hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall).mono_outcome
      (x, st0) R s0 hpc hrun hpre_fb hsp_align fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hq⟩ | hp | hex | hoom
    · refine Or.inl ⟨hret, hcc, ?_⟩
      unfold withLsCodeRoLoaded polyEncoderMergeSpec polyEncoderMergeSpecOfEnv at hq
      unfold withLsCodeRoLoaded tlb_polyEncoderMergeTightSpecOfEnv polyEncoderMergeSpecOfEnv
      dsimp only at hq ⊢
      exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (Entails.sepExists_mono fun evs =>
          Entails.pure_left fun h1 => Entails.pure_right
            (Or.inr ⟨hDom, polyEncoderMergePostEnv_imp_pre h1⟩) (Entails.refl _)))))) hq
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl hex))
    · exact Or.inr (Or.inr (Or.inr hoom))

/-- Guarded-tight contract for Block `297` (`PolynomialEncoder::merge`) on
`tlb_polyEncoderMergeTightSpecOfEnv` at `tlb_PolyEncoderGuardedEnvOf maxOps` (`35 ≤ maxOps`). -/
theorem e2p297_tlb_polyEncoderMerge_cro_placed_tight_ok_of [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {maxOps : Nat}
    (hOps : 35 ≤ maxOps)
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (blkPl_297).base
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (tlb_PolyEncoderGuardedEnvOf maxOps) (tlb_PolyEncoderGuardedEnvOf maxOps))) :=
  e2p297_tlb_polyEncoderMerge_cro_placed_tight_ok_of_bounds hOps (by decide) (Nat.le_refl _)
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall

/-- Guarded-tight contract `tlb_PolyEncoderMergePlacedTightOkOf` (`35 ≤ maxOps`) on
`libsignalSessionLib.blockProgram lsmpl 297`. -/
theorem e2p297_tlb_polyEncoderMerge_placed_ok_tight_of [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    {maxOps : Nat} (hOps : 35 ≤ maxOps)
    (hFromCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 621) (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    tlb_PolyEncoderMergePlacedTightOkOf A lim maxOps ext := by
  have hprog :
      ((blkPC_297).rebase (blkPl_297).base (Rust.withPanics ext)) =
        libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext) :=
    (inferInstance :
      IsLsBlockProg ((blkPC_297).rebase (blkPl_297).base (Rust.withPanics ext))
        297 (Rust.withPanics ext)).eq_blockProgram
  exact e2p297_rebase_to_blockProgram (j := 297)
    (e2p297_tlb_polyEncoderMerge_cro_placed_tight_ok_of hOps
      (hprog.symm ▸ hFromCall) (hprog.symm ▸ hPushCall) (hprog.symm ▸ hVarintCall)
      (hprog.symm ▸ hSkipCall) (hprog.symm ▸ hBytesCall) (hprog.symm ▸ hGrowCall))

/-- Default `35`-op guarded-tight contract `tlb_PolyEncoderMergePlacedTightOk` on Block `297`. -/
theorem e2p297_tlb_polyEncoderMerge_placed_ok_tight [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 621) (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    tlb_PolyEncoderMergePlacedTightOk A lim ext :=
  e2p297_tlb_polyEncoderMerge_placed_ok_tight_of (Nat.le_refl 35)
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall

/-- Parametric guarded-tight contract for Block `297` (`PolynomialEncoder::merge`) on
`e2p297_polyEncoderMergeZeroCapSpecOfEnv` (`35 ≤ maxOps`, `334823 ≤ cumCap`, `2560 ≤ maxReq`). -/
theorem e2p297_polyEncoderMerge_cro_placed_tight_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {maxOps cumCap maxReq : Nat}
    (hOps : 35 ≤ maxOps) (hCum : 334823 ≤ cumCap) (hReq : 2560 ≤ maxReq)
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (blkPl_297).base
      (withLsCodeRoLoaded lsmpl
        (e2p297_polyEncoderMergeZeroCapSpecOfEnv A lim tlb_PolyEncoderDom
          (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq)
          (e2p297_PolyEncoderGuardedEnvOf maxOps cumCap maxReq))) := by
  refine subroutine_ok_mono
    (e2p297_tlb_polyEncoderMerge_cro_placed_tight_ok_of_bounds hOps hCum hReq
      hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall)
    (fun ⟨x, st⟩ R s0 hp => ?_)
    (fun _ _ _ _ hq => hq)
  obtain ⟨hcro, hp⟩ := extract_withLsCodeRoLoaded hp
  dsimp only [withLsCodeRoLoaded, e2p297_polyEncoderMergeZeroCapSpecOfEnv,
    tlb_polyEncoderMergeTightSpecOfEnv] at hp ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hcro, ?_⟩
  exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
    (e2p297_domAt_entails_tlb_domHeap A.repAlloc x)))) hp

/-- Guarded-tight contract for Block `297` (`PolynomialEncoder::merge`) on
`e2p297_polyEncoderMergeZeroCapSpecOfEnv` at `tlb_PolyEncoderGuardedEnvOf maxOps` (`35 ≤ maxOps`). -/
theorem e2p297_polyEncoderMerge_cro_placed_tight_ok_of [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {maxOps : Nat}
    (hOps : 35 ≤ maxOps)
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (blkPl_297).base
      (withLsCodeRoLoaded lsmpl
        (e2p297_polyEncoderMergeZeroCapSpecOfEnv A lim tlb_PolyEncoderDom
          (tlb_PolyEncoderGuardedEnvOf maxOps) (tlb_PolyEncoderGuardedEnvOf maxOps))) :=
  e2p297_polyEncoderMerge_cro_placed_tight_ok_of_contracts hOps (by decide) (Nat.le_refl _)
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall

/-- Parametric `blockProgram` contract `e2p297_PolyEncoderMergePlacedTightOkOf` for Block `297` (`PolynomialEncoder::merge`). -/
theorem e2p297_polyEncoderMerge_blockProgram_tight_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {maxOps cumCap maxReq : Nat}
    (hOps : 35 ≤ maxOps) (hCum : 334823 ≤ cumCap) (hReq : 2560 ≤ maxReq)
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base (Rust.withPanics ext))
      (lsmpl.base 621) (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    e2p297_PolyEncoderMergePlacedTightOkOf A lim maxOps cumCap maxReq ext :=
  e2p297_rebase_to_blockProgram (j := 297)
    (e2p297_polyEncoderMerge_cro_placed_tight_ok_of_contracts hOps hCum hReq
      hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightP297PlacedBudget
