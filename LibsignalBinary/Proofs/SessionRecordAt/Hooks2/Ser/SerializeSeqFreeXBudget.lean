/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.RecordSerializeExtBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodySomeX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneSeqFreeXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExtBudget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1ExtBudget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBudget

/-!
# Exact-Envelope (`RecordSerializeSeqFreeEnv`) `SessionRecord::serialize` (Block `52`)

Verifies `SessionRecord::serialize` (Block `52`) under the exact allocation envelope
`RecordSerializeSeqFreeEnv` (`SerializeSomeSeqFreeEnv`), pairing `SessionCloneSegPlacedOkX` with the
pre-reserved zero-allocation Block `14` contract `EncodeRawPreallocPlacedOkX`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeSeqFreeXBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded IsLsBlockProg
  lsmpl withLsCodeLoaded withLsCl extract_withLsCodeLoaded sepWP_seq_lscl
  lsρ lsRustAllocSym lsRustNoAllocShimSym lsMemcpySym
)
open CryptoVerification.RustHeap (vecAt vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalPublicApiRepr (sessionStateReprAt sessionRecordAt)
open CryptoVerification.LibsignalTripleRatchet (ls_subroutine_ok_cl_of_callee)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost okTagVec sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost)
open CryptoVerification.E2E.Record (lenField encodeRecord)
open CryptoVerification.E2E.Record.Placed (lsProg_52 blkPl_52 blkLib_eq_52 blkPl_80)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open CryptoVerification.E2E.Record.Serialization (
  encCurMem encSessionMem encRecordMem encRecordMem_eq_of_canon CanonRecord
  SessionCloneGhost EncodeRawGhost SerializeGhost
)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux (
  subroutine_ok_withLsCodeLoaded_frame_weaken
  subroutine_ok_withLsCl_of_withLsCodeLoaded
  sessionAt_unpack_head_tail sessionAt_pack_head_tail repack_frame_368
  bytes336_to_w012 lenField_one_bounds sessionAt_entails_sessionStateAt
  cells_12_pack serialize_varintLen_eq serialize_varintLen_bvShift_eq lenField_one_bv_eq
)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX (
  SerializeSomeGhostX serializeSubStackX stackAt_serializeSub_splitX
  subroutine_ok_withLsCodeLoaded_of_withLsCl
  prevVecFrameX vecAt_empty_splitX
  sepWP_exists_left_sepX sepWP_pure_left_sepX vecU8_from_out_cellsX
  sessionAt_pack_776X sessionAt_unpack_800X memRegion_out32_stack_someX
  repack_stack_some_cellsX memRegion_split_init_byteX vecU8At_unpack_cells_432X
  lenField_one_bv_toNatX cap_lt_not_noneCapX bv64_ult_zeroX lenField_one_branch_condsX
  vecU8At_init_byte_432X lenField_one_cons_eqX
)
open LibsignalBinary.Heap (
  VmPreserved AllocCallPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  RustLayoutOk FitsEvents FitsEnv SeqEnv FreeOnlyEvs rustAllocEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (
  EncodeVarintEnv encodeVarintEvents_of_spare
)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit (
  SerializeSomeSeqFreeEnv RecordSerializeSeqFreeEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (
  EncodeRawPreallocPlacedOkX encodeRawPreallocSubSpecX encodeRawPrealloc_placed_sub_clX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DefsBudget (
  subroutine_ok_withLsCodeLoaded_map_oom'
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExtBudget (do_reserve_placed_ok_ext_x)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1ExtBudget (
  drop_session_structure_local1_placed_ok_ext
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  sessionCloneStackX serializeStackX SerContractsXPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  DoReservePlacedOkX EncodeVarintPlacedOkX DropSessionStructureLocal1PlacedOkX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneSeqFreeXBudget (
  sessionCloneSegSpecX SessionCloneSegPlacedOkX sessionClone_seg_placed_ok_ext
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget (
  vecVecCloneSubSpecX sessionLenSubSpecX
  encodeVarintSubSpecX dropLocal1SubSpecX
  rustAllocNoOomSubSpecX shimSubSpecX memcpySubSpecX
  vecVecClone_placed_sub_clX sessionLen_placed_sub_clX
  encodeVarint_placed_sub_clX dropLocal1_placed_sub_clX
  allocNoOom_placed_sub_clX shim_placed_sub_clX memcpy_placed_sub_clX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneXBudget (
  serializeNoneSpecX serialize_none_placed_okX
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBudget (
  encode_varint_placed_ok_of_doReserve_x
)

private theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

private theorem memRegion_eq_of_len {p : BitVec 64} {n : Nat} {bs : List (BitVec 8)}
    (h : bs.length = n) : memRegion p n = memRegion p bs.length := by
  rw [h]

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv64_ult_zeroX
attribute [local wp_norm] serialize_varintLen_eq serialize_varintLen_bvShift_eq lenField_one_bv_eq bv64_ult_zeroX
attribute [local simp] bv64_ult_zeroX

/-! ## `SessionCloneSeg` sub-spec and `SerializeSeqFree` specifications -/

def sessionCloneSegSubSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SessionCloneGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧
      FitsEnv M lim st (SegCloneEnv x.G x.s.state)⌝ ∗
      sessionStateReprAt A.repAlloc x.src x.G x.s ∗ memRegion x.dst 344 ∗
      A.pool lim st s ∗ stackAt s.sp serializeSubStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ SegCloneEnv x.G x.s.state evs⌝ ∗
      sessionStateReprAt A.repAlloc x.src x.G x.s ∗
      (∃∗ G' : SessionGhost, ⌜encSessionMem G' x.s = encSessionMem x.G x.s⌝ ∗
        sessionStateReprAt A.repAlloc x.dst G' x.s) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeSubStackX

theorem sessionCloneSeg_placed_sub_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hClone : SessionCloneSegPlacedOkX M A lim H) :
    subroutine_ok callerProg (blkPl_80).base
      (withLsCodeLoaded lsmpl (sessionCloneSegSubSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - sessionCloneStackX))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl
      (ls_subroutine_ok_cl_of_callee (callerProg := callerProg) hClone))
    (fun ⟨x, st⟩ s0 => ?_)
    (fun ⟨x, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [sessionCloneSegSubSpecX, sessionCloneSegSpecX,
      stackAt_serializeSub_splitX s0.sp sessionCloneStackX (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [sessionCloneSegSubSpecX, sessionCloneSegSpecX]
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_mono fun evs => ?_
    rw [stackAt_serializeSub_splitX s0.sp sessionCloneStackX (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem sessionCloneSeg_placed_sub_clX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hClone : SessionCloneSegPlacedOkX M A lim H) :
    subroutine_ok callerProg (blkPl_80).base
      (withLsCl lsmpl (sessionCloneSegSubSpecX M A lim)) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded (sessionCloneSeg_placed_sub_okX hClone)

/-- Budget-threaded specification of `SessionRecord::serialize` on a record with a current session
    under `FitsEnv M lim st (SerializeSomeSeqFreeEnv x.G x.sess)`. -/
def serializeSomeSeqFreeSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SerializeSomeGhostX × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧
      (lenField 1 (encSessionMem x.G x.sess)).length < 2 ^ 32 ∧
      FitsEnv M lim st (SerializeSomeSeqFreeEnv x.G x.sess)⌝ ∗
      ((x.self + 8#64) ↦₆₄ x.prevPtr) ∗ ((x.self + 16#64) ↦₆₄ 0#64) ∗
      sessionStateReprAt A.repAlloc (x.self + 24#64) x.G x.sess ∗
      A.pool lim st s ∗ memRegion x.out 32 ∗ stackAt s.sp serializeStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ SerializeSomeSeqFreeEnv x.G x.sess evs⌝ ∗
      ((x.self + 8#64) ↦₆₄ x.prevPtr) ∗ ((x.self + 16#64) ↦₆₄ 0#64) ∗
      sessionStateReprAt A.repAlloc (x.self + 24#64) x.G x.sess ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A.repAlloc (x.out + 8#64) (lenField 1 (encSessionMem x.G x.sess)) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeStackX

/-- Budget-threaded memory-level `serializeSpec` at `serializeStackX` using
`RecordSerializeSeqFreeEnv`. -/
def serializeSeqFreeSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SerializeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧
      (encRecordMem x.g x.r).length < 2 ^ 32 ∧
      FitsEnv M lim st (RecordSerializeSeqFreeEnv x.g x.r)⌝ ∗
      sessionRecordAt A.repAlloc x.self x.g x.r ∗ memRegion x.out 32 ∗
      A.pool lim st s ∗ stackAt s.sp serializeStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ RecordSerializeSeqFreeEnv x.g x.r evs⌝ ∗
      sessionRecordAt A.repAlloc x.self x.g x.r ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A.repAlloc (x.out + 8#64) (encRecordMem x.g x.r) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeStackX

/-- Budget-threaded canonical `serializeCanonSpec` at `serializeStackX` using
`RecordSerializeSeqFreeEnv`. -/
def serializeCanonSeqFreeSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SerializeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧ CanonRecord x.g x.r ∧
      (encodeRecord x.r).length < 2 ^ 32 ∧
      FitsEnv M lim st (RecordSerializeSeqFreeEnv x.g x.r)⌝ ∗
      sessionRecordAt A.repAlloc x.self x.g x.r ∗ memRegion x.out 32 ∗
      A.pool lim st s ∗ stackAt s.sp serializeStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ RecordSerializeSeqFreeEnv x.g x.r evs⌝ ∗
      sessionRecordAt A.repAlloc x.self x.g x.r ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A.repAlloc (x.out + 8#64) (encodeRecord x.r) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeStackX

/-! ## `SerializeSomeSeqFreeEnv` per-call projections and reassembly -/

private theorem fitsEnv_segClone_of_someSeqFree {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {G : SessionGhost} {sess : Session (List (BitVec 8))}
    (hFit : FitsEnv M lim st (SerializeSomeSeqFreeEnv G sess)) :
    FitsEnv M lim st (SegCloneEnv G sess.state) :=
  hFit.seq_left

private theorem fitsEvents_alloc_of_someSeqFree {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {evs1 : List AllocEvent}
    (hFit : FitsEnv M lim st (SerializeSomeSeqFreeEnv G sess))
    (h1 : SegCloneEnv G sess.state evs1) :
    FitsEvents M lim (M.stepEvents evs1 st)
      (rustAllocEvents (lenField 1 (encSessionMem G sess)).length 1) :=
  ((hFit.seq_right h1).seq_left) _ rfl

private theorem encodeVarint_spare_lenField_one (G : SessionGhost)
    (sess : Session (List (BitVec 8)))
    (hlt : (lenField 1 (encSessionMem G sess)).length < 2 ^ 32) :
    ([0x0a#8] : List (BitVec 8)).length +
      (encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length ≤
      (BitVec.ofNat 64 (lenField 1 (encSessionMem G sess)).length).toNat := by
  rw [lenField_one_bv_toNatX hlt, ← lenField_one_cons_eqX (rfl : encSessionMem G sess = _)]
  simp only [List.length_cons, List.length_nil, List.length_append]
  omega

private theorem fitsEnv_encodeVarint_of_spare {M : AllocCostModel} {lim : BudgetLimits}
    (st : M.σ) (x : EncodeVarintGhost)
    (hspare : x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat) :
    FitsEnv M lim st (EncodeVarintEnv x) := by
  intro evs hevs
  rw [hevs, encodeVarintEvents_of_spare hspare]
  trivial

private theorem eq_nil_of_encodeVarintEnv {x : EncodeVarintGhost} {evs : List AllocEvent}
    (hspare : x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat)
    (hevs : EncodeVarintEnv x evs) : evs = [] :=
  hevs.trans (encodeVarintEvents_of_spare hspare)

private theorem encodeRaw_spare_lenField_one {G w : SessionGhost}
    {sess : Session (List (BitVec 8))}
    (heq : encSessionMem w sess = encSessionMem G sess)
    (hlt : (lenField 1 (encSessionMem G sess)).length < 2 ^ 32) :
    ([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length +
      (encSessionMem w sess).length ≤
      (BitVec.ofNat 64 (lenField 1 (encSessionMem G sess)).length).toNat := by
  rw [lenField_one_bv_toNatX hlt]
  have hcons := congrArg List.length (lenField_one_cons_eqX heq)
  simp only [List.length_cons, List.length_nil, List.length_append] at hcons ⊢
  omega

private theorem serializeSomeSeqFreeEnv_of_parts
    {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {evs1 evsDrop : List AllocEvent}
    (h1 : SegCloneEnv G sess.state evs1)
    (hDrop : FreeOnlyEvs evsDrop) :
    SerializeSomeSeqFreeEnv G sess
      (evs1 ++ rustAllocEvents (lenField 1 (encSessionMem G sess)).length 1 ++ evsDrop) := by
  rw [List.append_assoc]
  exact SeqEnv.append h1 (SeqEnv.append rfl hDrop)

/-! ## Relocatable `[LibsignalPlacement]` proofs (Block `52`) -/

section Placed

attribute [local irreducible] encSessionMem sessionStateReprAt sessionStateAt FitsEvents FitsEnv

local macro "wp_seg_sync " hseg:ident mid:term : tactic =>
  `(tactic| (
    apply ($hseg:ident (mid := $mid))
    intro _m_strip
    wp_steps
    refine SepWP.done
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; assumption)
      fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [arm64_norm]))
      (hnext := ?_)
    clear _hnsp
    try clear _m_strip))

local macro "wp_done_call " hcl:ident : tactic =>
  `(tactic| (
    apply SepWP.done
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; assumption)
    intro $hcl:ident
    simp only [arm64_norm] at $hcl:ident))

set_option maxHeartbeats 800000 in
theorem serialize_some_seqFree_placed_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hClone : SessionCloneSegPlacedOkX M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializeSomeSeqFreeSpecX M A lim)) := by
  have hmemcpy := memcpy_placed_sub_clX (callerProg := lsProg_52 H) hC
  have hshim := shim_placed_sub_clX (callerProg := lsProg_52 H) hC
  have halloc := allocNoOom_placed_sub_clX (callerProg := lsProg_52 H) hC
  have hclone := sessionCloneSeg_placed_sub_clX (callerProg := lsProg_52 H) hClone
  have hvv := vecVecClone_placed_sub_clX (callerProg := lsProg_52 H)
  have hlen := sessionLen_placed_sub_clX A.repAlloc (callerProg := lsProg_52 H)
  have hev := encodeVarint_placed_sub_clX (callerProg := lsProg_52 H) hEV
  have hraw := encodeRawPrealloc_placed_sub_clX (callerProg := lsProg_52 H) hRaw
  have hdrop := dropLocal1_placed_sub_clX (callerProg := lsProg_52 H) hDrop
  change subroutine_ok (lsProg_52 H) (lsρ lsMemcpySym) (withLsCl lsmpl memcpySubSpecX) at hmemcpy
  change subroutine_ok (lsProg_52 H) (lsρ lsRustNoAllocShimSym) (withLsCl lsmpl shimSubSpecX) at hshim
  change subroutine_ok (lsProg_52 H) (lsρ lsRustAllocSym)
    (withLsCl lsmpl (rustAllocNoOomSubSpecX M A lim)) at halloc
  change subroutine_ok (lsProg_52 H) (lsmpl.base 80)
    (withLsCl lsmpl (sessionCloneSegSubSpecX M A lim)) at hclone
  change subroutine_ok (lsProg_52 H) (lsmpl.base 117)
    (withLsCl lsmpl vecVecCloneSubSpecX) at hvv
  change subroutine_ok (lsProg_52 H) (lsmpl.base 86)
    (withLsCl lsmpl (sessionLenSubSpecX A.repAlloc)) at hlen
  change subroutine_ok (lsProg_52 H) (lsmpl.base 10)
    (withLsCl lsmpl (encodeVarintSubSpecX M A lim)) at hev
  change subroutine_ok (lsProg_52 H) (lsmpl.base 14)
    (withLsCl lsmpl (encodeRawPreallocSubSpecX A.repAlloc)) at hraw
  change subroutine_ok (lsProg_52 H) (lsmpl.base 6)
    (withLsCl lsmpl (dropLocal1SubSpecX M A lim)) at hdrop
  dsimp only [withLsCl, memcpySubSpecX, shimSubSpecX, rustAllocNoOomSubSpecX,
    sessionCloneSegSubSpecX, vecVecCloneSubSpecX, sessionLenSubSpecX,
    encodeVarintSubSpecX, encodeRawPreallocSubSpecX, dropLocal1SubSpecX]
    at hmemcpy hshim halloc hclone hvv hlen hev hraw hdrop
  unfold withLsCodeLoaded serializeSomeSeqFreeSpecX
  simp only [okTagVec, memRegion_out32_stack_someX,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init x s0
  obtain ⟨⟨self, out, prevPtr, G, sess⟩, st⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_bounds_G : (lenField 1 (encSessionMem G sess)).length < 2 ^ 32 := by assumption
  have hFit0 : FitsEnv M lim st (SerializeSomeSeqFreeEnv G sess) := by assumption
  have hseg52 := fun {mid target : BitVec 64} {s : State} {Pre : SepProp}
      {post : State → SepProp → Prop} {oom : State → SepProp} =>
    sepWP_seg_ls_vm (prog := lsProg_52 H) (Q := lsProg_52 (hooksException H))
      blkLib_eq_52 (by rfl) (mid := mid) (target := target) (s := s) (Pre := Pre)
      (post := post) (oom := oom)
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 80)
  refine SepWP.fold (sessionAt_unpack_head_tail A.repAlloc (self + 24#64) G sess) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro bs336_self
  apply sepWP_pure_left_sepX; rintro ⟨hbs336_self, hcap_self, hinl_self⟩
  have hcmn_self : (G.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCapX hcap_self
  wp_seg_sync hseg52 (lsmpl.base 80)
  refine SepWP.fold (sessionAt_pack_head_tail A.repAlloc (self + 24#64) G sess hinl_self) (by sep_frame) ?_
  wp_done_call hcl1
  have hFit_clone := fitsEnv_segClone_of_someSeqFree hFit0
  wp_call hclone (⟨s0.sp - 800#64, self + 24#64, G, sess⟩, st)
  have h1_env : SegCloneEnv G sess.state w := by assumption
  have heq_enc : encSessionMem w_1 sess = encSessionMem G sess := by assumption
  have heq_encF : ∀ s', s' = sess → encSessionMem w_1 s' = encSessionMem G s' :=
    fun _ h => h ▸ heq_enc
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsMemcpySym); · assumption
  refine SepWP.fold (sessionAt_unpack_800X A.repAlloc s0.sp w_1 sess) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro bs336_clone
  apply sepWP_pure_left_sepX; rintro ⟨hbs336_clone, hcap_clone, hinl_clone⟩
  have hcmn_clone : (w_1.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCapX hcap_clone
  wp_seg_sync hseg52 (lsρ lsMemcpySym)
  wp_done_call hcl2
  rw [memRegion_eq_of_len hbs336_clone]
  wp_call hmemcpy (s0.sp - 432#64, s0.sp - 792#64, bs336_clone)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_1› (hnext := ?_)
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 117); · assumption
  refine SepWP.fold (repack_frame_368 s0.sp w_1.localIk.cap hbs336_clone) (by sep_frame) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro w_none
  wp_seg_sync hseg52 (lsmpl.base 117)
  wp_done_call hcl3
  wp_call hvv ⟨s0.sp - 800#64, prevPtr⟩
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsMemcpySym); · assumption
  wp_simp_pre [vecHeader, arm64_norm]
  wp_seg_sync hseg52 (lsρ lsMemcpySym)
  wp_done_call hcl4
  rw [memRegion_eq_of_len hbs336_clone]
  wp_call hmemcpy (s0.sp - 768#64, s0.sp - 432#64, bs336_clone)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_3› (hnext := ?_)
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 86); · assumption
  refine SepWP.fold (sessionAt_pack_776X A.repAlloc s0.sp w_1 sess hinl_clone) (by sep_frame) ?_
  refine SepWP.fold (bytes336_to_w012 s0.sp hbs336_clone) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro w0
  apply sepWP_exists_left_sepX; intro w1
  apply sepWP_exists_left_sepX; intro w2
  wp_seg_sync hseg52 (lsmpl.base 86)
  obtain ⟨hbs_lt_G, hlf_pos_G, hlf_lt63_G, hlayout_G, hv_lt62_G, hv_le_lf_G, hraw_lt_G⟩ :=
    lenField_one_bounds hlen_bounds_G
  obtain ⟨hbr_ls_G, hbr_tbz_G, hbr_cbz_G⟩ := lenField_one_branch_condsX hlen_bounds_G
  have hcap_toNat_G := lenField_one_bv_toNatX hlen_bounds_G
  have hbs_lt_w : (encSessionMem w_1 sess).length < 2 ^ 32 := by rw [heq_enc]; exact hbs_lt_G
  wp_done_call hcl5
  wp_call hlen ⟨s0.sp - 776#64, w_1, sess⟩
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_4› (hnext := ?_)
  simp only [heq_enc] at *
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsRustNoAllocShimSym); · assumption
  wp_seg_sync hseg52 (lsρ lsRustNoAllocShimSym)
  wp_done_call hcl6
  wp_call hshim ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_5› (hnext := ?_)
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsRustAllocSym); · assumption
  wp_seg_sync hseg52 (lsρ lsRustAllocSym)
  wp_done_call hcl7
  simp only [Bool.false_eq_true, ↓reduceIte] at halloc
  have hex_pow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hsz_pos : 0 < (lenField 1 (encSessionMem G sess)).length := by omega
  have hsz_le : (lenField 1 (encSessionMem G sess)).length + 1 ≤ 2 ^ 63 := by omega
  have hrlay : RustLayoutOk (lenField 1 (encSessionMem G sess)).length 1 :=
    ⟨⟨hsz_pos, hex_pow, hsz_le⟩, by decide⟩
  have hFit_alloc := fitsEvents_alloc_of_someSeqFree hFit0 h1_env
  wp_call halloc ((lenField 1 (encSessionMem G sess)).length, 1, M.stepEvents w st)
  have htr_sf6 := (‹AllocCallPreserved _ sf_6›).2.1
  have hp0_ne : sf_6.readReg64 Reg.x0 ≠ 0#64 := by assumption
  have hp0' : sf_6.readReg64 (Reg.gpr 0#5) ≠ 0 := hp0_ne
  have hp0_beq : (sf_6.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hp0_ne
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 86); · assumption
  rw [memRegion_split_init_byteX (sf_6.readReg64 (Reg.gpr 0#5)) hlf_pos_G hlf_lt63_G]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro b0
  wp_seg_sync hseg52 (lsmpl.base 86)
  wp_done_call hcl8
  have hbs_lt_w2 : (encSessionMem w_1 sess).length < 2 ^ 32 := by rw [heq_encF sess rfl]; exact hbs_lt_G
  wp_call hlen ⟨s0.sp - 776#64, w_1, sess⟩
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_7› (hnext := ?_)
  try simp only [heq_encF sess rfl] at *
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 10); · assumption
  wp_seg_sync hseg52 (lsmpl.base 10)
  have hvinit := vecU8At_init_byte_432X A.repAlloc s0.sp (sf_6.readReg64 (Reg.gpr 0#5))
    (lenField 1 (encSessionMem G sess)).length 0x0a#8 hlf_pos_G hlen_bounds_G hp0'
  rw [A.repAlloc_live_norm] at hvinit
  refine SepWP.fold hvinit (by sep_frame) ?_
  wp_done_call hcl9
  have hspare_ev := encodeVarint_spare_lenField_one G sess hlen_bounds_G
  let evGhost : EncodeVarintGhost :=
    ⟨BitVec.ofNat 64 (encSessionMem G sess).length, s0.sp - 432#64,
      BitVec.ofNat 64 (lenField 1 (encSessionMem G sess)).length,
      sf_6.readReg64 (Reg.gpr 0#5), [0x0a#8]⟩
  have hFit_ev : FitsEnv M lim
      (M.stepEvents (rustAllocEvents (lenField 1 (encSessionMem G sess)).length 1) (M.stepEvents w st))
      (EncodeVarintEnv evGhost) :=
    fitsEnv_encodeVarint_of_spare _ evGhost hspare_ev
  wp_call hev (evGhost,
    M.stepEvents (rustAllocEvents (lenField 1 (encSessionMem G sess)).length 1) (M.stepEvents w st))
  have hevs_ev_nil : _ = ([] : List AllocEvent) :=
    eq_nil_of_encodeVarintEnv (x := evGhost) hspare_ev (by assumption)
  rw [hevs_ev_nil] at *
  simp only [AllocCostModel.stepEvents_nil] at *
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 14); · assumption
  wp_seg_sync hseg52 (lsmpl.base 14)
  wp_done_call hcl10
  have hraw_spare_w :
      ([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length +
        (encSessionMem w_1 sess).length ≤
        (BitVec.ofNat 64 (lenField 1 (encSessionMem G sess)).length).toNat :=
    encodeRaw_spare_lenField_one (heq_encF sess rfl) hlen_bounds_G
  have hraw_lt_w :
      ([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length +
        (encSessionMem w_1 sess).length < 2 ^ 32 := by
    rw [heq_encF sess rfl]; exact hraw_lt_G
  let rawGhost : EncodeRawGhost :=
    ⟨s0.sp - 776#64, w_1, sess, s0.sp - 432#64,
      BitVec.ofNat 64 (lenField 1 (encSessionMem G sess)).length,
      w_4, [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)⟩
  have hw3_eq : w_3 = BitVec.ofNat 64 (lenField 1 (encSessionMem G sess)).length := by
    have hsp1 := hspare_ev
    have hsp2 : 1 + (encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length ≤
        (lenField 1 (encSessionMem G sess)).length := by
      simpa only [List.length_cons, List.length_nil, hcap_toNat_G] using hspare_ev
    dsimp only [evGhost, List.length_cons, List.length_nil] at *
    tauto
  rw [hw3_eq]
  wp_call hraw rawGhost
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 6); · assumption
  conv => arg 4; dsimp only [rawGhost]; simp only [List.cons_append, List.nil_append]
  rw [lenField_one_cons_eqX (heq_encF sess rfl), vecU8At_unpack_cells_432X]
  wp_seg_sync hseg52 (lsmpl.base 6)
  refine SepWP.fold (sessionAt_entails_sessionStateAt A.repAlloc (s0.sp - 776#64) w_1 sess)
    (by sep_frame) ?_
  wp_done_call hcl11
  wp_call hdrop (⟨s0.sp - 776#64, w_1, sess.state⟩,
    M.stepEvents (rustAllocEvents (lenField 1 (encSessionMem G sess)).length 1) (M.stepEvents w st))
  wp_steps_sync_pool (s0.readReg64 .lr)
  refine SepWP.fold
    (vecU8_from_out_cellsX A.repAlloc out _ _ (lenField 1 (encSessionMem G sess)))
    (by sep_frame) ?_
  refine SepWP.fold (cells_12_pack s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_frame) ?_
  conv => arg 4; conv in (stackAt _ _) => arg 1; simp only [arm64_norm, *]
  refine SepWP.fold (repack_stack_some_cellsX s0.sp _ _ _) (by sep_frame) ?_
  conv => arg 4; simp only [← AllocCostModel.stepEvents_append]
  have hEnv_final := serializeSomeSeqFreeEnv_of_parts h1_env (by assumption)
  simp only [List.append_assoc] at hEnv_final
  wp_done

private theorem pack_withLsCodeLoaded_seqFree {pl : MultiPlacement} {α : Type} {S : Spec α}
    {x : α} {s0 : State} {R : SepProp}
    (hcl : LibsignalCodeLoaded pl s0.mem)
    (hp : s0.mem ⊨ S.pre x s0 ∗ R) :
    s0.mem ⊨ (withLsCodeLoaded pl S).pre x s0 ∗ R := by
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm _ ⌜LibsignalCodeLoaded pl s0.mem⌝, satisfies_pure_sepConj]
  exact ⟨hcl, hp⟩

/-- Relocatable `[LibsignalPlacement]` `RecordSerializeSeqFreeEnv`-threaded
`SessionRecord::serialize` (`None`/`Some` split on `lsProg_52 H`). -/
theorem serialize_seqFree_placed_ok_of_leaves_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hClone : SessionCloneSegPlacedOkX M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializeSeqFreeSpecX M A lim)) := by
  have hnone := serialize_none_placed_okX (M := M) (A := A) (lim := lim) hC
  have hsome := serialize_some_seqFree_placed_okX hC hClone hEV hRaw hDrop
  apply subroutine_ok_outcome_intro
  rintro ⟨x, st⟩ R s0 hpc hrun hpre0 hsp
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre0
  rcases hcur_g : x.g.cur with _ | G <;> rcases hcur_r : x.r.currentSession with _ | sess
  ·
    have henc : encRecordMem x.g x.r = [] := by
      simp [encRecordMem, encCurMem, hcur_g, hcur_r]
    have henv_nil : RecordSerializeSeqFreeEnv x.g x.r [] := by
      simp [RecordSerializeSeqFreeEnv, hcur_g, hcur_r]
    let F := prevVecFrameX A.repAlloc x.self x.g ∗ memRegion (x.self + 32#64) 336
    have hpre' : s0.mem ⊨
        (withLsCodeLoaded lsmpl (serializeNoneSpecX M A lim)).pre
          ((x.self, x.out, x.g.prevPtr), st) s0 ∗ (F ∗ R) := by
      refine pack_withLsCodeLoaded_seqFree hcl0 ?_
      simp only [serializeSeqFreeSpecX, serializeNoneSpecX, sessionRecordAt, hcur_g,
        hcur_r, vecAt_empty_splitX, F, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      refine ⟨⟨hpre.1.1, hpre.1.2.1⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre.2
    refine hnone.mono_outcome ((x.self, x.out, x.g.prevPtr), st) (F ∗ R) s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨h1, h2, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
    · refine Or.inl ⟨h1, h2, ?_⟩
      dsimp only [withLsCodeLoaded] at hpost ⊢
      simp only [serializeSeqFreeSpecX, serializeNoneSpecX, sessionRecordAt, hcur_g,
        hcur_r, henc, vecAt_empty_splitX, F, sepExists_sepConj_left,
        satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      refine ⟨[], ⟨hpost.1, henv_nil⟩, ?_⟩
      simp only [AllocCostModel.stepEvents_nil]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost.2
    · exact False.elim (not_satisfies_false_sepConj hpan)
    · exact False.elim (not_satisfies_false_sepConj hex)
    · exact False.elim (not_satisfies_false_sepConj hoom)
  ·
    simp only [serializeSeqFreeSpecX, sessionRecordAt, hcur_g, hcur_r,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_comm (vecAt A.repAlloc 24 8 (fun _ _ => emp) x.self x.g.prevCap x.g.prevPtr []),
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact False.elim hpre.2.1
  ·
    simp only [serializeSeqFreeSpecX, sessionRecordAt, hcur_g, hcur_r,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_comm (vecAt A.repAlloc 24 8 (fun _ _ => emp) x.self x.g.prevCap x.g.prevPtr []),
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact False.elim hpre.2.1
  ·
    have henc : encRecordMem x.g x.r = lenField 1 (encSessionMem G sess) := by
      simp [encRecordMem, encCurMem, hcur_g, hcur_r]
    have henv_eq : RecordSerializeSeqFreeEnv x.g x.r = SerializeSomeSeqFreeEnv G sess := by
      simp [RecordSerializeSeqFreeEnv, hcur_g, hcur_r]
    let F := prevVecFrameX A.repAlloc x.self x.g
    have hpre' : s0.mem ⊨
        (withLsCodeLoaded lsmpl (serializeSomeSeqFreeSpecX M A lim)).pre
          (⟨x.self, x.out, x.g.prevPtr, G, sess⟩, st) s0 ∗ (F ∗ R) := by
      refine pack_withLsCodeLoaded_seqFree hcl0 ?_
      simp only [serializeSeqFreeSpecX, serializeSomeSeqFreeSpecX, sessionRecordAt, hcur_g,
        hcur_r, henc, vecAt_empty_splitX, F, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      have hFit_some : FitsEnv M lim st (SerializeSomeSeqFreeEnv G sess) := by
        rw [← henv_eq]
        exact hpre.1.2.2.2
      refine ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1, hFit_some⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre.2
    refine hsome.mono_outcome (⟨x.self, x.out, x.g.prevPtr, G, sess⟩, st) (F ∗ R) s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨h1, h2, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
    · refine Or.inl ⟨h1, h2, ?_⟩
      dsimp only [withLsCodeLoaded] at hpost ⊢
      simp only [serializeSeqFreeSpecX, serializeSomeSeqFreeSpecX, sessionRecordAt, hcur_g,
        hcur_r, henc, vecAt_empty_splitX, F, sepExists_sepConj_left,
        satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨evs, ⟨htr, henv⟩, hmem⟩
      refine ⟨evs, ⟨htr, ?_⟩, ?_⟩
      · rwa [henv_eq]
      · exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    · exact False.elim (not_satisfies_false_sepConj hpan)
    · exact False.elim (not_satisfies_false_sepConj hex)
    · exact False.elim (not_satisfies_false_sepConj hoom)

/-- Relocatable `withLsCodeLoaded` bridge from `serializeSeqFreeSpecX M A lim` to
`serializeCanonSeqFreeSpecX M A lim`. -/
theorem serializeCanonSeqFree_of_serializeSeqFree_placedX {pl : MultiPlacement}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (serializeSeqFreeSpecX M A lim))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (serializeCanonSeqFreeSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_map_oom' h fun ⟨x, st⟩ R s0 hpre => ?_
  dsimp only [serializeCanonSeqFreeSpecX] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨h0, h8, hcanon, hlen, hfit⟩, hrest⟩
  have henc := encRecordMem_eq_of_canon x.g x.r hcanon
  refine ⟨(x, st), R, ?_, ?_, fun _ ho => (not_satisfies_false_sepConj ho).elim⟩
  · dsimp only [serializeSeqFreeSpecX]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨h0, h8, henc ▸ hlen, hfit⟩, hrest⟩
  · intro sf hq
    have hpost_eq :
        (serializeSeqFreeSpecX M A lim).post (x, st) s0 sf =
          (serializeCanonSeqFreeSpecX M A lim).post (x, st) s0 sf := by
      dsimp only [serializeSeqFreeSpecX, serializeCanonSeqFreeSpecX]
      rw [henc]
    rwa [hpost_eq] at hq

/-- Relocatable `serializeSeqFreeSpecX M A lim` on Block `52` from `SerContractsXPlaced` and
`EncodeRawPreallocPlacedOkX A.repAlloc H`. -/
theorem serialize_seqFree_placed_ok_of_raw [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H) :
    subroutine_ok (lsProg_52 H) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeSeqFreeSpecX M A lim)) := by
  have hDR : DoReservePlacedOkX M A lim H := do_reserve_placed_ok_ext_x hC.alloc
  have hEV : EncodeVarintPlacedOkX M A lim H :=
    encode_varint_placed_ok_of_doReserve_x A lim H hDR
  have hClone : SessionCloneSegPlacedOkX M A lim H :=
    sessionClone_seg_placed_ok_ext hC
  have hDrop : DropSessionStructureLocal1PlacedOkX M A lim H :=
    drop_session_structure_local1_placed_ok_ext hC.alloc
  exact serialize_seqFree_placed_ok_of_leaves_ext hC hClone hEV hRaw hDrop

/-- Relocatable `serializeCanonSeqFreeSpecX M A lim` on Block `52` from `SerContractsXPlaced` and
`EncodeRawPreallocPlacedOkX A.repAlloc H`. -/
theorem serializeCanonSeqFree_placed_ok_of_raw [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H) :
    subroutine_ok (lsProg_52 H) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim)) :=
  serializeCanonSeqFree_of_serializeSeqFree_placedX
    (serialize_seqFree_placed_ok_of_raw hC hRaw)

end Placed

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeSeqFreeXBudget
