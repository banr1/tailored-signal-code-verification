/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyAPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyPlaced
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeSeqFreeXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneSeqFreeXBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneX
meta import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneX -- shake: keep
meta import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyB -- shake: keep
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Placed `SessionRecord::serialize` Body Proof (`Prev1`)

Proves the relocatable `[LibsignalPlacement]` body contract for `<SessionRecord>::serialize`
(block 52) on a record with a current session and one archived previous session (`[enc]`), under
both the bounded allocation-plus-drop envelope (`SerializePrev1EnvX`) and the pre-reserved
sequence-free envelope (`SerializePrev1Env`).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded
  lsmpl withLsCodeLoaded withLsCl sepWP_seq_lscl
  lsρ lsRustAllocSym lsRustNoAllocShimSym lsMemcpySym
)
open CryptoVerification.RustHeap (vecU8 vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalPublicApiRepr (sessionStateReprAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost okTagVec)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoVerification.E2E.Record (lenField)
open CryptoVerification.E2E.Record.Placed (lsProg_52 blkPl_52 blkLib_eq_52)
open CryptoVerification.E2E.Record.Serialization (encSessionMem EncodeRawGhost)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux (
  sessionAt_unpack_head_tail sessionAt_pack_head_tail repack_frame_368
  bytes336_to_w012 lenField_one_bounds lenField_one_length
  serialize_varintLen_eq serialize_varintLen_bvShift_eq lenField_one_bv_eq
)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX (
  sepWP_exists_left_sepX sepWP_pure_left_sepX
  sessionAt_pack_776X sessionAt_unpack_800X memRegion_out32_stack_someX
  memRegion_split_init_byteX lenField_one_bv_toNatX cap_lt_not_noneCapX
  bv64_ult_zeroX lenField_one_branch_condsX lenField_one_cons_eqX
)
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux (entails_of_sep_focus)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  prevVecAt serSavedCells encodeRecordPrev1Mem lenField_two_length
  bv64_ult_zeroK5 ult_ofNat_add_false ofNat_add_bits
)
open LibsignalBinary.Heap (
  VmPreserved AllocCallPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  RustLayoutOk FitsEvents FitsEnv SeqEnv FreeOnlyEvs fitsEvents_append rustAllocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (
  BoundedRustEvs SessionCloneEnv EncodeRawEnv
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget (EncRawSegEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (
  EncodeVarintEnv encodeVarintEvents_of_spare
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  serializeStackX SerContractsXPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  SepWPpLsCl DoReservePlacedOkX EncodeVarintPlacedOkX SessionClonePlacedOkX
  EncodeRawPlacedOkX DropSessionStructureLocal1PlacedOkX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget (
  sessionLenSubSpecX sessionCloneSubSpecX encodeVarintSubSpecX encodeRawSubSpecX
  rustAllocNoOomSubSpecX shimSubSpecX memcpySubSpecX
  sessionLen_placed_sub_clX sessionClone_placed_sub_clX encodeVarint_placed_sub_clX
  encodeRaw_placed_sub_clX allocNoOom_placed_sub_clX shim_placed_sub_clX memcpy_placed_sub_clX
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsBudget (
  VecVecClone1Ghost VecVecClone1Env vecVecClone1Env_bounded
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsPlacedBudget (
  VecVecClone1PlacedOkStmt
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsBudget (
  vecVecClone1SubSpecX
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsPlacedBudget (
  serializePrev1BodySpecWithEnvX SerializePrev1BodyPlacedOkWithEnvStmt
  SerField2Env SerField2PlacedStepStmt
  encRawSegEnv_of_serField2Env fitsEnv_serField2_of_encRawSeg vecVecClone1_placed_sub_clX
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBBudget (
  prevVecAt_one_fold_ser prevVecAt_one_pure_first prevVecAt_800_open
  memRegion_out32_pool_stack_swap vecU8At_init_byte_432_cap
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyAPlacedBudget (
  serField2_placed_step
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBPlacedBudget (
  SerPrev1PlacedTailStmt serPrev1Tail_placed_ok k5_fold_q_placed
)

private theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

private theorem memRegion_eq_of_len {p : BitVec 64} {n : Nat} {bs : List (BitVec 8)}
    (h : bs.length = n) : memRegion p n = memRegion p bs.length := by
  rw [h]

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv64_ult_zeroX bv64_ult_zeroK5
attribute [local wp_norm]
  serialize_varintLen_eq serialize_varintLen_bvShift_eq lenField_one_bv_eq
  bv64_ult_zeroX bv64_ult_zeroK5
attribute [local simp] bv64_ult_zeroX bv64_ult_zeroK5

/-! ## Allocation Envelopes -/

/-- Allocation-only prefix envelope for `SessionRecord::serialize` on a record with current
session `sess` (ghost `G`) and `previous_sessions = [enc]`. -/
def SerializePrev1AllocEnvX (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (enc : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  let recLen := (encodeRecordPrev1Mem G sess enc).length
  BoundedRustEvs (8 * recLen + 128) (256 * (recLen + 16)) evs

/-- Full allocation-and-drop envelope for `SessionRecord::serialize` with one previous session. -/
def SerializePrev1EnvX (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (enc : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (SerializePrev1AllocEnvX G sess enc) FreeOnlyEvs

private theorem len_le_lenField (tag : Nat) (bs : List (BitVec 8)) :
    bs.length ≤ (lenField tag bs).length := by
  simp only [lenField, List.length_append]
  omega

private theorem encodeRecordPrev1Mem_len_split (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (enc : List (BitVec 8)) :
    (encodeRecordPrev1Mem G sess enc).length =
      (lenField 1 (encSessionMem G sess)).length + (lenField 2 enc).length := by
  unfold encodeRecordPrev1Mem
  exact List.length_append

private theorem boundedRustEvs_rustAllocEvents_one (n : Nat) (hpos : 0 < n) (hlt : n < 2 ^ 32) :
    BoundedRustEvs 1 n (rustAllocEvents n 1) := by
  have heq : rustAllocEvents n 1 = [.alloc n] := by
    unfold rustAllocEvents
    split
    · rfl
    · omega
  rw [heq]
  refine ⟨Nat.le_refl 1, fun ev hev => ?_⟩
  simp only [List.mem_singleton] at hev
  subst hev
  refine ⟨?_, Nat.le_refl _, ?_, ?_⟩
  · dsimp only [AllocEvent.withinMaxAlloc]
    have hmax : (2 ^ 32 : Nat) ≤ MallocngMaxAllocSize := by decide
    omega
  · rintro _ _ ⟨⟩
  · rintro _ _ _ ⟨⟩

private theorem vecVecClone1Env_bounded_of_recLt {dst prevPtr : BitVec 64}
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {evs : List AllocEvent}
    (hlt : (encodeRecordPrev1Mem G sess enc).length < 2 ^ 32)
    (h : VecVecClone1Env ⟨dst, prevPtr, enc⟩ evs) :
    BoundedRustEvs 2 (max 24 enc.length) evs := by
  refine vecVecClone1Env_bounded ?_ h
  dsimp only [AllocEvent.withinMaxAlloc]
  have hmax : (2 ^ 32 : Nat) ≤ MallocngMaxAllocSize := by decide
  have hsp := encodeRecordPrev1Mem_len_split G sess enc
  have hle := len_le_lenField 2 enc
  omega

private theorem fitsEnv_sessionClone_of_prev1Alloc {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (hFit : FitsEnv M lim st (SerializePrev1AllocEnvX G sess enc)) :
    FitsEnv M lim st (SessionCloneEnv G sess) := by
  refine FitsEnv.mono (fun evs h => ?_) hFit
  have hsp := encodeRecordPrev1Mem_len_split G sess enc
  have hle := len_le_lenField 1 (encSessionMem G sess)
  dsimp only [SerializePrev1AllocEnvX, SessionCloneEnv] at h ⊢
  exact BoundedRustEvs.mono (by omega) (by omega) h

private theorem fitsEnv_vecVecClone1_of_prev1Alloc {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {dst prevPtr : BitVec 64} {evs1 : List AllocEvent}
    (hFit : FitsEnv M lim st (SerializePrev1AllocEnvX G sess enc))
    (hlt : (encodeRecordPrev1Mem G sess enc).length < 2 ^ 32)
    (h1 : SessionCloneEnv G sess evs1) :
    FitsEnv M lim (M.stepEvents evs1 st) (VecVecClone1Env ⟨dst, prevPtr, enc⟩) := by
  intro evs2 h2
  have hall : SerializePrev1AllocEnvX G sess enc (evs1 ++ evs2) := by
    have h2b := vecVecClone1Env_bounded_of_recLt hlt h2
    have hsp := encodeRecordPrev1Mem_len_split G sess enc
    have hle1 := len_le_lenField 1 (encSessionMem G sess)
    have hle2 := len_le_lenField 2 enc
    dsimp only [SerializePrev1AllocEnvX, SessionCloneEnv] at h1 ⊢
    exact BoundedRustEvs.mono (by omega) (by omega) (h1.append h2b)
  exact ((fitsEvents_append M lim evs1 evs2 st).mp (hFit _ hall)).2

private theorem fitsEvents_alloc_of_prev1Alloc {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {dst prevPtr : BitVec 64} {evs1 evs2 : List AllocEvent}
    (hFit : FitsEnv M lim st (SerializePrev1AllocEnvX G sess enc))
    (hpos : 0 < (encodeRecordPrev1Mem G sess enc).length)
    (hlt : (encodeRecordPrev1Mem G sess enc).length < 2 ^ 32)
    (h1 : SessionCloneEnv G sess evs1)
    (h2 : VecVecClone1Env ⟨dst, prevPtr, enc⟩ evs2) :
    FitsEvents M lim (M.stepEvents evs2 (M.stepEvents evs1 st))
      (rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1) := by
  let recLen := (encodeRecordPrev1Mem G sess enc).length
  have hall : SerializePrev1AllocEnvX G sess enc
      ((evs1 ++ evs2) ++ rustAllocEvents recLen 1) := by
    have h2b := vecVecClone1Env_bounded_of_recLt hlt h2
    have h3b := boundedRustEvs_rustAllocEvents_one recLen hpos hlt
    have hsp := encodeRecordPrev1Mem_len_split G sess enc
    have hle1 := len_le_lenField 1 (encSessionMem G sess)
    have hle2 := len_le_lenField 2 enc
    dsimp only [SerializePrev1AllocEnvX, SessionCloneEnv, recLen] at h1 h3b ⊢
    exact BoundedRustEvs.mono (by omega) (by omega) ((h1.append h2b).append h3b)
  have hf := hFit _ hall
  rw [fitsEvents_append, AllocCostModel.stepEvents_append] at hf
  exact hf.2

private theorem encodeVarint_spare_prev1 (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (enc : List (BitVec 8))
    (hlt : (encodeRecordPrev1Mem G sess enc).length < 2 ^ 32) :
    ([0x0a#8] : List (BitVec 8)).length +
      (encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length ≤
      (BitVec.ofNat 64 (encodeRecordPrev1Mem G sess enc).length).toNat := by
  have hsp := encodeRecordPrev1Mem_len_split G sess enc
  have hcons := congrArg List.length
    (lenField_one_cons_eqX (rfl : encSessionMem G sess = encSessionMem G sess))
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [List.length_cons, List.length_nil, List.length_append] at hcons ⊢
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

private theorem serializePrev1AllocEnvX_of_parts
    {G w : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {dst prevPtr ss v ptr : BitVec 64}
    {evs1 evs2 evs4 evs5 : List AllocEvent}
    (heq : encSessionMem w sess = encSessionMem G sess)
    (hpos : 0 < (encodeRecordPrev1Mem G sess enc).length)
    (hlt : (encodeRecordPrev1Mem G sess enc).length < 2 ^ 32)
    (h1 : SessionCloneEnv G sess evs1)
    (h2 : VecVecClone1Env ⟨dst, prevPtr, enc⟩ evs2)
    (h4 : EncodeRawEnv ⟨ss, w, sess, v,
      BitVec.ofNat 64 (encodeRecordPrev1Mem G sess enc).length, ptr,
      [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)⟩ evs4)
    (h5 : EncRawSegEnv (lenField 1 (encSessionMem G sess)).length (lenField 2 enc).length evs5) :
    SerializePrev1AllocEnvX G sess enc
      ((((evs1 ++ evs2) ++ rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1) ++ evs4) ++
        evs5) := by
  let recLen := (encodeRecordPrev1Mem G sess enc).length
  let L1 := (lenField 1 (encSessionMem G sess)).length
  let L2 := (lenField 2 enc).length
  have hsp : recLen = L1 + L2 := encodeRecordPrev1Mem_len_split G sess enc
  have h2b := vecVecClone1Env_bounded_of_recLt hlt h2
  have h3b := boundedRustEvs_rustAllocEvents_one recLen hpos hlt
  have hout : ([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length +
      (encSessionMem w sess).length = L1 := by
    have hcons := congrArg List.length (lenField_one_cons_eqX heq)
    simp only [L1, List.length_cons, List.length_nil, List.length_append] at hcons ⊢
    omega
  have hcap : (BitVec.ofNat 64 recLen).toNat = recLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  dsimp only [EncodeRawEnv] at h4
  rw [hout, hcap] at h4
  dsimp only [EncRawSegEnv] at h5
  have hle1 := len_le_lenField 1 (encSessionMem G sess)
  have hle2 := len_le_lenField 2 enc
  dsimp only [SerializePrev1AllocEnvX, SessionCloneEnv, recLen, L1, L2] at h1 h3b h4 h5 hsp ⊢
  exact BoundedRustEvs.mono (by omega) (by omega) ((((h1.append h2b).append h3b).append h4).append h5)

private theorem fitsEnv_encodeRaw_of_prev1Alloc {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {G w : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {dst prevPtr ss v ptr : BitVec 64} {evs1 evs2 : List AllocEvent}
    (hFit : FitsEnv M lim st (SerializePrev1AllocEnvX G sess enc))
    (heq : encSessionMem w sess = encSessionMem G sess)
    (hpos : 0 < (encodeRecordPrev1Mem G sess enc).length)
    (hlt : (encodeRecordPrev1Mem G sess enc).length < 2 ^ 32)
    (h1 : SessionCloneEnv G sess evs1)
    (h2 : VecVecClone1Env ⟨dst, prevPtr, enc⟩ evs2) :
    FitsEnv M lim
      (M.stepEvents (rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1)
        (M.stepEvents evs2 (M.stepEvents evs1 st)))
      (EncodeRawEnv ⟨ss, w, sess, v,
        BitVec.ofNat 64 (encodeRecordPrev1Mem G sess enc).length, ptr,
        [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)⟩) := by
  intro evs4 h4
  have h5 : EncRawSegEnv (lenField 1 (encSessionMem G sess)).length (lenField 2 enc).length [] :=
    BoundedRustEvs.nil _ _
  have hall := serializePrev1AllocEnvX_of_parts heq hpos hlt h1 h2 h4 h5
  rw [List.append_nil] at hall
  have hf := hFit _ hall
  rw [fitsEvents_append, AllocCostModel.stepEvents_append, AllocCostModel.stepEvents_append] at hf
  exact hf.2

private theorem fitsEnv_serField2_of_prev1Alloc {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {G w : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {dst prevPtr ss v ptr capF2 : BitVec 64} {evs1 evs2 evs4 : List AllocEvent}
    (hFit : FitsEnv M lim st (SerializePrev1AllocEnvX G sess enc))
    (heq : encSessionMem w sess = encSessionMem G sess)
    (hpos : 0 < (encodeRecordPrev1Mem G sess enc).length)
    (hlt : (encodeRecordPrev1Mem G sess enc).length < 2 ^ 32)
    (h1 : SessionCloneEnv G sess evs1)
    (h2 : VecVecClone1Env ⟨dst, prevPtr, enc⟩ evs2)
    (h4 : EncodeRawEnv ⟨ss, w, sess, v,
      BitVec.ofNat 64 (encodeRecordPrev1Mem G sess enc).length, ptr,
      [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)⟩ evs4) :
    FitsEnv M lim
      (M.stepEvents evs4
        (M.stepEvents (rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1)
          (M.stepEvents evs2 (M.stepEvents evs1 st))))
      (SerField2Env capF2 (lenField 1 (encSessionMem G sess)) enc) := by
  refine fitsEnv_serField2_of_encRawSeg fun evs5 h5 => ?_
  have hall := serializePrev1AllocEnvX_of_parts heq hpos hlt h1 h2 h4 h5
  have hf := hFit _ hall
  rw [fitsEvents_append, AllocCostModel.stepEvents_append, AllocCostModel.stepEvents_append,
    AllocCostModel.stepEvents_append] at hf
  exact hf.2

private theorem fitsEvents_alloc_of_serializePrev1 {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {evs1 evs2 : List AllocEvent}
    (hFit : FitsEnv M lim st
      (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsBudget.SerializePrev1Env
        G sess enc))
    (h1 : LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.SegCloneEnv G sess.state evs1)
    (h2 : evs2 =
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsBudget.vecVecClone1Events
        enc) :
    FitsEvents M lim (M.stepEvents evs2 (M.stepEvents evs1 st))
      (rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1) :=
  (((hFit.seq_right h1).seq_right h2).seq_left) _ rfl

/-! ## Relocatable Body Proofs -/

section Placed

attribute [local irreducible] encSessionMem sessionStateReprAt FitsEvents FitsEnv

local macro "wp_seg_sync52 " hseg:ident mid:term : tactic =>
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

local macro "wp_done_call52 " hcl:ident : tactic =>
  `(tactic| (
    apply SepWP.done
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; assumption)
    intro $hcl:ident
    simp only [arm64_norm] at $hcl:ident))

set_option maxHeartbeats 1200000 in
/-- Budget-threaded `[LibsignalPlacement]` body contract for `SessionRecord::serialize` (block 52)
under `SerializePrev1EnvX`. -/
theorem serializePrev1Body_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hClone : SessionClonePlacedOkX M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hRaw : EncodeRawPlacedOkX M A lim H)
    (hK1 : VecVecClone1PlacedOkStmt M A lim H)
    (hF2 : SerField2PlacedStepStmt M A lim H)
    (hTail : SerPrev1PlacedTailStmt M A lim H) :
    SerializePrev1BodyPlacedOkWithEnvStmt M A lim H SerializePrev1EnvX := by
  unfold SerializePrev1BodyPlacedOkWithEnvStmt
  have hmemcpy := memcpy_placed_sub_clX (callerProg := lsProg_52 H) hC
  have hshim := shim_placed_sub_clX (callerProg := lsProg_52 H) hC
  have halloc := allocNoOom_placed_sub_clX (callerProg := lsProg_52 H) hC
  have hclone := sessionClone_placed_sub_clX (callerProg := lsProg_52 H) hClone
  have hvv1 := vecVecClone1_placed_sub_clX (callerProg := lsProg_52 H) hK1
  have hlen := sessionLen_placed_sub_clX A.repAlloc (callerProg := lsProg_52 H)
  have hev := encodeVarint_placed_sub_clX (callerProg := lsProg_52 H) hEV
  have hraw := encodeRaw_placed_sub_clX (callerProg := lsProg_52 H) hRaw
  change subroutine_ok (lsProg_52 H) (lsρ lsMemcpySym) (withLsCl lsmpl memcpySubSpecX) at hmemcpy
  change subroutine_ok (lsProg_52 H) (lsρ lsRustNoAllocShimSym)
    (withLsCl lsmpl shimSubSpecX) at hshim
  change subroutine_ok (lsProg_52 H) (lsρ lsRustAllocSym)
    (withLsCl lsmpl (rustAllocNoOomSubSpecX M A lim)) at halloc
  change subroutine_ok (lsProg_52 H) (lsmpl.base 80)
    (withLsCl lsmpl (sessionCloneSubSpecX M A lim)) at hclone
  change subroutine_ok (lsProg_52 H) (lsmpl.base 117)
    (withLsCl lsmpl (vecVecClone1SubSpecX M A lim)) at hvv1
  change subroutine_ok (lsProg_52 H) (lsmpl.base 86)
    (withLsCl lsmpl (sessionLenSubSpecX A.repAlloc)) at hlen
  change subroutine_ok (lsProg_52 H) (lsmpl.base 10)
    (withLsCl lsmpl (encodeVarintSubSpecX M A lim)) at hev
  change subroutine_ok (lsProg_52 H) (lsmpl.base 14)
    (withLsCl lsmpl (encodeRawSubSpecX M A lim)) at hraw
  dsimp only [withLsCl, memcpySubSpecX, shimSubSpecX, rustAllocNoOomSubSpecX,
    sessionCloneSubSpecX, vecVecClone1SubSpecX, sessionLenSubSpecX,
    encodeVarintSubSpecX, encodeRawSubSpecX]
    at hmemcpy hshim halloc hclone hvv1 hlen hev hraw
  conv =>
    arg 3; arg 2
    unfold serializePrev1BodySpecWithEnvX
    simp only [memRegion_out32_pool_stack_swap, memRegion_out32_stack_someX,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wpplscl_init x s0
  unfold SerField2PlacedStepStmt at hF2
  unfold SerPrev1PlacedTailStmt
    LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBBudget.SerPrev1PlacedTailStmt
    at hTail
  obtain ⟨⟨self, out, prevCap, prevPtr, G, sess, enc⟩, st⟩ := x
  dsimp only at *
  have hrec_lt : (encodeRecordPrev1Mem G sess enc).length < 2 ^ 32 := by assumption
  have hFit_full : FitsEnv M lim st (SerializePrev1EnvX G sess enc) := by assumption
  have hFit0 : FitsEnv M lim st (SerializePrev1AllocEnvX G sess enc) := hFit_full.seq_left
  have hseg52 := fun {mid target : BitVec 64} {s : State} {Pre : SepProp}
      {post : State → SepProp → Prop} {oom : State → SepProp} =>
    sepWP_seg_ls_vm (prog := lsProg_52 H) (Q := lsProg_52 (hooksException H))
      blkLib_eq_52 (by rfl) (mid := mid) (target := target) (s := s) (Pre := Pre)
      (post := post) (oom := oom)
  intro hcl0
  refine SepWPpLsCl.of_sepWP (mid := (blkPl_52).base + bv% (444)) ?_ hcl0
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 80)
  refine SepWP.fold (sessionAt_unpack_head_tail A.repAlloc (self + 24#64) G sess) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro bs336_self
  apply sepWP_pure_left_sepX; rintro ⟨hbs336_self, hcap_self, hinl_self⟩
  have hcmn_self : (G.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCapX hcap_self
  wp_seg_sync52 hseg52 (lsmpl.base 80)
  refine SepWP.fold (sessionAt_pack_head_tail A.repAlloc (self + 24#64) G sess hinl_self)
    (by sep_frame) ?_
  wp_done_call52 hcl1
  have hFit_clone := fitsEnv_sessionClone_of_prev1Alloc hFit0
  wp_call hclone (⟨s0.sp - 800#64, self + 24#64, G, sess⟩, st)
  have h1_env : SessionCloneEnv G sess w := by assumption
  have heq_enc : encSessionMem w_1 sess = encSessionMem G sess := by assumption
  have heq_encF : ∀ s', s' = sess → encSessionMem w_1 s' = encSessionMem G s' :=
    fun _ hs => hs ▸ heq_enc
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsMemcpySym); · assumption
  refine SepWP.fold (sessionAt_unpack_800X A.repAlloc s0.sp w_1 sess) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro bs336_clone
  apply sepWP_pure_left_sepX; rintro ⟨hbs336_clone, hcap_clone, hinl_clone⟩
  have hcmn_clone : (w_1.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCapX hcap_clone
  wp_seg_sync52 hseg52 (lsρ lsMemcpySym)
  wp_done_call52 hcl2
  rw [memRegion_eq_of_len hbs336_clone]
  wp_call hmemcpy (s0.sp - 432#64, s0.sp - 792#64, bs336_clone)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_1› (hnext := ?_)
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 117); · assumption
  refine SepWP.fold (repack_frame_368 s0.sp w_1.localIk.cap hbs336_clone) (by sep_frame) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro w_k1
  refine SepWP.fold (Entails.of_eq (prevVecAt_one_pure_first A self prevCap prevPtr enc))
    (by sep_frame) ?_
  apply sepWP_pure_left_sepX; rintro ⟨hpcap0, hpcap24, hpptr0⟩
  conv => arg 4; simp only [sepConj_assoc]
  wp_seg_sync52 hseg52 (lsmpl.base 117)
  wp_done_call52 hcl3
  have hFit_vv1 :=
    fitsEnv_vecVecClone1_of_prev1Alloc (dst := s0.sp - 800#64) (prevPtr := prevPtr)
      hFit0 hrec_lt h1_env
  wp_call hvv1 (⟨s0.sp - 800#64, prevPtr, enc⟩, M.stepEvents w st)
  have h2_env : VecVecClone1Env ⟨s0.sp - 800#64, prevPtr, enc⟩ w_2 := by assumption
  let q' : BitVec 64 := w_3
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsMemcpySym); · assumption
  refine SepWP.fold (prevVecAt_one_fold_ser A self prevCap prevPtr enc ⟨hpcap0, hpcap24, hpptr0⟩)
    (by sep_frame) ?_
  wp_seg_sync52 hseg52 (lsρ lsMemcpySym)
  wp_done_call52 hcl4
  rw [memRegion_eq_of_len hbs336_clone]
  wp_call hmemcpy (s0.sp - 768#64, s0.sp - 432#64, bs336_clone)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_3› (hnext := ?_)
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 86); · assumption
  refine SepWP.fold (sessionAt_pack_776X A.repAlloc s0.sp w_1 sess hinl_clone) (by sep_frame) ?_
  refine SepWP.fold (bytes336_to_w012 s0.sp hbs336_clone) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro w0
  apply sepWP_exists_left_sepX; intro w1
  apply sepWP_exists_left_sepX; intro w2
  refine SepWP.fold (Entails.of_eq (prevVecAt_800_open A s0.sp q' enc)) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro capE
  apply sepWP_exists_left_sepX; intro ptrE
  apply sepWP_pure_left_sepX; intro hq0
  conv => arg 4; simp only [sepConj_assoc]
  have hrec_len : (lenField 1 (encSessionMem G sess)).length + (lenField 2 enc).length < 2 ^ 32 := by
    rwa [← encodeRecordPrev1Mem_len_split G sess enc]
  have hlen_bounds_G : (lenField 1 (encSessionMem G sess)).length < 2 ^ 32 := by omega
  obtain ⟨hbs_lt_G, hlf_pos_G, hlf_lt63_G, hlayout_G, hv_lt62_G, hv_le_lf_G, hraw_lt_G⟩ :=
    lenField_one_bounds hlen_bounds_G
  obtain ⟨hbr_ls_G, hbr_tbz_G, hbr_cbz_G⟩ := lenField_one_branch_condsX hlen_bounds_G
  have hcap_toNat_G := lenField_one_bv_toNatX hlen_bounds_G
  have hex_pow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hL1e := lenField_one_length enc
  have hL2e := lenField_two_length enc
  have hbr_loop : (BitVec.ofNat 64 (lenField 1 enc).length).ult
      (BitVec.ofNat 64 enc.length +
        BitVec.ofNat 64 (encodeVarint (BitVec.ofNat 64 enc.length)).length) = false := by
    rw [← BitVec.ofNat_add]
    simp only [BitVec.ult, BitVec.toNat_ofNat]
    have h1 : (lenField 1 enc).length % 2 ^ 64 = (lenField 1 enc).length :=
      Nat.mod_eq_of_lt (by omega)
    have h2 : (enc.length + (encodeVarint (BitVec.ofNat 64 enc.length)).length) % 2 ^ 64 =
        enc.length + (encodeVarint (BitVec.ofNat 64 enc.length)).length :=
      Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]
    exact decide_eq_false (by omega)
  have hbr_c2 := ult_ofNat_add_false (a := (lenField 1 enc).length)
    (b := (lenField 1 (encSessionMem G sess)).length) (by omega)
  obtain ⟨hbr_tbz2, hbr_cbz2⟩ := ofNat_add_bits (a := (lenField 1 enc).length)
    (b := (lenField 1 (encSessionMem G sess)).length) (by omega) (by omega)
  clear hL1e hL2e
  have hbs_lt_w : (encSessionMem w_1 sess).length < 2 ^ 32 := by rw [heq_enc]; exact hbs_lt_G
  wp_seg_sync52 hseg52 (lsmpl.base 86)
  wp_done_call52 hcl5
  wp_call hlen ⟨s0.sp - 776#64, w_1, sess⟩
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_4› (hnext := ?_)
  simp only [heq_enc] at *
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsRustNoAllocShimSym); · assumption
  wp_seg_sync52 hseg52 (lsρ lsRustNoAllocShimSym)
  wp_done_call52 hcl6
  wp_call hshim ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_5› (hnext := ?_)
  have hNsplit : (encodeRecordPrev1Mem G sess enc).length =
      (lenField 1 enc).length + (lenField 1 (encSessionMem G sess)).length := by
    have h1 := lenField_one_length enc
    have h2 := lenField_two_length enc
    rw [encodeRecordPrev1Mem_len_split]
    omega
  have hN_pos : 1 ≤ (encodeRecordPrev1Mem G sess enc).length := by omega
  have hN_lt : (encodeRecordPrev1Mem G sess enc).length < 2 ^ 32 := hrec_lt
  have hN_toNat : (BitVec.ofNat 64 (lenField 1 enc).length +
      BitVec.ofNat 64 (lenField 1 (encSessionMem G sess)).length).toNat =
      (encodeRecordPrev1Mem G sess enc).length := by
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hNsplit]
  clear hNsplit
  have hsz_pos : 0 < (encodeRecordPrev1Mem G sess enc).length := by omega
  have hsz_le : (encodeRecordPrev1Mem G sess enc).length + 1 ≤ 2 ^ 63 := by omega
  have hrlay : RustLayoutOk (encodeRecordPrev1Mem G sess enc).length 1 :=
    ⟨⟨hsz_pos, hex_pow, hsz_le⟩, by decide⟩
  have hFit_alloc := fitsEvents_alloc_of_prev1Alloc hFit0 hsz_pos hN_lt h1_env h2_env
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsRustAllocSym); · assumption
  wp_seg_sync52 hseg52 (lsρ lsRustAllocSym)
  wp_done_call52 hcl7
  wp_call halloc ((encodeRecordPrev1Mem G sess enc).length, 1, M.stepEvents w_2 (M.stepEvents w st))
  have htr_sf6 := (‹AllocCallPreserved _ sf_6›).2.1
  have hp0_ne : sf_6.readReg64 Reg.x0 ≠ 0#64 := by assumption
  have hp0' : sf_6.readReg64 (Reg.gpr 0#5) ≠ 0 := hp0_ne
  have hp0_beq : (sf_6.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hp0_ne
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 86); · assumption
  rw [memRegion_split_init_byteX (sf_6.readReg64 (Reg.gpr 0#5)) hN_pos (by omega)]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro b0
  wp_seg_sync52 hseg52 (lsmpl.base 86)
  wp_done_call52 hcl8
  have hbs_lt_w2 : (encSessionMem w_1 sess).length < 2 ^ 32 := by
    rw [heq_encF sess rfl]; exact hbs_lt_G
  wp_call hlen ⟨s0.sp - 776#64, w_1, sess⟩
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_7› (hnext := ?_)
  try simp only [heq_encF sess rfl] at *
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 10); · assumption
  wp_seg_sync52 hseg52 (lsmpl.base 10)
  refine SepWP.fold (vecU8At_init_byte_432_cap A s0.sp (sf_6.readReg64 (Reg.gpr 0#5)) _
    (encodeRecordPrev1Mem G sess enc).length 0x0a#8 hN_toNat hN_pos hN_lt hp0')
    (by sep_frame) ?_
  wp_done_call52 hcl9
  have hspare_ev := encodeVarint_spare_prev1 G sess enc hN_lt
  let evGhost : EncodeVarintGhost :=
    ⟨BitVec.ofNat 64 (encSessionMem G sess).length, s0.sp - 432#64,
      BitVec.ofNat 64 (encodeRecordPrev1Mem G sess enc).length,
      sf_6.readReg64 (Reg.gpr 0#5), [0x0a#8]⟩
  have hFit_ev : FitsEnv M lim
      (M.stepEvents (rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1)
        (M.stepEvents w_2 (M.stepEvents w st)))
      (EncodeVarintEnv evGhost) :=
    fitsEnv_encodeVarint_of_spare _ evGhost hspare_ev
  wp_call hev (evGhost,
    M.stepEvents (rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1)
      (M.stepEvents w_2 (M.stepEvents w st)))
  have hevs_ev_nil : _ = ([] : List AllocEvent) :=
    eq_nil_of_encodeVarintEnv (x := evGhost) hspare_ev (by assumption)
  rw [hevs_ev_nil] at *
  simp only [AllocCostModel.stepEvents_nil] at *
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 14); · assumption
  wp_seg_sync52 hseg52 (lsmpl.base 14)
  wp_done_call52 hcl10
  have hraw_lt_w :
      ([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length +
        (encSessionMem w_1 sess).length < 2 ^ 32 := by
    rw [heq_encF sess rfl]; exact hraw_lt_G
  have hwcap_eq : w_5 = BitVec.ofNat 64 (encodeRecordPrev1Mem G sess enc).length := by
    have hsp1 := hspare_ev
    have hN_bv : (BitVec.ofNat 64 (encodeRecordPrev1Mem G sess enc).length).toNat =
        (encodeRecordPrev1Mem G sess enc).length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hsp2 : 1 + (encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length ≤
        (encodeRecordPrev1Mem G sess enc).length := by
      simpa only [List.length_cons, List.length_nil, hN_bv] using hspare_ev
    dsimp only [evGhost, List.length_cons, List.length_nil] at *
    tauto
  rw [hwcap_eq]
  let rawGhost : EncodeRawGhost :=
    ⟨s0.sp - 776#64, w_1, sess, s0.sp - 432#64,
      BitVec.ofNat 64 (encodeRecordPrev1Mem G sess enc).length,
      w_6, [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)⟩
  have hFit_raw : FitsEnv M lim
      (M.stepEvents (rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1)
        (M.stepEvents w_2 (M.stepEvents w st)))
      (EncodeRawEnv rawGhost) :=
    fitsEnv_encodeRaw_of_prev1Alloc (ss := s0.sp - 776#64) (v := s0.sp - 432#64) (ptr := w_6)
      hFit0 (heq_encF sess rfl) hsz_pos hN_lt h1_env h2_env
  wp_call hraw (rawGhost,
    M.stepEvents (rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1)
      (M.stepEvents w_2 (M.stepEvents w st)))
  have h4_env : EncodeRawEnv rawGhost w_7 := by assumption
  conv => arg 4; dsimp only [rawGhost]; simp only [List.cons_append, List.nil_append]
  rw [lenField_one_cons_eqX (heq_encF sess rfl)]
  wp_seg_sync52 hseg52 ((blkPl_52).base + bv% (444))
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm]; assumption)
  refine k5_fold_q_placed A q' capE ptrE enc (by sep_frame) ?_
  have hFit_f2 :=
    fitsEnv_serField2_of_prev1Alloc (ss := s0.sp - 776#64) (v := s0.sp - 432#64) (ptr := w_6)
      (capF2 := w_8) hFit0 (heq_encF sess rfl) hsz_pos hN_lt h1_env h2_env h4_env
  refine hF2 s0.sp q' w_8 w_9 capE ptrE (lenField 1 (encSessionMem G sess)) enc
    (M.stepEvents w_7
      (M.stepEvents (rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1)
        (M.stepEvents w_2 (M.stepEvents w st))))
    (s0 := s0) hrec_len hFit_f2
    (by k5_side) (by k5_side) (by k5_side)
    (beq_iff_eq.mp hsp_align) (by k5_side) (by k5_side) (by k5_side) (by sep_frame) ?_
  intro sm cap' ptr' evs5 h5_env hpc_m hrun_m hsp_m htr_m hsv_m
  obtain ⟨hsv19, hsv23, hsv24, hsv28, hsvfp, hsvv⟩ := hsv_m
  refine SepWPpLsCl.weaken_pre ?_
    (hTail out q' capE ptrE cap' ptr' v_stk_15 v_stk_14 v_stk_13 v_stk_12
      (encodeRecordPrev1Mem G sess enc) enc w_1 sess
      (M.stepEvents evs5
        (M.stepEvents w_7
          (M.stepEvents (rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1)
            (M.stepEvents w_2 (M.stepEvents w st)))))
      (s0 := s0) (sm := sm)
      (Fx := prevVecAt A.repAlloc self prevCap prevPtr [enc] ∗
        sessionStateReprAt A.repAlloc (self + 24#64) G sess)
      ?_ (beq_iff_eq.mp hsp_align) hpc_m hrun_m hsp_m htr_m
      (by rw [hsv19]; k5_side) (by rw [hsv23]; k5_side) (by rw [hsv24]; k5_side)
      (by rw [hsvv]; k5_side))
  · unfold serSavedCells encodeRecordPrev1Mem
    exact entails_of_sep_focus (by sep_frame)
  · intro sf evs_tail htr_f hsp_f hcs_f hfree_tail
    refine ⟨fun hm => ?_, hsp_f, hcs_f⟩
    simp only [← AllocCostModel.stepEvents_append] at hm
    have hAlloc : SerializePrev1AllocEnvX G sess enc
        ((((w ++ w_2) ++ rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1) ++ w_7) ++
          evs5) :=
      serializePrev1AllocEnvX_of_parts (heq_encF sess rfl) hsz_pos hN_lt
        h1_env h2_env h4_env (encRawSegEnv_of_serField2Env h5_env)
    have hEnv_final : SerializePrev1EnvX G sess enc
        (((((w ++ w_2) ++ rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1) ++ w_7) ++
          evs5) ++ evs_tail) :=
      SeqEnv.append hAlloc hfree_tail
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨((((w ++ w_2) ++ rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1) ++ w_7) ++
      evs5) ++ evs_tail, ?_⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    exact Entails.pure_right ⟨htr_f, hEnv_final⟩ (Entails.of_eq (by sep_ac_rfl))

theorem serializePrev1Body_placed_ok_withEnvX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hClone : SessionClonePlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hRaw : EncodeRawPlacedOkX M A lim H)
    (hK1 : VecVecClone1PlacedOkStmt M A lim H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    SerializePrev1BodyPlacedOkWithEnvStmt M A lim H SerializePrev1EnvX :=
  serializePrev1Body_placed_ok hC hClone hEV hRaw hK1
    (serField2_placed_step hC hDR hEV)
    (serPrev1Tail_placed_ok hC hDrop)

section SeqFree

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsBudget
  (SerializePrev1Env fitsEnv_segClone_of_serializePrev1)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsPlacedBudget
  (SerializePrev1BodyPlacedOkStmt fitsEnv_serField2_of_spare serializePrev1BodySpecWithEnvX_eq
   serField2Env_of_spare)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsBudget
  (vecVecClone1Events)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget
  (EncodeRawPreallocPlacedOkX encodeRawPreallocSubSpecX encodeRawPrealloc_placed_sub_clX)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeSeqFreeXBudget
  (sessionCloneSegSubSpecX sessionCloneSeg_placed_sub_clX)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneSeqFreeXBudget
  (SessionCloneSegPlacedOkX)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv)

private theorem encodeRaw_spare_prev1 {G w : SessionGhost}
    {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (heq : encSessionMem w sess = encSessionMem G sess)
    (hlt : (encodeRecordPrev1Mem G sess enc).length < 2 ^ 32) :
    ([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length +
      (encSessionMem w sess).length ≤
      (BitVec.ofNat 64 (encodeRecordPrev1Mem G sess enc).length).toNat := by
  have hcap : (BitVec.ofNat 64 (encodeRecordPrev1Mem G sess enc).length).toNat =
      (encodeRecordPrev1Mem G sess enc).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsplit := encodeRecordPrev1Mem_len_split G sess enc
  have hcons := congrArg List.length (lenField_one_cons_eqX heq)
  simp only [List.length_cons, List.length_nil, List.length_append] at hcons ⊢
  omega

private theorem serField2_spare_prev1 (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (enc : List (BitVec 8))
    (hlt : (encodeRecordPrev1Mem G sess enc).length < 2 ^ 32) :
    (lenField 1 (encSessionMem G sess)).length + (lenField 2 enc).length ≤
      (BitVec.ofNat 64 (encodeRecordPrev1Mem G sess enc).length).toNat := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), encodeRecordPrev1Mem_len_split]

set_option maxHeartbeats 1200000 in
/-- Sequence-free (`SerializePrev1Env`) `[LibsignalPlacement]` body contract for
`SessionRecord::serialize`, using `sessionCloneSeg_placed_sub_clX` and pre-reserved
zero-allocation `encodeRawPrealloc_placed_sub_clX`. -/
theorem serializePrev1Body_seqFree_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hClone : SessionCloneSegPlacedOkX M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H)
    (hK1 : VecVecClone1PlacedOkStmt M A lim H)
    (hF2 : SerField2PlacedStepStmt M A lim H)
    (hTail : SerPrev1PlacedTailStmt M A lim H) :
    SerializePrev1BodyPlacedOkStmt M A lim H := by
  unfold SerializePrev1BodyPlacedOkStmt
  rw [← serializePrev1BodySpecWithEnvX_eq]
  have hmemcpy := memcpy_placed_sub_clX (callerProg := lsProg_52 H) hC
  have hshim := shim_placed_sub_clX (callerProg := lsProg_52 H) hC
  have halloc := allocNoOom_placed_sub_clX (callerProg := lsProg_52 H) hC
  have hclone := sessionCloneSeg_placed_sub_clX (callerProg := lsProg_52 H) hClone
  have hvv1 := vecVecClone1_placed_sub_clX (callerProg := lsProg_52 H) hK1
  have hlen := sessionLen_placed_sub_clX A.repAlloc (callerProg := lsProg_52 H)
  have hev := encodeVarint_placed_sub_clX (callerProg := lsProg_52 H) hEV
  have hraw := encodeRawPrealloc_placed_sub_clX (callerProg := lsProg_52 H) hRaw
  change subroutine_ok (lsProg_52 H) (lsρ lsMemcpySym) (withLsCl lsmpl memcpySubSpecX) at hmemcpy
  change subroutine_ok (lsProg_52 H) (lsρ lsRustNoAllocShimSym)
    (withLsCl lsmpl shimSubSpecX) at hshim
  change subroutine_ok (lsProg_52 H) (lsρ lsRustAllocSym)
    (withLsCl lsmpl (rustAllocNoOomSubSpecX M A lim)) at halloc
  change subroutine_ok (lsProg_52 H) (lsmpl.base 80)
    (withLsCl lsmpl (sessionCloneSegSubSpecX M A lim)) at hclone
  change subroutine_ok (lsProg_52 H) (lsmpl.base 117)
    (withLsCl lsmpl (vecVecClone1SubSpecX M A lim)) at hvv1
  change subroutine_ok (lsProg_52 H) (lsmpl.base 86)
    (withLsCl lsmpl (sessionLenSubSpecX A.repAlloc)) at hlen
  change subroutine_ok (lsProg_52 H) (lsmpl.base 10)
    (withLsCl lsmpl (encodeVarintSubSpecX M A lim)) at hev
  change subroutine_ok (lsProg_52 H) (lsmpl.base 14)
    (withLsCl lsmpl (encodeRawPreallocSubSpecX A.repAlloc)) at hraw
  dsimp only [withLsCl, memcpySubSpecX, shimSubSpecX, rustAllocNoOomSubSpecX,
    sessionCloneSegSubSpecX, vecVecClone1SubSpecX, sessionLenSubSpecX,
    encodeVarintSubSpecX, encodeRawPreallocSubSpecX]
    at hmemcpy hshim halloc hclone hvv1 hlen hev hraw
  conv =>
    arg 3; arg 2
    unfold serializePrev1BodySpecWithEnvX
    simp only [memRegion_out32_pool_stack_swap, memRegion_out32_stack_someX,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wpplscl_init x s0
  unfold SerField2PlacedStepStmt at hF2
  unfold SerPrev1PlacedTailStmt
    LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBBudget.SerPrev1PlacedTailStmt
    at hTail
  obtain ⟨⟨self, out, prevCap, prevPtr, G, sess, enc⟩, st⟩ := x
  dsimp only at *
  have hrec_lt : (encodeRecordPrev1Mem G sess enc).length < 2 ^ 32 := by assumption
  have hFit_full : FitsEnv M lim st (SerializePrev1Env G sess enc) := by assumption
  have hseg52 := fun {mid target : BitVec 64} {s : State} {Pre : SepProp}
      {post : State → SepProp → Prop} {oom : State → SepProp} =>
    sepWP_seg_ls_vm (prog := lsProg_52 H) (Q := lsProg_52 (hooksException H))
      blkLib_eq_52 (by rfl) (mid := mid) (target := target) (s := s) (Pre := Pre)
      (post := post) (oom := oom)
  intro hcl0
  refine SepWPpLsCl.of_sepWP (mid := (blkPl_52).base + bv% (444)) ?_ hcl0
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 80)
  refine SepWP.fold (sessionAt_unpack_head_tail A.repAlloc (self + 24#64) G sess) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro bs336_self
  apply sepWP_pure_left_sepX; rintro ⟨hbs336_self, hcap_self, hinl_self⟩
  have hcmn_self : (G.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCapX hcap_self
  wp_seg_sync52 hseg52 (lsmpl.base 80)
  refine SepWP.fold (sessionAt_pack_head_tail A.repAlloc (self + 24#64) G sess hinl_self)
    (by sep_frame) ?_
  wp_done_call52 hcl1
  have hFit_clone : FitsEnv M lim st (SegCloneEnv G sess.state) :=
    fitsEnv_segClone_of_serializePrev1 hFit_full
  wp_call hclone (⟨s0.sp - 800#64, self + 24#64, G, sess⟩, st)
  have h1_env : SegCloneEnv G sess.state w := by assumption
  have heq_enc : encSessionMem w_1 sess = encSessionMem G sess := by assumption
  have heq_encF : ∀ s', s' = sess → encSessionMem w_1 s' = encSessionMem G s' :=
    fun _ hs => hs ▸ heq_enc
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsMemcpySym); · assumption
  refine SepWP.fold (sessionAt_unpack_800X A.repAlloc s0.sp w_1 sess) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro bs336_clone
  apply sepWP_pure_left_sepX; rintro ⟨hbs336_clone, hcap_clone, hinl_clone⟩
  have hcmn_clone : (w_1.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCapX hcap_clone
  wp_seg_sync52 hseg52 (lsρ lsMemcpySym)
  wp_done_call52 hcl2
  rw [memRegion_eq_of_len hbs336_clone]
  wp_call hmemcpy (s0.sp - 432#64, s0.sp - 792#64, bs336_clone)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_1› (hnext := ?_)
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 117); · assumption
  refine SepWP.fold (repack_frame_368 s0.sp w_1.localIk.cap hbs336_clone) (by sep_frame) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro w_k1
  refine SepWP.fold (Entails.of_eq (prevVecAt_one_pure_first A self prevCap prevPtr enc))
    (by sep_frame) ?_
  apply sepWP_pure_left_sepX; rintro ⟨hpcap0, hpcap24, hpptr0⟩
  conv => arg 4; simp only [sepConj_assoc]
  wp_seg_sync52 hseg52 (lsmpl.base 117)
  wp_done_call52 hcl3
  have hFit_vv1 : FitsEnv M lim (M.stepEvents w st)
      (VecVecClone1Env ⟨s0.sp - 800#64, prevPtr, enc⟩) :=
    (hFit_full.seq_right h1_env).seq_left
  wp_call hvv1 (⟨s0.sp - 800#64, prevPtr, enc⟩, M.stepEvents w st)
  have h2_env : VecVecClone1Env ⟨s0.sp - 800#64, prevPtr, enc⟩ w_2 := by assumption
  have h2_eq : w_2 = vecVecClone1Events enc := h2_env
  let q' : BitVec 64 := w_3
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsMemcpySym); · assumption
  refine SepWP.fold (prevVecAt_one_fold_ser A self prevCap prevPtr enc ⟨hpcap0, hpcap24, hpptr0⟩)
    (by sep_frame) ?_
  wp_seg_sync52 hseg52 (lsρ lsMemcpySym)
  wp_done_call52 hcl4
  rw [memRegion_eq_of_len hbs336_clone]
  wp_call hmemcpy (s0.sp - 768#64, s0.sp - 432#64, bs336_clone)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_3› (hnext := ?_)
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 86); · assumption
  refine SepWP.fold (sessionAt_pack_776X A.repAlloc s0.sp w_1 sess hinl_clone) (by sep_frame) ?_
  refine SepWP.fold (bytes336_to_w012 s0.sp hbs336_clone) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro w0
  apply sepWP_exists_left_sepX; intro w1
  apply sepWP_exists_left_sepX; intro w2
  refine SepWP.fold (Entails.of_eq (prevVecAt_800_open A s0.sp q' enc)) (by sep_frame) ?_
  apply sepWP_exists_left_sepX; intro capE
  apply sepWP_exists_left_sepX; intro ptrE
  apply sepWP_pure_left_sepX; intro hq0
  conv => arg 4; simp only [sepConj_assoc]
  have hrec_len : (lenField 1 (encSessionMem G sess)).length + (lenField 2 enc).length < 2 ^ 32 := by
    rwa [← encodeRecordPrev1Mem_len_split G sess enc]
  have hlen_bounds_G : (lenField 1 (encSessionMem G sess)).length < 2 ^ 32 := by omega
  obtain ⟨hbs_lt_G, hlf_pos_G, hlf_lt63_G, hlayout_G, hv_lt62_G, hv_le_lf_G, hraw_lt_G⟩ :=
    lenField_one_bounds hlen_bounds_G
  obtain ⟨hbr_ls_G, hbr_tbz_G, hbr_cbz_G⟩ := lenField_one_branch_condsX hlen_bounds_G
  have hcap_toNat_G := lenField_one_bv_toNatX hlen_bounds_G
  have hex_pow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hL1e := lenField_one_length enc
  have hL2e := lenField_two_length enc
  have hbr_loop : (BitVec.ofNat 64 (lenField 1 enc).length).ult
      (BitVec.ofNat 64 enc.length +
        BitVec.ofNat 64 (encodeVarint (BitVec.ofNat 64 enc.length)).length) = false := by
    rw [← BitVec.ofNat_add]
    simp only [BitVec.ult, BitVec.toNat_ofNat]
    have h1 : (lenField 1 enc).length % 2 ^ 64 = (lenField 1 enc).length :=
      Nat.mod_eq_of_lt (by omega)
    have h2 : (enc.length + (encodeVarint (BitVec.ofNat 64 enc.length)).length) % 2 ^ 64 =
        enc.length + (encodeVarint (BitVec.ofNat 64 enc.length)).length :=
      Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]
    exact decide_eq_false (by omega)
  have hbr_c2 := ult_ofNat_add_false (a := (lenField 1 enc).length)
    (b := (lenField 1 (encSessionMem G sess)).length) (by omega)
  obtain ⟨hbr_tbz2, hbr_cbz2⟩ := ofNat_add_bits (a := (lenField 1 enc).length)
    (b := (lenField 1 (encSessionMem G sess)).length) (by omega) (by omega)
  clear hL1e hL2e
  have hbs_lt_w : (encSessionMem w_1 sess).length < 2 ^ 32 := by rw [heq_enc]; exact hbs_lt_G
  wp_seg_sync52 hseg52 (lsmpl.base 86)
  wp_done_call52 hcl5
  wp_call hlen ⟨s0.sp - 776#64, w_1, sess⟩
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_4› (hnext := ?_)
  simp only [heq_enc] at *
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsRustNoAllocShimSym); · assumption
  wp_seg_sync52 hseg52 (lsρ lsRustNoAllocShimSym)
  wp_done_call52 hcl6
  wp_call hshim ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_5› (hnext := ?_)
  have hNsplit : (encodeRecordPrev1Mem G sess enc).length =
      (lenField 1 enc).length + (lenField 1 (encSessionMem G sess)).length := by
    have h1 := lenField_one_length enc
    have h2 := lenField_two_length enc
    rw [encodeRecordPrev1Mem_len_split]
    omega
  have hN_pos : 1 ≤ (encodeRecordPrev1Mem G sess enc).length := by omega
  have hN_lt : (encodeRecordPrev1Mem G sess enc).length < 2 ^ 32 := hrec_lt
  have hN_toNat : (BitVec.ofNat 64 (lenField 1 enc).length +
      BitVec.ofNat 64 (lenField 1 (encSessionMem G sess)).length).toNat =
      (encodeRecordPrev1Mem G sess enc).length := by
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hNsplit]
  clear hNsplit
  have hsz_pos : 0 < (encodeRecordPrev1Mem G sess enc).length := by omega
  have hsz_le : (encodeRecordPrev1Mem G sess enc).length + 1 ≤ 2 ^ 63 := by omega
  have hrlay : RustLayoutOk (encodeRecordPrev1Mem G sess enc).length 1 :=
    ⟨⟨hsz_pos, hex_pow, hsz_le⟩, by decide⟩
  have hFit_alloc : FitsEvents M lim (M.stepEvents w_2 (M.stepEvents w st))
      (rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1) :=
    fitsEvents_alloc_of_serializePrev1 hFit_full h1_env h2_eq
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsRustAllocSym); · assumption
  wp_seg_sync52 hseg52 (lsρ lsRustAllocSym)
  wp_done_call52 hcl7
  wp_call halloc ((encodeRecordPrev1Mem G sess enc).length, 1, M.stepEvents w_2 (M.stepEvents w st))
  have htr_sf6 := (‹AllocCallPreserved _ sf_6›).2.1
  have hp0_ne : sf_6.readReg64 Reg.x0 ≠ 0#64 := by assumption
  have hp0' : sf_6.readReg64 (Reg.gpr 0#5) ≠ 0 := hp0_ne
  have hp0_beq : (sf_6.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hp0_ne
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 86); · assumption
  rw [memRegion_split_init_byteX (sf_6.readReg64 (Reg.gpr 0#5)) hN_pos (by omega)]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro b0
  wp_seg_sync52 hseg52 (lsmpl.base 86)
  wp_done_call52 hcl8
  have hbs_lt_w2 : (encSessionMem w_1 sess).length < 2 ^ 32 := by
    rw [heq_encF sess rfl]; exact hbs_lt_G
  wp_call hlen ⟨s0.sp - 776#64, w_1, sess⟩
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_7› (hnext := ?_)
  try simp only [heq_encF sess rfl] at *
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 10); · assumption
  wp_seg_sync52 hseg52 (lsmpl.base 10)
  refine SepWP.fold (vecU8At_init_byte_432_cap A s0.sp (sf_6.readReg64 (Reg.gpr 0#5)) _
    (encodeRecordPrev1Mem G sess enc).length 0x0a#8 hN_toNat hN_pos hN_lt hp0')
    (by sep_frame) ?_
  wp_done_call52 hcl9
  have hspare_ev := encodeVarint_spare_prev1 G sess enc hN_lt
  let evGhost : EncodeVarintGhost :=
    ⟨BitVec.ofNat 64 (encSessionMem G sess).length, s0.sp - 432#64,
      BitVec.ofNat 64 (encodeRecordPrev1Mem G sess enc).length,
      sf_6.readReg64 (Reg.gpr 0#5), [0x0a#8]⟩
  have hFit_ev : FitsEnv M lim
      (M.stepEvents (rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1)
        (M.stepEvents w_2 (M.stepEvents w st)))
      (EncodeVarintEnv evGhost) :=
    fitsEnv_encodeVarint_of_spare _ evGhost hspare_ev
  wp_call hev (evGhost,
    M.stepEvents (rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1)
      (M.stepEvents w_2 (M.stepEvents w st)))
  have hevs_ev_nil : _ = ([] : List AllocEvent) :=
    eq_nil_of_encodeVarintEnv (x := evGhost) hspare_ev (by assumption)
  rw [hevs_ev_nil] at *
  simp only [AllocCostModel.stepEvents_nil] at *
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 14); · assumption
  wp_seg_sync52 hseg52 (lsmpl.base 14)
  wp_done_call52 hcl10
  have hraw_lt_w :
      ([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length +
        (encSessionMem w_1 sess).length < 2 ^ 32 := by
    rw [heq_encF sess rfl]; exact hraw_lt_G
  have hwcap_eq : w_5 = BitVec.ofNat 64 (encodeRecordPrev1Mem G sess enc).length := by
    have hN_bv : (BitVec.ofNat 64 (encodeRecordPrev1Mem G sess enc).length).toNat =
        (encodeRecordPrev1Mem G sess enc).length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hsp2 : 1 + (encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length ≤
        (encodeRecordPrev1Mem G sess enc).length := by
      simpa only [List.length_cons, List.length_nil, hN_bv] using hspare_ev
    dsimp only [evGhost, List.length_cons, List.length_nil] at *
    tauto
  rw [hwcap_eq]
  have hraw_spare_w :
      ([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length +
        (encSessionMem w_1 sess).length ≤
        (BitVec.ofNat 64 (encodeRecordPrev1Mem G sess enc).length).toNat :=
    encodeRaw_spare_prev1 (heq_encF sess rfl) hN_lt
  let rawGhost : EncodeRawGhost :=
    ⟨s0.sp - 776#64, w_1, sess, s0.sp - 432#64,
      BitVec.ofNat 64 (encodeRecordPrev1Mem G sess enc).length,
      w_6, [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)⟩
  wp_call hraw rawGhost
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  conv => arg 4; dsimp only [rawGhost]; simp only [List.cons_append, List.nil_append]
  rw [lenField_one_cons_eqX (heq_encF sess rfl)]
  wp_seg_sync52 hseg52 ((blkPl_52).base + bv% (444))
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm]; assumption)
  refine k5_fold_q_placed A q' capE ptrE enc (by sep_frame) ?_
  have hspare_f2 := serField2_spare_prev1 G sess enc hN_lt
  have hFit_f2 : FitsEnv M lim
      (M.stepEvents (rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1)
        (M.stepEvents w_2 (M.stepEvents w st)))
      (SerField2Env (BitVec.ofNat 64 (encodeRecordPrev1Mem G sess enc).length)
        (lenField 1 (encSessionMem G sess)) enc) :=
    fitsEnv_serField2_of_spare _ hspare_f2
  refine hF2 s0.sp q' (BitVec.ofNat 64 (encodeRecordPrev1Mem G sess enc).length) w_6 capE ptrE
    (lenField 1 (encSessionMem G sess)) enc
    (M.stepEvents (rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1)
      (M.stepEvents w_2 (M.stepEvents w st)))
    (s0 := s0) hrec_len hFit_f2
    (by k5_side) (by k5_side) (by k5_side)
    (beq_iff_eq.mp hsp_align) (by k5_side) (by k5_side) (by k5_side) (by sep_frame) ?_
  intro sm cap' ptr' evs5 h5_env hpc_m hrun_m hsp_m htr_m hsv_m
  have hevs5_nil : evs5 = [] := (serField2Env_of_spare hspare_f2).mp h5_env
  rw [hevs5_nil] at *
  simp only [AllocCostModel.stepEvents_nil] at *
  obtain ⟨hsv19, hsv23, hsv24, hsv28, hsvfp, hsvv⟩ := hsv_m
  refine SepWPpLsCl.weaken_pre ?_
    (hTail out q' capE ptrE cap' ptr' v_stk_15 v_stk_14 v_stk_13 v_stk_12
      (encodeRecordPrev1Mem G sess enc) enc w_1 sess
      (M.stepEvents (rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1)
        (M.stepEvents w_2 (M.stepEvents w st)))
      (s0 := s0) (sm := sm)
      (Fx := prevVecAt A.repAlloc self prevCap prevPtr [enc] ∗
        sessionStateReprAt A.repAlloc (self + 24#64) G sess)
      ?_ (beq_iff_eq.mp hsp_align) hpc_m hrun_m hsp_m htr_m
      (by rw [hsv19]; k5_side) (by rw [hsv23]; k5_side) (by rw [hsv24]; k5_side)
      (by rw [hsvv]; k5_side))
  · unfold serSavedCells encodeRecordPrev1Mem
    exact entails_of_sep_focus (by sep_frame)
  · intro sf evs_tail htr_f hsp_f hcs_f hfree_tail
    refine ⟨fun hm => ?_, hsp_f, hcs_f⟩
    simp only [← AllocCostModel.stepEvents_append] at hm
    have hEnv_final : SerializePrev1Env G sess enc
        (((w ++ w_2) ++ rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1) ++ evs_tail) :=
      SerializePrev1Env.of_steps h1_env h2_eq rfl hfree_tail
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨((w ++ w_2) ++ rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1) ++ evs_tail,
      ?_⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    exact Entails.pure_right ⟨htr_f, hEnv_final⟩ (Entails.of_eq (by sep_ac_rfl))

theorem serializePrev1Body_seqFree_placed_ok_withEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hClone : SessionCloneSegPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H)
    (hK1 : VecVecClone1PlacedOkStmt M A lim H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    SerializePrev1BodyPlacedOkStmt M A lim H :=
  serializePrev1Body_seqFree_placed_ok hC hClone hEV hRaw hK1
    (serField2_placed_step hC hDR hEV)
    (serPrev1Tail_placed_ok hC hDrop)

end SeqFree

end Placed

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyPlacedBudget
