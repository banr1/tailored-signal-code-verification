/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodySomeX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneX

/-!
# Budget-Threaded `SessionRecord::serialize` `Some` Branch (Block `52`)

Defines the `Some`-branch allocation envelope `SerializeSomeAllocEnv` and verifies relocatable
`SessionRecord::serialize` (Block `52`) on a `SessionRecord` with an active session
(`serializeSomeSpecX M A lim`) under `FitsEnv M lim st (SerializeSomeAllocEnv x.G x.sess)`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodySomeXBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded
  lsmpl withLsCodeLoaded withLsCl sepWP_seq_lscl
  lsρ lsRustAllocSym lsRustNoAllocShimSym lsMemcpySym
)
open CryptoVerification.RustHeap (vecHeader vecU8)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalPublicApiRepr (sessionStateReprAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost okTagVec sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoVerification.E2E.Record (lenField)
open CryptoVerification.E2E.Record.Placed (lsProg_52 blkPl_52 blkLib_eq_52)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open CryptoVerification.E2E.Record.Serialization (encSessionMem EncodeRawGhost)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux (
  sessionAt_unpack_head_tail sessionAt_pack_head_tail repack_frame_368
  bytes336_to_w012 lenField_one_bounds sessionAt_entails_sessionStateAt
  cells_12_pack serialize_varintLen_eq serialize_varintLen_bvShift_eq lenField_one_bv_eq
)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX (
  SerializeSomeGhostX
  sepWP_exists_left_sepX sepWP_pure_left_sepX vecU8_from_out_cellsX
  sessionAt_pack_776X sessionAt_unpack_800X memRegion_out32_stack_someX
  repack_stack_some_cellsX memRegion_split_init_byteX vecU8At_unpack_cells_432X
  lenField_one_bv_toNatX cap_lt_not_noneCapX bv64_ult_zeroX lenField_one_branch_condsX
  vecU8At_init_byte_432X lenField_one_cons_eqX
)
open LibsignalBinary.Heap (
  VmPreserved AllocCallPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  RustLayoutOk FitsEvents FitsEnv SeqEnv FreeOnlyEvs fitsEvents_append
  rustAllocEvents
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (
  BoundedRustEvs SessionCloneEnv EncodeRawEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (
  EncodeVarintEnv encodeVarintEvents_of_spare
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  serializeStackX SerContractsXPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  EncodeVarintPlacedOkX SessionClonePlacedOkX EncodeRawPlacedOkX
  DropSessionStructureLocal1PlacedOkX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget (
  vecVecCloneSubSpecX sessionLenSubSpecX sessionCloneSubSpecX
  encodeVarintSubSpecX encodeRawSubSpecX dropLocal1SubSpecX
  rustAllocNoOomSubSpecX shimSubSpecX memcpySubSpecX
  vecVecClone_placed_sub_clX sessionLen_placed_sub_clX sessionClone_placed_sub_clX
  encodeVarint_placed_sub_clX encodeRaw_placed_sub_clX dropLocal1_placed_sub_clX
  allocNoOom_placed_sub_clX shim_placed_sub_clX memcpy_placed_sub_clX
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

/-! ## Allocation envelope and specification -/

/-- Allocation-only prefix envelope for `SessionRecord::serialize` (`Some` branch), equal to
    `DefsBudget.SerializeEnv g r` whenever `g.cur = some G` and `r.currentSession = some sess`. -/
def SerializeSomeAllocEnv (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  let encLen := (lenField 1 (encSessionMem G sess)).length
  BoundedRustEvs (8 * encLen + 128) (256 * (encLen + 16)) evs

/-- Budget-threaded specification of `SessionRecord::serialize` on a record with a current session
    (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under `FitsEnv M lim st (SerializeSomeAllocEnv x.G x.sess)`). -/
def serializeSomeSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SerializeSomeGhostX × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧
      (lenField 1 (encSessionMem x.G x.sess)).length < 2 ^ 32 ∧
      FitsEnv M lim st (SerializeSomeAllocEnv x.G x.sess)⌝ ∗
      ((x.self + 8#64) ↦₆₄ x.prevPtr) ∗ ((x.self + 16#64) ↦₆₄ 0#64) ∗
      sessionStateReprAt A.repAlloc (x.self + 24#64) x.G x.sess ∗
      A.pool lim st s ∗ memRegion x.out 32 ∗ stackAt s.sp serializeStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ SeqEnv (SerializeSomeAllocEnv x.G x.sess) FreeOnlyEvs evs⌝ ∗
      ((x.self + 8#64) ↦₆₄ x.prevPtr) ∗ ((x.self + 16#64) ↦₆₄ 0#64) ∗
      sessionStateReprAt A.repAlloc (x.self + 24#64) x.G x.sess ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A.repAlloc (x.out + 8#64) (lenField 1 (encSessionMem x.G x.sess)) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeStackX

/-! ## Envelope inclusion and per-call `FitsEnv` projections -/

private theorem len_le_lenField_one (bs : List (BitVec 8)) :
    bs.length ≤ (lenField 1 bs).length := by
  simp only [lenField, List.length_append]
  omega

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

private theorem fitsEnv_sessionClone_of_someAlloc {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {G : SessionGhost} {sess : Session (List (BitVec 8))}
    (hFit : FitsEnv M lim st (SerializeSomeAllocEnv G sess)) :
    FitsEnv M lim st (SessionCloneEnv G sess) := by
  refine FitsEnv.mono (fun evs h => ?_) hFit
  have hle := len_le_lenField_one (encSessionMem G sess)
  exact BoundedRustEvs.mono (by omega) (by omega) h

private theorem fitsEvents_alloc_of_someAlloc {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {evs1 : List AllocEvent}
    (hFit : FitsEnv M lim st (SerializeSomeAllocEnv G sess))
    (h1 : SessionCloneEnv G sess evs1)
    (hpos : 0 < (lenField 1 (encSessionMem G sess)).length)
    (hlt : (lenField 1 (encSessionMem G sess)).length < 2 ^ 32) :
    FitsEvents M lim (M.stepEvents evs1 st)
      (rustAllocEvents (lenField 1 (encSessionMem G sess)).length 1) := by
  let encLen := (lenField 1 (encSessionMem G sess)).length
  have hall : SerializeSomeAllocEnv G sess (evs1 ++ rustAllocEvents encLen 1) := by
    have h2 := boundedRustEvs_rustAllocEvents_one encLen hpos hlt
    have hle := len_le_lenField_one (encSessionMem G sess)
    exact BoundedRustEvs.mono (by omega) (by omega) (h1.append h2)
  exact ((fitsEvents_append M lim evs1 (rustAllocEvents encLen 1) st).mp (hFit _ hall)).2

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

private theorem serializeSomeAllocEnv_of_parts
    {G w : SessionGhost} {sess : Session (List (BitVec 8))}
    {ss v ptr : BitVec 64}
    {evs1 evs4 : List AllocEvent}
    (heq : encSessionMem w sess = encSessionMem G sess)
    (hpos : 0 < (lenField 1 (encSessionMem G sess)).length)
    (hlt : (lenField 1 (encSessionMem G sess)).length < 2 ^ 32)
    (h1 : SessionCloneEnv G sess evs1)
    (h4 : EncodeRawEnv ⟨ss, w, sess, v,
      BitVec.ofNat 64 (lenField 1 (encSessionMem G sess)).length, ptr,
      [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)⟩ evs4) :
    SerializeSomeAllocEnv G sess
      (evs1 ++ rustAllocEvents (lenField 1 (encSessionMem G sess)).length 1 ++ evs4) := by
  let encLen := (lenField 1 (encSessionMem G sess)).length
  have h2 := boundedRustEvs_rustAllocEvents_one encLen hpos hlt
  have hout : ([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length +
      (encSessionMem w sess).length = encLen := by
    have hcons := congrArg List.length (lenField_one_cons_eqX heq)
    simp only [List.length_cons, List.length_nil, List.length_append] at hcons ⊢
    omega
  have hcap : (BitVec.ofNat 64 encLen).toNat = encLen := lenField_one_bv_toNatX hlt
  dsimp only [EncodeRawEnv] at h4
  rw [hout, hcap] at h4
  have hle := len_le_lenField_one (encSessionMem G sess)
  exact BoundedRustEvs.mono (by omega) (by omega) ((h1.append h2).append h4)

private theorem fitsEnv_encodeRaw_of_someAlloc {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {G w : SessionGhost} {sess : Session (List (BitVec 8))}
    {ss v ptr : BitVec 64} {evs1 : List AllocEvent}
    (hFit : FitsEnv M lim st (SerializeSomeAllocEnv G sess))
    (heq : encSessionMem w sess = encSessionMem G sess)
    (hpos : 0 < (lenField 1 (encSessionMem G sess)).length)
    (hlt : (lenField 1 (encSessionMem G sess)).length < 2 ^ 32)
    (h1 : SessionCloneEnv G sess evs1) :
    FitsEnv M lim
      (M.stepEvents (rustAllocEvents (lenField 1 (encSessionMem G sess)).length 1)
        (M.stepEvents evs1 st))
      (EncodeRawEnv ⟨ss, w, sess, v,
        BitVec.ofNat 64 (lenField 1 (encSessionMem G sess)).length, ptr,
        [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)⟩) := by
  intro evs4 h4
  have hall := serializeSomeAllocEnv_of_parts heq hpos hlt h1 h4
  have hf := hFit _ hall
  rw [fitsEvents_append, fitsEvents_append, AllocCostModel.stepEvents_append] at hf
  exact hf.2

private theorem eq_nil_of_encodeVarintEnv {x : EncodeVarintGhost} {evs : List AllocEvent}
    (hspare : x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat)
    (hevs : EncodeVarintEnv x evs) : evs = [] :=
  hevs.trans (encodeVarintEvents_of_spare hspare)

/-! ## Relocatable `[LibsignalPlacement]` proof (Block `52`) -/

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
theorem serialize_some_placed_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hClone : SessionClonePlacedOkX M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hRaw : EncodeRawPlacedOkX M A lim H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializeSomeSpecX M A lim)) := by
  have hmemcpy := memcpy_placed_sub_clX (callerProg := lsProg_52 H) hC
  have hshim := shim_placed_sub_clX (callerProg := lsProg_52 H) hC
  have halloc := allocNoOom_placed_sub_clX (callerProg := lsProg_52 H) hC
  have hclone := sessionClone_placed_sub_clX (callerProg := lsProg_52 H) hClone
  have hvv := vecVecClone_placed_sub_clX (callerProg := lsProg_52 H)
  have hlen := sessionLen_placed_sub_clX A.repAlloc (callerProg := lsProg_52 H)
  have hev := encodeVarint_placed_sub_clX (callerProg := lsProg_52 H) hEV
  have hraw := encodeRaw_placed_sub_clX (callerProg := lsProg_52 H) hRaw
  have hdrop := dropLocal1_placed_sub_clX (callerProg := lsProg_52 H) hDrop
  change subroutine_ok (lsProg_52 H) (lsρ lsMemcpySym) (withLsCl lsmpl memcpySubSpecX) at hmemcpy
  change subroutine_ok (lsProg_52 H) (lsρ lsRustNoAllocShimSym) (withLsCl lsmpl shimSubSpecX) at hshim
  change subroutine_ok (lsProg_52 H) (lsρ lsRustAllocSym)
    (withLsCl lsmpl (rustAllocNoOomSubSpecX M A lim)) at halloc
  change subroutine_ok (lsProg_52 H) (lsmpl.base 80)
    (withLsCl lsmpl (sessionCloneSubSpecX M A lim)) at hclone
  change subroutine_ok (lsProg_52 H) (lsmpl.base 117)
    (withLsCl lsmpl vecVecCloneSubSpecX) at hvv
  change subroutine_ok (lsProg_52 H) (lsmpl.base 86)
    (withLsCl lsmpl (sessionLenSubSpecX A.repAlloc)) at hlen
  change subroutine_ok (lsProg_52 H) (lsmpl.base 10)
    (withLsCl lsmpl (encodeVarintSubSpecX M A lim)) at hev
  change subroutine_ok (lsProg_52 H) (lsmpl.base 14)
    (withLsCl lsmpl (encodeRawSubSpecX M A lim)) at hraw
  change subroutine_ok (lsProg_52 H) (lsmpl.base 6)
    (withLsCl lsmpl (dropLocal1SubSpecX M A lim)) at hdrop
  dsimp only [withLsCl, memcpySubSpecX, shimSubSpecX, rustAllocNoOomSubSpecX,
    sessionCloneSubSpecX, vecVecCloneSubSpecX, sessionLenSubSpecX,
    encodeVarintSubSpecX, encodeRawSubSpecX, dropLocal1SubSpecX]
    at hmemcpy hshim halloc hclone hvv hlen hev hraw hdrop
  unfold withLsCodeLoaded serializeSomeSpecX
  simp only [okTagVec, memRegion_out32_stack_someX,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init x s0
  obtain ⟨⟨self, out, prevPtr, G, sess⟩, st⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_bounds_G : (lenField 1 (encSessionMem G sess)).length < 2 ^ 32 := by assumption
  have hFit0 : FitsEnv M lim st (SerializeSomeAllocEnv G sess) := by assumption
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
  have hFit_clone := fitsEnv_sessionClone_of_someAlloc hFit0
  wp_call hclone (⟨s0.sp - 800#64, self + 24#64, G, sess⟩, st)
  have h1_env : SessionCloneEnv G sess w := by assumption
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
  have hFit_alloc :=
    fitsEvents_alloc_of_someAlloc hFit0 h1_env hsz_pos hlen_bounds_G
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
  have hraw_lt_w :
      ([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length +
        (encSessionMem w_1 sess).length < 2 ^ 32 := by
    rw [heq_encF sess rfl]; exact hraw_lt_G
  let rawGhost : EncodeRawGhost :=
    ⟨s0.sp - 776#64, w_1, sess, s0.sp - 432#64,
      BitVec.ofNat 64 (lenField 1 (encSessionMem G sess)).length,
      w_4, [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)⟩
  have hFit_raw : FitsEnv M lim
      (M.stepEvents (rustAllocEvents (lenField 1 (encSessionMem G sess)).length 1) (M.stepEvents w st))
      (EncodeRawEnv rawGhost) :=
    fitsEnv_encodeRaw_of_someAlloc (ss := s0.sp - 776#64) (v := s0.sp - 432#64) (ptr := w_4)
      hFit0 (heq_encF sess rfl) hsz_pos hlen_bounds_G h1_env
  have hw3_eq : w_3 = BitVec.ofNat 64 (lenField 1 (encSessionMem G sess)).length := by
    have hsp1 := hspare_ev
    have hsp2 : 1 + (encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length ≤
        (lenField 1 (encSessionMem G sess)).length := by
      simpa only [List.length_cons, List.length_nil, hcap_toNat_G] using hspare_ev
    dsimp only [evGhost, List.length_cons, List.length_nil] at *
    tauto
  rw [hw3_eq]
  wp_call hraw (rawGhost,
    M.stepEvents (rustAllocEvents (lenField 1 (encSessionMem G sess)).length 1) (M.stepEvents w st))
  have h4_env : EncodeRawEnv rawGhost w_5 := by assumption
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 6); · assumption
  conv => arg 4; dsimp only [rawGhost]; simp only [List.cons_append, List.nil_append]
  rw [lenField_one_cons_eqX (heq_encF sess rfl), vecU8At_unpack_cells_432X]
  wp_seg_sync hseg52 (lsmpl.base 6)
  refine SepWP.fold (sessionAt_entails_sessionStateAt A.repAlloc (s0.sp - 776#64) w_1 sess)
    (by sep_frame) ?_
  wp_done_call hcl11
  wp_call hdrop (⟨s0.sp - 776#64, w_1, sess.state⟩,
    M.stepEvents w_5
      (M.stepEvents (rustAllocEvents (lenField 1 (encSessionMem G sess)).length 1) (M.stepEvents w st)))
  wp_steps_sync_pool (s0.readReg64 .lr)
  refine SepWP.fold
    (vecU8_from_out_cellsX A.repAlloc out _ _ (lenField 1 (encSessionMem G sess)))
    (by sep_frame) ?_
  refine SepWP.fold (cells_12_pack s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_frame) ?_
  conv => arg 4; conv in (stackAt _ _) => arg 1; simp only [arm64_norm, *]
  refine SepWP.fold (repack_stack_some_cellsX s0.sp _ _ _) (by sep_frame) ?_
  conv => arg 4; simp only [← AllocCostModel.stepEvents_append]
  have hEnv_final :=
    SeqEnv.append (E₂ := FreeOnlyEvs)
      (serializeSomeAllocEnv_of_parts (ss := s0.sp - 776#64) (v := s0.sp - 432#64) (ptr := w_4)
        (heq_encF sess rfl) hsz_pos hlen_bounds_G h1_env h4_env)
      (by assumption)
  simp only [List.append_assoc] at hEnv_final
  wp_done

end Placed

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodySomeXBudget
