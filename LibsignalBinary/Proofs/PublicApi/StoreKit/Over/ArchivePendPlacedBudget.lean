/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePendPlaced
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodySomeX
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Entry Prefix and Pending-Key Clearing

Total-correctness (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`) `SepWP` and `SepWPpLsCl` prefix theorems
for `archive_current_state_inner` on Block `51` (`lsProg_51 H`) from entry through pending/Kyber
deallocations (`FreeOnlyEvs`), `NoOom` `__rust_alloc`, and pre-reserved 0-allocation `encode_raw`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePendPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded
  lsmpl withLsCl sepWP_seq_lscl
  lsρ lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsMemcpySym
  lsProg_51 blkPl_51 blkLib_eq_51
)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalPublicApiRepr (sessionStateReprAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.E2E.Record.Serialization (encSessionMem)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX (
  serializeSubStackX sepWP_exists_left_sepX sepWP_pure_left_sepX cap_lt_not_noneCapX
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  clearPendingGhost clearPending optTailCap
  archiveShimCutOff archiveEncodeRawCutOff
  cap_slt_conds_of_true cap_slt_conds_of_false
  heap_split_tt heap_split_tf heap_split_ft heap_split_ff
  sessionAt_unpack_rec_genX bs336_split_gen bytes448_split_genX
  sessionAt_pack_456_clearX encSessionMem_length_pos vecU8At_nil_88X
)
open Proofs.libsignal.Hooks2 (SepWPpLsCl)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  RustLayoutOk FitsEvents FitsEnv SeqEnv FreeOnlyEvs
  rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomSpecWithStack rustCliDeallocBudgetExternSpecWithStack
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerContractsXPlaced)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget (ArchiveCoreEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (
  ArchiveOverGenPlacedOk PromoteStateOverGenPlacedOk
  ArchiveOverPlacedOkX PromoteStateOverPlacedOkX
  encodeRawPreallocSpecX EncodeRawPreallocPlacedOkX encodeRawPreallocSubSpecX
  encodeRawPrealloc_placed_sub_okX encodeRawPrealloc_placed_sub_clX
  rustDeallocSubSpecX dealloc_arch_placed_okX dealloc_arch_placed_clX
  sessionLenSubSpecX rustAllocNoOomSubSpecX shimSubSpecX memcpySubSpecX
  sessionLen_placed_sub_clX allocNoOom_placed_sub_clX
  shim_placed_sub_clX memcpy_placed_sub_clX
  freeOnlyEvs_rustDealloc
  fitsEvents_allocEnc_of_archiveCoreEnv fitsEnv_growTail_of_archiveCoreEnv
  fitsEvents_growOneZero_of_archiveCoreEnv fitsEnv_growOneZero_of_archiveCoreEnv
  archiveCoreEnv_of_parts archiveCoreEnv_zero_of_parts archiveCoreEnv_nonzero_of_parts
)

/-! ## Re-Exports from `ArchiveAuxBudget` -/

export LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (
  ArchiveOverGenPlacedOk PromoteStateOverGenPlacedOk
  ArchiveOverPlacedOkX PromoteStateOverPlacedOkX
  encodeRawPreallocSpecX EncodeRawPreallocPlacedOkX encodeRawPreallocSubSpecX
  encodeRawPrealloc_placed_sub_okX encodeRawPrealloc_placed_sub_clX
  rustDeallocSubSpecX dealloc_arch_placed_okX dealloc_arch_placed_clX
  growOneBudgetCondSubSpecX growOneNoOomSubSpecX growOneSubSpecX
  growOneCond_arch_placed_clX growOneCond_arch_placed_okX
  growOneNoOom_arch_placed_okX growOneNoOom_arch_placed_clX
  growOne_arch_placed_okX growOne_arch_placed_clX
  freeOnlyEvs_rustDealloc
  fitsEvents_allocEnc_of_archiveCoreEnv fitsEnv_growTail_of_archiveCoreEnv
  fitsEvents_growOneZero_of_archiveCoreEnv fitsEnv_growOneZero_of_archiveCoreEnv
  archiveCoreEnv_of_parts archiveCoreEnv_zero_of_parts archiveCoreEnv_nonzero_of_parts
)

private theorem bv_sub_add_lit_local (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

private theorem memRegion_eq_of_len {p : BitVec 64} {n : Nat} {bs : List (BitVec 8)}
    (h : bs.length = n) : memRegion p n = memRegion p bs.length := by
  rw [h]

private theorem sepWP_eq_pre {prog : Program} {target : BitVec 64} {s : State}
    {P1 P2 : SepProp} {post : State → SepProp → Prop}
    (heq : P1 = P2) (h : SepWP prog target s P2 post) :
    SepWP prog target s P1 post :=
  heq ▸ h

private theorem freeOnlyEvs_nil : FreeOnlyEvs [] :=
  fun _ h => nomatch h

private theorem freeOnlyEvs_append {e1 e2 : List AllocEvent}
    (h1 : FreeOnlyEvs e1) (h2 : FreeOnlyEvs e2) :
    FreeOnlyEvs (e1 ++ e2) := by
  intro ev hev
  rcases List.mem_append.mp hev with hm1 | hm2
  · exact h1 ev hm1
  · exact h2 ev hm2

private theorem spAligned_of_sub_464 {s0 s2 : State}
    (halign0 : s0.spAligned = true) (hsp2 : s2.sp = s0.sp - 464#64) :
    s2.spAligned = true := by
  unfold State.spAligned at halign0 ⊢
  rw [hsp2, beq_iff_eq] at *
  have h0 : (s0.sp &&& 15#64).toNat = 0 := congrArg BitVec.toNat halign0
  rw [BitVec.toNat_and, show (15#64 : BitVec 64).toNat = 2 ^ 4 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod] at h0
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (15#64 : BitVec 64).toNat = 2 ^ 4 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit_local BitVec.toNat_zero

/-! ## Budget-Threaded Midpoint Spatial Predicates -/

/-- Budget-threaded spatial state right after `bl __rust_no_alloc_shim_is_unstable_v2` in
    `archive_current_state_inner`. -/
def archiveMidShimPre {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (sf s0 : State)
    (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (bs336 : List (BitVec 8))
    (c0 c1 c2 c3 v464 : BitVec 64) (v112 : BitVec 128)
    (Fprev : SepProp) : SepProp :=
  stackAt (s0.sp - 464#64) serializeSubStackX ∗
    sessionStateReprAt A.repAlloc (s0.sp - 456#64) (clearPendingGhost G) (clearPending sess) ∗
    ((recPtr + 32#64) ↦ₛ bs336) ∗
    ((recPtr + 24#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    (recPtr ↦₆₄ prevCap) ∗
    ((recPtr + 8#64) ↦₆₄ prevPtr) ∗
    ((recPtr + 16#64) ↦₆₄ 0#64) ∗
    A.pool lim st sf ∗
    ((s0.sp - 464#64) ↦₆₄ v464) ∗
    ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
    ((s0.sp - 96#64) ↦₆₄ c0) ∗
    ((s0.sp - 88#64) ↦₆₄ c1) ∗
    ((s0.sp - 80#64) ↦₆₄ c2) ∗
    ((s0.sp - 72#64) ↦₆₄ c3) ∗
    ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗
    ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x28) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
    Fprev

/-- Budget-threaded spatial state right after `bl encode_raw` in `archive_current_state_inner`. -/
def archiveMidRawPre {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (sf s0 : State)
    (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (bs336 : List (BitVec 8))
    (capEnc ptrEnc c0 v464 : BitVec 64) (v112 : BitVec 128)
    (Fprev : SepProp) : SepProp :=
  stackAt (s0.sp - 464#64) serializeSubStackX ∗
    vecU8At A.repAlloc (s0.sp - 88#64) capEnc ptrEnc
      (encSessionMem (clearPendingGhost G) (clearPending sess)) ∗
    sessionStateReprAt A.repAlloc (s0.sp - 456#64) (clearPendingGhost G) (clearPending sess) ∗
    ((recPtr + 32#64) ↦ₛ bs336) ∗
    ((recPtr + 24#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    (recPtr ↦₆₄ prevCap) ∗
    ((recPtr + 8#64) ↦₆₄ prevPtr) ∗
    ((recPtr + 16#64) ↦₆₄ 0#64) ∗
    A.pool lim st sf ∗
    ((s0.sp - 464#64) ↦₆₄ v464) ∗
    ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
    ((s0.sp - 96#64) ↦₆₄ c0) ∗
    ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗
    ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x28) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
    Fprev

/-! ## Entry to Allocator-Shim Return (Block `51`) -/

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
/-- Total-correctness `SepWP` prefix of `archive_current_state_inner` (Block `51`) from function
    entry through `bl __rust_no_alloc_shim_is_unstable_v2` across all 4 `(pending, kyber)` niche
    branches, emitting `evs1` with `FreeOnlyEvs evs1`. -/
theorem archive_clear_to_shim_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (st : M.σ)
    (Fprev : SepProp)
    (s0 : State)
    (target : BitVec 64)
    (post : State → SepProp → Prop)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_51).base)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = recPtr)
    (hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 : BitVec 64) (v112 : BitVec 128)
    (hcont : ∀ (sf : State) (evs1 : List AllocEvent) (bs336 : List (BitVec 8)),
      FreeOnlyEvs evs1 →
      bs336.length = 336 →
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_51).base + (archiveShimCutOff + 4#64) →
      sf.status = .Running →
      sf.sp = s0.sp - 464#64 →
      sf.trace = s0.trace →
      sf.readReg64 .x19 = recPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length →
      sf.readReg64 .x23 = 0#64 →
      sf.readReg64 .x24 = s0.readReg64 .x24 →
      sf.readReg64 .x25 = s0.readReg64 .x25 →
      sf.readReg64 .x26 = s0.readReg64 .x26 →
      sf.readReg64 .x27 = s0.readReg64 .x27 →
      sf.readReg64 .x28 = s0.readReg64 .x28 →
      sf.readReg64 .x29 = s0.sp - 64#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWP (lsProg_51 H) target sf
        (archiveMidShimPre A lim (M.stepEvents evs1 st) sf s0 recPtr prevCap prevPtr G sess bs336
          c0 c1 c2 c3 v464 v112 Fprev)
        post) :
    SepWP (lsProg_51 H) target s0
      ((recPtr ↦₆₄ prevCap) ∗ ((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 0#64) ∗
        sessionStateReprAt A.repAlloc (recPtr + 0x18#64) G sess ∗ A.pool lim st s0 ∗
        stackAt (s0.sp - 464#64) serializeSubStackX ∗
        ((s0.sp - 464#64) ↦₆₄ v464) ∗ ((s0.sp - 456#64) ↦₆₄ v456) ∗
        memRegion (s0.sp - 448#64) 336 ∗ ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
        ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
        ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
        ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
        ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
        ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
        ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗ Fprev)
      post := by
  have hmemcpy := memcpy_placed_sub_clX (callerProg := lsProg_51 H) hC
  have hdealloc := dealloc_arch_placed_clX (callerProg := lsProg_51 H) hC
  have hshim := shim_placed_sub_clX (callerProg := lsProg_51 H) hC
  have hlen := sessionLen_placed_sub_clX A.repAlloc (callerProg := lsProg_51 H)
  change subroutine_ok (lsProg_51 H) (lsρ lsMemcpySym) (withLsCl lsmpl memcpySubSpecX) at hmemcpy
  change subroutine_ok (lsProg_51 H) (lsρ lsRustDeallocSym)
    (withLsCl lsmpl (rustDeallocSubSpecX M A lim)) at hdealloc
  change subroutine_ok (lsProg_51 H) (lsρ lsRustNoAllocShimSym) (withLsCl lsmpl shimSubSpecX) at hshim
  change subroutine_ok (lsProg_51 H) (lsmpl.base 86)
    (withLsCl lsmpl (sessionLenSubSpecX A.repAlloc)) at hlen
  dsimp only [withLsCl, memcpySubSpecX, rustDeallocSubSpecX,
    rustCliDeallocBudgetExternSpecWithStack,
    _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
    shimSubSpecX, sessionLenSubSpecX]
    at hmemcpy hdealloc hshim hlen
  have hseg51 := fun {mid tgt : BitVec 64} {s : State} {Pre : SepProp}
      {post' : State → SepProp → Prop} {oom : State → SepProp} =>
    sepWP_seg_ls_vm (prog := lsProg_51 H) (Q := lsProg_51 (hooksException H))
      blkLib_eq_51 (by rfl) (mid := mid) (target := tgt) (s := s) (Pre := Pre)
      (post := post') (oom := oom)
  apply sepWP_seq_lscl hcl0 (mid := lsρ lsMemcpySym)
  refine SepWP.fold (sessionAt_unpack_rec_genX A.repAlloc recPtr G sess) (by sep_focus) ?_
  apply sepWP_exists_left_sepX; intro bs336
  apply sepWP_pure_left_sepX; rintro ⟨hbs336, hcap, hinl⟩
  have hcmn : (G.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCapX hcap
  wp_seg_sync hseg51 (lsρ lsMemcpySym)
  wp_done_call hcl1
  rw [memRegion_eq_of_len hbs336]
  wp_call hmemcpy (s0.sp - 448#64, recPtr + 32#64, bs336)
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  obtain ⟨a, pPtr, pRest, kPtr, kTail, ha, hpRest, _hkTail, hbs_eq, hinl', hheap⟩ :=
    bs336_split_gen A.repAlloc hinl
  have hsplit448 : ((s0.sp - 448#64) ↦ₛ bs336) ⊢
      (((s0.sp - 448#64) ↦ₛ a) ∗
        ((s0.sp - 208#64) ↦₆₄ optTailCap G.pending) ∗ ((s0.sp - 200#64) ↦₆₄ pPtr) ∗
        ((s0.sp - 192#64) ↦ₛ pRest) ∗
        ((s0.sp - 160#64) ↦₆₄ optTailCap G.kyber) ∗ ((s0.sp - 152#64) ↦₆₄ kPtr) ∗
        ((s0.sp - 144#64) ↦ₛ kTail)) := by
    rw [hbs_eq, bytes448_split_genX s0.sp a pRest kTail _ _ _ _ ha hpRest]
    exact Entails.refl _
  have hpack_clear := sessionAt_pack_456_clearX A.repAlloc s0.sp G sess ha hpRest hinl'
  have hn_pos : 0 < (encSessionMem (clearPendingGhost G) (clearPending sess)).length :=
    encSessionMem_length_pos _ _
  have hlen_enc' : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 4294967296 :=
    hlen_enc
  have hn_toNat : (BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length).toNat =
      (encSessionMem (clearPendingGhost G) (clearPending sess)).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hn_b63 :
      (BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length).getLsbD 63 = false := by
    rw [BitVec.getLsbD_ofNat]
    simp only [Nat.reduceLT, decide_true, Bool.true_and]
    exact Nat.testBit_lt_two_pow (by omega)
  have hn_ne0 :
      (BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length == 0#64) = false := by
    apply beq_eq_false_iff_ne.mpr; intro heq
    have h1 : (BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length).toNat = 0 :=
      congrArg BitVec.toNat heq
    rw [hn_toNat] at h1; omega
  by_cases hps : (optTailCap G.pending).slt 1#64 = true
  · obtain ⟨hps_gt0, hps_le0, hps_ge1⟩ := cap_slt_conds_of_true hps
    by_cases hks : (optTailCap G.kyber).slt 1#64 = true
    · -- Branch (tt): neither pending nor kyber frees (`evs1 = []`)
      obtain ⟨hks_gt0, hks_le0, hks_ge1⟩ := cap_slt_conds_of_true hks
      apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 86); · assumption
      refine SepWP.fold hsplit448 (by sep_focus) ?_
      refine SepWP.fold (heap_split_tt A.repAlloc hheap hps hks) (by sep_focus) ?_
      wp_seg_sync hseg51 (lsmpl.base 86)
      refine SepWP.fold hpack_clear (by sep_focus) ?_
      wp_done_call hcl_len
      wp_call hlen ⟨s0.sp - 456#64, clearPendingGhost G, clearPending sess⟩
      refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
      apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsRustNoAllocShimSym); · assumption
      wp_seg_sync hseg51 (lsρ lsRustNoAllocShimSym)
      wp_done_call hcl_shim
      wp_call hshim ()
      refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
      have cont_goal := hcont _ [] bs336 freeOnlyEvs_nil hbs336 (by assumption)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*])
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by simp only [*])
      simp only [AllocCostModel.stepEvents_nil] at cont_goal
      refine sepWP_eq_pre ?_ cont_goal
      unfold archiveMidShimPre; sep_ac_rfl
    · -- Branch (tf): kyber frees (`evs1 = rustDeallocEvents (optTailCap G.kyber).toNat 1`)
      have hks' : (optTailCap G.kyber).slt 1#64 = false := Bool.eq_false_iff.mpr hks
      obtain ⟨hks_gt0, hks_le0, hks_ge1⟩ := cap_slt_conds_of_false hks'
      have hsplit_tf := heap_split_tf A.repAlloc hheap hps hks'
      rw [A.repAlloc_live_norm] at hsplit_tf
      apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsRustDeallocSym); · assumption
      refine SepWP.fold hsplit448 (by sep_focus) ?_
      refine SepWP.fold hsplit_tf (by sep_focus) ?_
      apply sepWP_pure_left_sepX; rintro ⟨hk_pos, hk_lt⟩
      wp_seg_sync hseg51 (lsρ lsRustDeallocSym)
      wp_done_call hcl_dk
      have hex_k : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      have hsz_k : (optTailCap G.kyber).toNat + 1 ≤ 2 ^ 63 := by omega
      have hrlay_k : RustLayoutOk (optTailCap G.kyber).toNat 1 :=
        ⟨⟨by omega, hex_k, hsz_k⟩, by decide⟩
      wp_call hdealloc (kPtr, (optTailCap G.kyber).toNat, 1, st)
      apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 86); · assumption
      wp_seg_sync hseg51 (lsmpl.base 86)
      refine SepWP.fold hpack_clear (by sep_focus) ?_
      wp_done_call hcl_len
      wp_call hlen ⟨s0.sp - 456#64, clearPendingGhost G, clearPending sess⟩
      refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
      apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsRustNoAllocShimSym); · assumption
      wp_seg_sync hseg51 (lsρ lsRustNoAllocShimSym)
      wp_done_call hcl_shim
      wp_call hshim ()
      refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
      have cont_goal := hcont _ (rustDeallocEvents (optTailCap G.kyber).toNat 1) bs336
        (freeOnlyEvs_rustDealloc _ _) hbs336 (by assumption)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*])
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by simp only [*])
      refine sepWP_eq_pre ?_ cont_goal
      unfold archiveMidShimPre; sep_ac_rfl
  · have hps' : (optTailCap G.pending).slt 1#64 = false := Bool.eq_false_iff.mpr hps
    obtain ⟨hps_gt0, hps_le0, hps_ge1⟩ := cap_slt_conds_of_false hps'
    by_cases hks : (optTailCap G.kyber).slt 1#64 = true
    · -- Branch (ft): pending frees (`evs1 = rustDeallocEvents (optTailCap G.pending).toNat 1`)
      obtain ⟨hks_gt0, hks_le0, hks_ge1⟩ := cap_slt_conds_of_true hks
      have hsplit_ft := heap_split_ft A.repAlloc hheap hps' hks
      rw [A.repAlloc_live_norm] at hsplit_ft
      apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsRustDeallocSym); · assumption
      refine SepWP.fold hsplit448 (by sep_focus) ?_
      refine SepWP.fold hsplit_ft (by sep_focus) ?_
      apply sepWP_pure_left_sepX; rintro ⟨hp_pos, hp_lt⟩
      wp_seg_sync hseg51 (lsρ lsRustDeallocSym)
      wp_done_call hcl_dp
      have hex_p : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      have hsz_p : (optTailCap G.pending).toNat + 1 ≤ 2 ^ 63 := by omega
      have hrlay_p : RustLayoutOk (optTailCap G.pending).toNat 1 :=
        ⟨⟨by omega, hex_p, hsz_p⟩, by decide⟩
      wp_call hdealloc (pPtr, (optTailCap G.pending).toNat, 1, st)
      apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 86); · assumption
      wp_seg_sync hseg51 (lsmpl.base 86)
      refine SepWP.fold hpack_clear (by sep_focus) ?_
      wp_done_call hcl_len
      wp_call hlen ⟨s0.sp - 456#64, clearPendingGhost G, clearPending sess⟩
      refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
      apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsRustNoAllocShimSym); · assumption
      wp_seg_sync hseg51 (lsρ lsRustNoAllocShimSym)
      wp_done_call hcl_shim
      wp_call hshim ()
      refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
      have cont_goal := hcont _ (rustDeallocEvents (optTailCap G.pending).toNat 1) bs336
        (freeOnlyEvs_rustDealloc _ _) hbs336 (by assumption)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*])
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by simp only [*])
      refine sepWP_eq_pre ?_ cont_goal
      unfold archiveMidShimPre; sep_ac_rfl
    · -- Branch (ff): both pending and kyber free
      have hks' : (optTailCap G.kyber).slt 1#64 = false := Bool.eq_false_iff.mpr hks
      obtain ⟨hks_gt0, hks_le0, hks_ge1⟩ := cap_slt_conds_of_false hks'
      have hsplit_ff := heap_split_ff A.repAlloc hheap hps' hks'
      rw [A.repAlloc_live_norm] at hsplit_ff
      apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsRustDeallocSym); · assumption
      refine SepWP.fold hsplit448 (by sep_focus) ?_
      refine SepWP.fold hsplit_ff (by sep_focus) ?_
      apply sepWP_pure_left_sepX; rintro ⟨⟨hp_pos, hp_lt⟩, ⟨hk_pos, hk_lt⟩⟩
      wp_seg_sync hseg51 (lsρ lsRustDeallocSym)
      wp_done_call hcl_dp
      have hex_p : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      have hsz_p : (optTailCap G.pending).toNat + 1 ≤ 2 ^ 63 := by omega
      have hrlay_p : RustLayoutOk (optTailCap G.pending).toNat 1 :=
        ⟨⟨by omega, hex_p, hsz_p⟩, by decide⟩
      wp_call hdealloc (pPtr, (optTailCap G.pending).toNat, 1, st)
      apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsRustDeallocSym); · assumption
      wp_seg_sync hseg51 (lsρ lsRustDeallocSym)
      wp_done_call hcl_dk
      have hsz_k : (optTailCap G.kyber).toNat + 1 ≤ 2 ^ 63 := by omega
      have hrlay_k : RustLayoutOk (optTailCap G.kyber).toNat 1 :=
        ⟨⟨by omega, hex_p, hsz_k⟩, by decide⟩
      wp_call hdealloc (kPtr, (optTailCap G.kyber).toNat, 1,
        M.stepEvents (rustDeallocEvents (optTailCap G.pending).toNat 1) st)
      apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 86); · assumption
      wp_seg_sync hseg51 (lsmpl.base 86)
      refine SepWP.fold hpack_clear (by sep_focus) ?_
      wp_done_call hcl_len
      wp_call hlen ⟨s0.sp - 456#64, clearPendingGhost G, clearPending sess⟩
      refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
      apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsRustNoAllocShimSym); · assumption
      wp_seg_sync hseg51 (lsρ lsRustNoAllocShimSym)
      wp_done_call hcl_shim
      wp_call hshim ()
      refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
      have cont_goal := hcont _
        (rustDeallocEvents (optTailCap G.pending).toNat 1 ++
          rustDeallocEvents (optTailCap G.kyber).toNat 1)
        bs336
        (freeOnlyEvs_append (freeOnlyEvs_rustDealloc _ _) (freeOnlyEvs_rustDealloc _ _))
        hbs336 (by assumption)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*])
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by simp only [*])
      rw [AllocCostModel.stepEvents_append] at cont_goal
      refine sepWP_eq_pre ?_ cont_goal
      unfold archiveMidShimPre; sep_ac_rfl

/-- `SepWPpLsCl` CPS counterpart of `archive_clear_to_shim_placed_sepWP` (for arbitrary `Q`, `Qp`). -/
theorem archive_clear_to_shim_placed_cps [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (st : M.σ)
    (Fprev : SepProp)
    (s0 : State)
    (Q Qp : State → SepProp → Prop)
    (hpc : s0.pc = (blkPl_51).base)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = recPtr)
    (hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 : BitVec 64) (v112 : BitVec 128)
    (hcont : ∀ (sf : State) (evs1 : List AllocEvent) (bs336 : List (BitVec 8)),
      FreeOnlyEvs evs1 →
      bs336.length = 336 →
      sf.pc = (blkPl_51).base + (archiveShimCutOff + 4#64) →
      sf.status = .Running →
      sf.sp = s0.sp - 464#64 →
      sf.trace = s0.trace →
      sf.readReg64 .x19 = recPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length →
      sf.readReg64 .x23 = 0#64 →
      sf.readReg64 .x24 = s0.readReg64 .x24 →
      sf.readReg64 .x25 = s0.readReg64 .x25 →
      sf.readReg64 .x26 = s0.readReg64 .x26 →
      sf.readReg64 .x27 = s0.readReg64 .x27 →
      sf.readReg64 .x28 = s0.readReg64 .x28 →
      sf.readReg64 .x29 = s0.sp - 64#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPpLsCl lsmpl (lsProg_51 H) (s0.readReg64 .lr) sf
        (archiveMidShimPre A lim (M.stepEvents evs1 st) sf s0 recPtr prevCap prevPtr G sess bs336
          c0 c1 c2 c3 v464 v112 Fprev)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_51 H) (s0.readReg64 .lr) s0
      ((recPtr ↦₆₄ prevCap) ∗ ((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 0#64) ∗
        sessionStateReprAt A.repAlloc (recPtr + 0x18#64) G sess ∗ A.pool lim st s0 ∗
        stackAt (s0.sp - 464#64) serializeSubStackX ∗
        ((s0.sp - 464#64) ↦₆₄ v464) ∗ ((s0.sp - 456#64) ↦₆₄ v456) ∗
        memRegion (s0.sp - 448#64) 336 ∗ ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
        ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
        ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
        ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
        ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
        ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
        ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗ Fprev)
      Q Qp := by
  intro hcl0
  exact SepWPpLsCl.of_sepWP
    (mid := (blkPl_51).base + (archiveShimCutOff + 4#64))
    (archive_clear_to_shim_placed_sepWP hC recPtr prevCap prevPtr G sess st Fprev s0
      ((blkPl_51).base + (archiveShimCutOff + 4#64))
      (fun sm Pm => SepWPpLsCl lsmpl (lsProg_51 H) (s0.readReg64 .lr) sm Pm Q Qp)
      hcl0 hpc hrun hsp_align hx0 hlen_enc
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 v112
      (fun sf evs1 bs336 hf1 hbs336 _hclf hpcsf hrunsf hspsf htrsf
          hx19 hx20 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvr =>
        SepWP.done hpcsf hrunsf
          (hcont sf evs1 bs336 hf1 hbs336 hpcsf hrunsf hspsf htrsf
            hx19 hx20 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvr)))
    hcl0

/-! ## Allocator-Shim Return to `encode_raw` Return -/

set_option maxHeartbeats 800000 in
/-- Pre-reserved (`0`-event `encode_raw`, `EncodeRawPreallocPlacedOkX`) `SepWP` midpoint segment
    from `shim` return through `NoOom` `__rust_alloc` and `encode_raw` return on `lsProg_51 H`
    (Block `51`), matching `ArchiveCoreEnv`. -/
theorem archive_shim_to_raw_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H)
    (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (st1 : M.σ)
    (bs336 : List (BitVec 8))
    (Fprev : SepProp)
    (s0 s2 : State)
    (target : BitVec 64)
    (post : State → SepProp → Prop)
    (hcl2 : LibsignalCodeLoaded lsmpl s2.mem)
    (hsp_align : s0.spAligned = true)
    (hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32)
    (hfit_alloc : FitsEvents M lim st1
      (rustAllocEvents (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1))
    (c0 c1 c2 c3 v464 : BitVec 64) (v112 : BitVec 128)
    (hpc2 : s2.pc = (blkPl_51).base + (archiveShimCutOff + 4#64))
    (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 464#64)
    (htr2 : s2.trace = s0.trace)
    (hx19 : s2.readReg64 .x19 = recPtr)
    (hx20 : s2.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length)
    (hx23 : s2.readReg64 .x23 = 0#64)
    (hx24 : s2.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s2.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s2.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s2.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s2.readReg64 .x28 = s0.readReg64 .x28)
    (hx29 : s2.readReg64 .x29 = s0.sp - 64#64)
    (hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hcont : ∀ (sf : State) (capEnc ptrEnc : BitVec 64),
      capEnc = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length →
      ptrEnc ≠ 0#64 →
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_51).base + (archiveEncodeRawCutOff + 4#64) →
      sf.status = .Running →
      sf.sp = s0.sp - 464#64 →
      sf.trace = s0.trace →
      sf.readReg64 .x19 = recPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length →
      sf.readReg64 .x21 = s0.sp - 112#64 →
      sf.readReg64 .x23 = 0#64 →
      sf.readReg64 .x24 = s0.readReg64 .x24 →
      sf.readReg64 .x25 = s0.readReg64 .x25 →
      sf.readReg64 .x26 = s0.readReg64 .x26 →
      sf.readReg64 .x27 = s0.readReg64 .x27 →
      sf.readReg64 .x28 = s0.readReg64 .x28 →
      sf.readReg64 .x29 = s0.sp - 64#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWP (lsProg_51 H) target sf
        (archiveMidRawPre A lim
          (M.stepEvents
            (rustAllocEvents (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1)
            st1)
          sf s0 recPtr prevCap prevPtr G sess bs336 capEnc ptrEnc c0 v464 v112 Fprev)
        post) :
    SepWP (lsProg_51 H) target s2
      (archiveMidShimPre A lim st1 s2 s0 recPtr prevCap prevPtr G sess bs336
        c0 c1 c2 c3 v464 v112 Fprev)
      post := by
  have halloc := allocNoOom_placed_sub_clX (callerProg := lsProg_51 H) hC
  have hraw := encodeRawPrealloc_placed_sub_clX (callerProg := lsProg_51 H) hRaw
  change subroutine_ok (lsProg_51 H) (lsρ lsRustAllocSym)
    (withLsCl lsmpl (rustAllocNoOomSubSpecX M A lim)) at halloc
  change subroutine_ok (lsProg_51 H) (lsmpl.base 14)
    (withLsCl lsmpl (encodeRawPreallocSubSpecX A.repAlloc)) at hraw
  dsimp only [withLsCl, rustAllocNoOomSubSpecX,
    LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget.rustAllocNoOomSubSpecX,
    rustCliAllocNoOomSpecWithStack,
    encodeRawPreallocSubSpecX] at halloc hraw
  simp only [Bool.false_eq_true, ↓reduceIte] at halloc
  have hsp2_align : s2.spAligned = true := spAligned_of_sub_464 hsp_align hsp2
  have hseg51 := fun {mid tgt : BitVec 64} {s : State} {Pre : SepProp}
      {post' : State → SepProp → Prop} {oom : State → SepProp} =>
    sepWP_seg_ls_vm (prog := lsProg_51 H) (Q := lsProg_51 (hooksException H))
      blkLib_eq_51 (by rfl) (mid := mid) (target := tgt) (s := s) (Pre := Pre)
      (post := post') (oom := oom)
  simp only [archiveShimCutOff, arm64_norm] at hpc2
  unfold archiveMidShimPre
  have hn_pos : 0 < (encSessionMem (clearPendingGhost G) (clearPending sess)).length :=
    encSessionMem_length_pos _ _
  have hn_toNat : (BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length).toNat =
      (encSessionMem (clearPendingGhost G) (clearPending sess)).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply sepWP_seq_lscl hcl2 (mid := lsρ lsRustAllocSym)
  wp_seg_sync hseg51 (lsρ lsRustAllocSym)
  wp_done_call hcl_alloc
  have hex_pow : ∃ k, 1 = 1 * 2 ^ k := ⟨0, rfl⟩
  have hex_pow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hsz_le : (encSessionMem (clearPendingGhost G) (clearPending sess)).length + 1 ≤ 2 ^ 63 := by
    omega
  have hrlay : RustLayoutOk (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1 :=
    ⟨⟨hn_pos, hex_pow1, hsz_le⟩, by decide⟩
  wp_call halloc ((encSessionMem (clearPendingGhost G) (clearPending sess)).length, 1, st1)
  have htr_alloc := (‹AllocCallPreserved _ sf›).2.1
  have hp0_ne : sf.readReg64 Reg.x0 ≠ 0#64 := by assumption
  have hp0' : sf.readReg64 (Reg.gpr 0#5) ≠ 0 := hp0_ne
  have hp0_beq : (sf.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hp0_ne
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 14); · assumption
  wp_seg_sync hseg51 (lsmpl.base 14)
  have hv88 := vecU8At_nil_88X A.repAlloc s0.sp (sf.readReg64 (Reg.gpr 0#5))
    (encSessionMem (clearPendingGhost G) (clearPending sess)).length hn_pos (by omega) hp0'
  rw [A.repAlloc_live_norm] at hv88
  refine SepWP.fold hv88 (by sep_focus) ?_
  wp_done_call hcl_raw
  have hraw_spare : ([] : List (BitVec 8)).length +
      (encSessionMem (clearPendingGhost G) (clearPending sess)).length ≤
      (BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length).toNat := by
    simp only [List.length_nil, Nat.zero_add, hn_toNat]; exact Nat.le_refl _
  have hraw_lt : ([] : List (BitVec 8)).length +
      (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32 := by
    simp only [List.length_nil, Nat.zero_add]; exact hlen_enc
  wp_call hraw ⟨s0.sp - 456#64, clearPendingGhost G, clearPending sess, s0.sp - 88#64,
    BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length,
    sf.readReg64 (Reg.gpr 0#5), []⟩
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  conv => arg 4; simp only [List.nil_append]
  have cont_goal := hcont _
    (BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length)
    (sf.readReg64 (Reg.gpr 0#5))
    rfl hp0_ne (by assumption)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*])
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*])
  refine sepWP_eq_pre ?_ cont_goal
  unfold archiveMidRawPre; sep_ac_rfl

/-- `SepWPpLsCl` CPS counterpart of `archive_shim_to_raw_placed_sepWP`
    (`EncodeRawPreallocPlacedOkX`). -/
theorem archive_shim_to_raw_placed_cps [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H)
    (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (st1 : M.σ)
    (bs336 : List (BitVec 8))
    (Fprev : SepProp)
    (s0 s2 : State)
    (Q Qp : State → SepProp → Prop)
    (hsp_align : s0.spAligned = true)
    (hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32)
    (hfit_alloc : FitsEvents M lim st1
      (rustAllocEvents (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1))
    (c0 c1 c2 c3 v464 : BitVec 64) (v112 : BitVec 128)
    (hpc2 : s2.pc = (blkPl_51).base + (archiveShimCutOff + 4#64))
    (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 464#64)
    (htr2 : s2.trace = s0.trace)
    (hx19 : s2.readReg64 .x19 = recPtr)
    (hx20 : s2.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length)
    (hx23 : s2.readReg64 .x23 = 0#64)
    (hx24 : s2.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s2.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s2.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s2.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s2.readReg64 .x28 = s0.readReg64 .x28)
    (hx29 : s2.readReg64 .x29 = s0.sp - 64#64)
    (hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hcont : ∀ (sf : State) (capEnc ptrEnc : BitVec 64),
      capEnc = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length →
      ptrEnc ≠ 0#64 →
      sf.pc = (blkPl_51).base + (archiveEncodeRawCutOff + 4#64) →
      sf.status = .Running →
      sf.sp = s0.sp - 464#64 →
      sf.trace = s0.trace →
      sf.readReg64 .x19 = recPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length →
      sf.readReg64 .x21 = s0.sp - 112#64 →
      sf.readReg64 .x23 = 0#64 →
      sf.readReg64 .x24 = s0.readReg64 .x24 →
      sf.readReg64 .x25 = s0.readReg64 .x25 →
      sf.readReg64 .x26 = s0.readReg64 .x26 →
      sf.readReg64 .x27 = s0.readReg64 .x27 →
      sf.readReg64 .x28 = s0.readReg64 .x28 →
      sf.readReg64 .x29 = s0.sp - 64#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPpLsCl lsmpl (lsProg_51 H) (s0.readReg64 .lr) sf
        (archiveMidRawPre A lim
          (M.stepEvents
            (rustAllocEvents (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1)
            st1)
          sf s0 recPtr prevCap prevPtr G sess bs336 capEnc ptrEnc c0 v464 v112 Fprev)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_51 H) (s0.readReg64 .lr) s2
      (archiveMidShimPre A lim st1 s2 s0 recPtr prevCap prevPtr G sess bs336
        c0 c1 c2 c3 v464 v112 Fprev)
      Q Qp := by
  intro hcl2
  exact SepWPpLsCl.of_sepWP
    (mid := (blkPl_51).base + (archiveEncodeRawCutOff + 4#64))
    (archive_shim_to_raw_placed_sepWP hC hRaw recPtr prevCap prevPtr G sess st1 bs336 Fprev
      s0 s2 ((blkPl_51).base + (archiveEncodeRawCutOff + 4#64))
      (fun sm Pm => SepWPpLsCl lsmpl (lsProg_51 H) (s0.readReg64 .lr) sm Pm Q Qp)
      hcl2 hsp_align hlen_enc hfit_alloc c0 c1 c2 c3 v464 v112
      hpc2 hrun2 hsp2 htr2 hx19 hx20 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs2
      (fun sf capEnc ptrEnc hcap hptr _hclf hpcsf hrunsf hspsf htrsf
          hx19f hx20f hx21f hx23f hx24f hx25f hx26f hx27f hx28f hx29f hvrf =>
        SepWP.done hpcsf hrunsf
          (hcont sf capEnc ptrEnc hcap hptr hpcsf hrunsf hspsf htrsf
            hx19f hx20f hx21f hx23f hx24f hx25f hx26f hx27f hx28f hx29f hvrf)))
    hcl2

/-! ## Combined Entry-to-`encode_raw` Return Theorems -/

/-- Combined `SepWP` prefix from `archive_current_state_inner` entry through `encode_raw` return
    under `FitsEnv M lim st (ArchiveCoreEnv prevCap G sess)` +
    `EncodeRawPreallocPlacedOkX A.repAlloc H`, handing the continuation the residual `FitsEnv` for
    `grow_one ++ drop_glue`. -/
theorem archive_head_to_raw_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H)
    (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (st : M.σ)
    (Fprev : SepProp)
    (s0 : State)
    (target : BitVec 64)
    (post : State → SepProp → Prop)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_51).base)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = recPtr)
    (hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32)
    (hFit : FitsEnv M lim st (ArchiveCoreEnv prevCap G sess))
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 : BitVec 64) (v112 : BitVec 128)
    (hcont : ∀ (sf : State) (evs1 : List AllocEvent) (bs336 : List (BitVec 8))
        (capEnc ptrEnc : BitVec 64),
      FreeOnlyEvs evs1 →
      bs336.length = 336 →
      capEnc = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length →
      ptrEnc ≠ 0#64 →
      FitsEnv M lim
        (M.stepEvents
          (rustAllocEvents (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1)
          (M.stepEvents evs1 st))
        (SeqEnv (fun evs => if prevCap = 0#64 then evs = rustAllocEvents 96 8 else evs = [])
          FreeOnlyEvs) →
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_51).base + (archiveEncodeRawCutOff + 4#64) →
      sf.status = .Running →
      sf.sp = s0.sp - 464#64 →
      sf.trace = s0.trace →
      sf.readReg64 .x19 = recPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length →
      sf.readReg64 .x21 = s0.sp - 112#64 →
      sf.readReg64 .x23 = 0#64 →
      sf.readReg64 .x24 = s0.readReg64 .x24 →
      sf.readReg64 .x25 = s0.readReg64 .x25 →
      sf.readReg64 .x26 = s0.readReg64 .x26 →
      sf.readReg64 .x27 = s0.readReg64 .x27 →
      sf.readReg64 .x28 = s0.readReg64 .x28 →
      sf.readReg64 .x29 = s0.sp - 64#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWP (lsProg_51 H) target sf
        (archiveMidRawPre A lim
          (M.stepEvents
            (rustAllocEvents (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1)
            (M.stepEvents evs1 st))
          sf s0 recPtr prevCap prevPtr G sess bs336 capEnc ptrEnc c0 v464 v112 Fprev)
        post) :
    SepWP (lsProg_51 H) target s0
      ((recPtr ↦₆₄ prevCap) ∗ ((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 0#64) ∗
        sessionStateReprAt A.repAlloc (recPtr + 0x18#64) G sess ∗ A.pool lim st s0 ∗
        stackAt (s0.sp - 464#64) serializeSubStackX ∗
        ((s0.sp - 464#64) ↦₆₄ v464) ∗ ((s0.sp - 456#64) ↦₆₄ v456) ∗
        memRegion (s0.sp - 448#64) 336 ∗ ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
        ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
        ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
        ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
        ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
        ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
        ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗ Fprev)
      post :=
  archive_clear_to_shim_placed_sepWP hC recPtr prevCap prevPtr G sess st Fprev s0 target post
    hcl0 hpc hrun hsp_align hx0 hlen_enc
    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 v112
    fun s2 evs1 bs336 hf1 hbs336 hcl2 hpc2 hrun2 hsp2 htr2
        hx19 hx20 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs2 =>
      archive_shim_to_raw_placed_sepWP hC hRaw recPtr prevCap prevPtr G sess
        (M.stepEvents evs1 st) bs336 Fprev s0 s2 target post
        hcl2 hsp_align hlen_enc (fitsEvents_allocEnc_of_archiveCoreEnv hFit hf1)
        c0 c1 c2 c3 v464 v112
        hpc2 hrun2 hsp2 htr2 hx19 hx20 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs2
        fun sf capEnc ptrEnc hcap hptr =>
          hcont sf evs1 bs336 capEnc ptrEnc hf1 hbs336 hcap hptr
            (fitsEnv_growTail_of_archiveCoreEnv hFit hf1)

/-- `SepWPpLsCl` CPS counterpart of `archive_head_to_raw_placed_sepWP`
    (`ArchiveCoreEnv` + `EncodeRawPreallocPlacedOkX`). -/
theorem archive_head_to_raw_placed_cps [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H)
    (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (st : M.σ)
    (Fprev : SepProp)
    (s0 : State)
    (Q Qp : State → SepProp → Prop)
    (hpc : s0.pc = (blkPl_51).base)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = recPtr)
    (hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32)
    (hFit : FitsEnv M lim st (ArchiveCoreEnv prevCap G sess))
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 : BitVec 64) (v112 : BitVec 128)
    (hcont : ∀ (sf : State) (evs1 : List AllocEvent) (bs336 : List (BitVec 8))
        (capEnc ptrEnc : BitVec 64),
      FreeOnlyEvs evs1 →
      bs336.length = 336 →
      capEnc = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length →
      ptrEnc ≠ 0#64 →
      FitsEnv M lim
        (M.stepEvents
          (rustAllocEvents (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1)
          (M.stepEvents evs1 st))
        (SeqEnv (fun evs => if prevCap = 0#64 then evs = rustAllocEvents 96 8 else evs = [])
          FreeOnlyEvs) →
      sf.pc = (blkPl_51).base + (archiveEncodeRawCutOff + 4#64) →
      sf.status = .Running →
      sf.sp = s0.sp - 464#64 →
      sf.trace = s0.trace →
      sf.readReg64 .x19 = recPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length →
      sf.readReg64 .x21 = s0.sp - 112#64 →
      sf.readReg64 .x23 = 0#64 →
      sf.readReg64 .x24 = s0.readReg64 .x24 →
      sf.readReg64 .x25 = s0.readReg64 .x25 →
      sf.readReg64 .x26 = s0.readReg64 .x26 →
      sf.readReg64 .x27 = s0.readReg64 .x27 →
      sf.readReg64 .x28 = s0.readReg64 .x28 →
      sf.readReg64 .x29 = s0.sp - 64#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPpLsCl lsmpl (lsProg_51 H) (s0.readReg64 .lr) sf
        (archiveMidRawPre A lim
          (M.stepEvents
            (rustAllocEvents (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1)
            (M.stepEvents evs1 st))
          sf s0 recPtr prevCap prevPtr G sess bs336 capEnc ptrEnc c0 v464 v112 Fprev)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_51 H) (s0.readReg64 .lr) s0
      ((recPtr ↦₆₄ prevCap) ∗ ((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 0#64) ∗
        sessionStateReprAt A.repAlloc (recPtr + 0x18#64) G sess ∗ A.pool lim st s0 ∗
        stackAt (s0.sp - 464#64) serializeSubStackX ∗
        ((s0.sp - 464#64) ↦₆₄ v464) ∗ ((s0.sp - 456#64) ↦₆₄ v456) ∗
        memRegion (s0.sp - 448#64) 336 ∗ ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
        ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
        ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
        ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
        ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
        ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
        ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗ Fprev)
      Q Qp := by
  intro hcl0
  exact SepWPpLsCl.of_sepWP
    (mid := (blkPl_51).base + (archiveEncodeRawCutOff + 4#64))
    (archive_head_to_raw_placed_sepWP hC hRaw recPtr prevCap prevPtr G sess st Fprev s0
      ((blkPl_51).base + (archiveEncodeRawCutOff + 4#64))
      (fun sm Pm => SepWPpLsCl lsmpl (lsProg_51 H) (s0.readReg64 .lr) sm Pm Q Qp)
      hcl0 hpc hrun hsp_align hx0 hlen_enc hFit
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 v112
      (fun sf evs1 bs336 capEnc ptrEnc hf1 hbs336 hcap hptr hfit_rest _hclf
          hpcsf hrunsf hspsf htrsf
          hx19f hx20f hx21f hx23f hx24f hx25f hx26f hx27f hx28f hx29f hvrf =>
        SepWP.done hpcsf hrunsf
          (hcont sf evs1 bs336 capEnc ptrEnc hf1 hbs336 hcap hptr hfit_rest
            hpcsf hrunsf hspsf htrsf
            hx19f hx20f hx21f hx23f hx24f hx25f hx26f hx27f hx28f hx29f hvrf)))
    hcl0

end Placed

end LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePendPlacedBudget
