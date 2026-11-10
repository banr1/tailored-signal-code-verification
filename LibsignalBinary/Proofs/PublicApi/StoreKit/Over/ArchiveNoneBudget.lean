/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePendPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveNone
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.HeapDefs
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodySomeX
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Tail and Top-Level Proofs of `archive_current_state_inner`

Verifies the budget-threaded `prevCap = 0#64` (`grow_one`) and `prevCap ≠ 0#64` (in-place) tails on
Block `51` (`lsProg_51 H`), establishing `ArchiveOverPlacedOkX` and `ArchiveOverGenPlacedOk` under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveNoneBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded IsLsBlockProg
  lsmpl withLsCodeLoaded withLsCl sepWP_seq_lscl
  lsProg_51 blkPl_51 blkLib_eq_51
)
open CryptoVerification.RustHeap (vecAt vecU8At)
open CryptoVerification.LibsignalPublicApiRepr (sessionStateReprAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet (ls_subroutine_ok_cl_of_callee)
open CryptoVerification.LibsignalSpqrV1 (GrowOneCall newCapVecU8)
open CryptoVerification.E2E.Record.Serialization (encSessionMem)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux (
  sessionAt_entails_sessionStateAt
)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX (
  serializeSubStackX sepWP_exists_left_sepX sepWP_pure_left_sepX
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  HdrP Prev1 prevVecAt
  clearPendingGhost clearPending archiveStackX
  ArchiveOverGhost ArchiveOverGenGhost
  archiveEncodeRawCutOff
  vecU8At_unpack_88X cell112_splitX vecU8_from_cellsX newCapVecU8_zeroX
  memRegion_prev_slot0_cells prevVecAt_one_of_parts
  prevVecAt_nil_eq prevVecAt_zero_nil_eq prevVecAt_ne_zero_nil_eq
  hdrP_eq hdrP_prev1_of_raw_cellsX memRegion_prev96_cellsX
  stackAt_archive_unpackX stackAt_archive_pack_344X hdrP_prev1_entails_gen
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FitsEnv FreeOnlyEvs rustAllocEvents
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
  GrowOneVecU8Env
  growOneVecU8BudgetSpec
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerContractsXPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  DropSessionStructureLocal1PlacedOkX
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget (
  ArchiveCoreEnv ArchiveOverEnvX ArchiveOverGenEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (
  ArchiveOverGenPlacedOk ArchiveOverPlacedOkX
  archiveOverGenSpec_pre_eq archiveOverGenSpec_post_eq
  archiveOverSpecX_pre_eq archiveOverSpecX_post_eq
  EncodeRawPreallocPlacedOkX
  dropLocal1SubSpecX dropLocal1_placed_sub_clX
  growOneSubSpecX growOne_arch_placed_clX
  growOneVecU8Env_zero_iff fitsEnv_growOneZero_of_archiveCoreEnv
  archiveCoreEnv_zero_of_parts archiveCoreEnv_nonzero_of_parts
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePendPlacedBudget (
  archiveMidRawPre archive_head_to_raw_placed_sepWP
)

private theorem bv_sub_add_lit_local (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

private theorem sepWP_eq_pre {prog : Program} {target : BitVec 64} {s : State}
    {P1 P2 : SepProp} {post : State → SepProp → Prop}
    (heq : P1 = P2) (h : SepWP prog target s P2 post) :
    SepWP prog target s P1 post :=
  heq ▸ h

private abbrev mod8Var {p : BitVec 64} (_ : p.toNat % 8 = 0) : BitVec 64 := p

private theorem growOneVecU8Env_zero_eq {x : GrowOneCall} {evs : List AllocEvent}
    (hcap : x.cap = 0#64) (hevs : GrowOneVecU8Env x evs) :
    evs = rustAllocEvents 96 8 :=
  (growOneVecU8Env_zero_iff (x := x) hcap).mp hevs

private theorem spAligned_of_sub_464_local {s0 s3 : State}
    (halign0 : s0.spAligned = true) (hsp3 : s3.sp = s0.sp - 464#64) :
    s3.spAligned = true := by
  unfold State.spAligned at halign0 ⊢
  rw [hsp3, beq_iff_eq] at *
  have h0 : (s0.sp &&& 15#64).toNat = 0 := congrArg BitVec.toNat halign0
  rw [BitVec.toNat_and, show (15#64 : BitVec 64).toNat = 2 ^ 4 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod] at h0
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (15#64 : BitVec 64).toNat = 2 ^ 4 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  bv_omega

private theorem archiveOverSpecX_pre_fun_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    (ArchiveDefsBudget.archiveOverSpecX M A lim).pre =
      fun (x, st) s =>
        ⌜FitsEnv M lim st (ArchiveOverEnvX x) ∧ s.readReg64 .x0 = x.recPtr ∧
          x.prevPtr ≠ 0#64 ∧
          (encSessionMem (clearPendingGhost x.G) (clearPending x.sess)).length < 2 ^ 32⌝ ∗
          HdrP x.recPtr 0#64 x.prevPtr 0#64 ∗
          sessionStateReprAt A.repAlloc (x.recPtr + 0x18#64) x.G x.sess ∗
          A.pool lim st s ∗ stackAt s.sp archiveStackX := by
  funext ⟨x, st⟩ s
  rw [archiveOverSpecX_pre_eq, ← sepConj_assoc, pure_sepConj_pure]

private theorem archiveOverSpecX_post_fun_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    (ArchiveDefsBudget.archiveOverSpecX M A lim).post =
      fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜ArchiveOverEnvX x evs⌝ ∗
          ⌜sf.trace = s0.trace⌝ ∗
          (∃∗ q : BitVec 64,
            HdrP x.recPtr 4#64 q 1#64 ∗
              Prev1 A.repAlloc q (encSessionMem (clearPendingGhost x.G) (clearPending x.sess))) ∗
          ((x.recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.recPtr + 0x20#64) 336 ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp archiveStackX := by
  funext ⟨x, st⟩ s0 sf
  exact archiveOverSpecX_post_eq M A lim x st s0 sf

private theorem archiveOverGenSpec_pre_fun_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    (ArchiveDefsBudget.archiveOverGenSpec M A lim).pre =
      fun (x, st) s =>
        ⌜FitsEnv M lim st (ArchiveOverGenEnv x) ∧ s.readReg64 .x0 = x.recPtr ∧
          (encSessionMem (clearPendingGhost x.G) (clearPending x.sess)).length < 2 ^ 32⌝ ∗
          vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) x.recPtr x.prevCap x.prevPtr [] ∗
          sessionStateReprAt A.repAlloc (x.recPtr + 0x18#64) x.G x.sess ∗
          A.pool lim st s ∗ stackAt s.sp archiveStackX := by
  funext ⟨x, st⟩ s
  rw [archiveOverGenSpec_pre_eq, ← sepConj_assoc, pure_sepConj_pure]

private theorem archiveOverGenSpec_post_fun_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    (ArchiveDefsBudget.archiveOverGenSpec M A lim).post =
      fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜ArchiveOverGenEnv x evs⌝ ∗
          ⌜sf.trace = s0.trace⌝ ∗
          (∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
            ⌜prevCap' ≠ 0#64⌝ ∗
            prevVecAt A.repAlloc x.recPtr prevCap' prevPtr'
              [encSessionMem (clearPendingGhost x.G) (clearPending x.sess)]) ∗
          ((x.recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.recPtr + 0x20#64) 336 ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp archiveStackX := by
  funext ⟨x, st⟩ s0 sf
  exact archiveOverGenSpec_post_eq M A lim x st s0 sf

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit_local BitVec.toNat_zero

section Placed

attribute [local irreducible] encSessionMem sessionStateReprAt sessionStateAt FitsEnv

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

/-! ## Zero-Capacity Tail (`prevCap = 0#64`) -/

set_option maxHeartbeats 800000 in
/-- Relocatable budget-threaded `prevCap = 0#64` tail (`grow_one` to capacity `4#64` +
`drop_glue::<SessionStructure> [local#1]` + epilogue) on `lsProg_51 H`. -/
theorem archive_tail_zero_cap_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H)
    (recPtr prevPtr : BitVec 64)
    (hprev_ne : prevPtr ≠ 0#64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (st : M.σ)
    (evs1 : List AllocEvent) (hf1 : FreeOnlyEvs evs1)
    (hFit : FitsEnv M lim st (ArchiveCoreEnv 0#64 G sess))
    (bs336 : List (BitVec 8)) (hbs336 : bs336.length = 336)
    (capEnc ptrEnc c0 v464 : BitVec 64) (v112 : BitVec 128)
    (s0 s3 : State)
    (post : State → SepProp → Prop)
    (hcl3 : LibsignalCodeLoaded lsmpl s3.mem)
    (hsp_align : s0.spAligned = true)
    (hpc3 : s3.pc = (blkPl_51).base + (archiveEncodeRawCutOff + 4#64))
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 464#64)
    (htr3 : s3.trace = s0.trace)
    (hx19 : s3.readReg64 .x19 = recPtr)
    (_hx20 : s3.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length)
    (hx21 : s3.readReg64 .x21 = s0.sp - 112#64)
    (hx23 : s3.readReg64 .x23 = 0#64)
    (hx24 : s3.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s3.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s3.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s3.readReg64 .x27 = s0.readReg64 .x27)
    (_hx28 : s3.readReg64 .x28 = s0.readReg64 .x28)
    (hx29 : s3.readReg64 .x29 = s0.sp - 64#64)
    (hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hcont : ∀ (sf : State) (evs : List AllocEvent) (q : BitVec 64),
      ArchiveCoreEnv 0#64 G sess evs →
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = s0.sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      SepWP (lsProg_51 H) (s0.readReg64 .lr) sf
        ((HdrP recPtr 4#64 q 1#64 ∗
            Prev1 A.repAlloc q (encSessionMem (clearPendingGhost G) (clearPending sess))) ∗
          ((recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (recPtr + 0x20#64) 336 ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp archiveStackX)
        post) :
    SepWP (lsProg_51 H) (s0.readReg64 .lr) s3
      (archiveMidRawPre A lim
        (M.stepEvents
          (rustAllocEvents (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1)
          (M.stepEvents evs1 st))
        s3 s0 recPtr 0#64 prevPtr G sess bs336 capEnc ptrEnc c0 v464 v112 emp)
      post := by
  have hgrow := growOne_arch_placed_clX (callerProg := lsProg_51 H) hGrow
  have hdrop := dropLocal1_placed_sub_clX (callerProg := lsProg_51 H) hDrop
  change subroutine_ok (lsProg_51 H) (lsmpl.base 621)
    (withLsCl lsmpl (growOneSubSpecX M A lim)) at hgrow
  change subroutine_ok (lsProg_51 H) (lsmpl.base 6)
    (withLsCl lsmpl (dropLocal1SubSpecX M A lim)) at hdrop
  dsimp only [withLsCl, growOneSubSpecX, dropLocal1SubSpecX] at hgrow hdrop
  have hsp3_align : s3.spAligned = true := spAligned_of_sub_464_local hsp_align hsp3
  have hseg51 := fun {mid tgt : BitVec 64} {s : State} {Pre : SepProp}
      {post' : State → SepProp → Prop} {oom : State → SepProp} =>
    sepWP_seg_ls_vm (prog := lsProg_51 H) (Q := lsProg_51 (hooksException H))
      blkLib_eq_51 (by rfl) (mid := mid) (target := tgt) (s := s) (Pre := Pre)
      (post := post') (oom := oom)
  simp only [archiveEncodeRawCutOff, arm64_norm] at hpc3
  unfold archiveMidRawPre
  conv => arg 4; simp only [sepConj_emp]
  apply sepWP_seq_lscl hcl3 (mid := lsmpl.base 621)
  rw [vecU8At_unpack_88X]
  refine SepWP.fold (cell112_splitX s0.sp _) (by sep_focus) ?_
  apply sepWP_exists_left_sepX; intro lo112
  conv => arg 4; simp only [sepExists_sepConj_left]
  apply SepWP.exists_left; intro hi112
  conv => arg 4; simp only [sepConj_assoc]
  wp_seg_sync hseg51 (lsmpl.base 621)
  wp_done_call hcl_grow
  have hprev_ne0 : prevPtr ≠ 0 := hprev_ne
  let growGhost : GrowOneCall := ⟨recPtr, 0#64, prevPtr, []⟩
  have hgrow_len : growGhost.bs.length = growGhost.cap.toNat * 24 := rfl
  have hgrow_ptr : growGhost.ptr ≠ 0 := hprev_ne
  have hgrow_max : max (2 * growGhost.cap.toNat) 4 * 24 + 8 ≤ 2 ^ 63 := by
    dsimp only [growGhost]; decide
  have hfit_grow : FitsEnv M lim
      (M.stepEvents
        (rustAllocEvents (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1)
        (M.stepEvents evs1 st))
      (GrowOneVecU8Env growGhost) :=
    fitsEnv_growOneZero_of_archiveCoreEnv rfl hFit hf1
  have hite_emp :
      (emp : SepProp) =
        (if growGhost.cap = 0 then emp
         else A.live growGhost.ptr growGhost.bs.length 8 ∗ (growGhost.ptr ↦ₛ growGhost.bs)) := by
    dsimp only [growGhost]
    simp
  have hstack_s3 :
      stackAt (s0.sp - 464#64) serializeSubStackX = stackAt s3.sp serializeSubStackX := by
    rw [hsp3]
  conv => arg 4; rw [hstack_s3, ← emp_sepConj (stackAt s3.sp serializeSubStackX), hite_emp]
  wp_call hgrow (growGhost,
    M.stepEvents
      (rustAllocEvents (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1)
      (M.stepEvents evs1 st))
  have hstack_grow := congrArg (fun x => stackAt x serializeSubStackX) ‹_ = s3.sp›
  have hevs_grow_eq := growOneVecU8Env_zero_eq (x := growGhost) rfl (by assumption)
  conv => arg 4; rw [hevs_grow_eq]
  apply sepWP_seq_lscl (pl := lsmpl) (mid := lsmpl.base 6); · assumption
  have hmax4 : max 0 4 = 4 := rfl
  conv => arg 4; dsimp only [growGhost]; simp only [List.length_nil, BitVec.toNat_zero,
    Nat.mul_zero, hmax4, Nat.sub_zero, Nat.reduceMul, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, pointsToBytes_nil, emp_sepConj, sepConj_emp]
  rw [memRegion_prev96_cellsX, newCapVecU8_zeroX]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro sc0
  apply SepWP.exists_left; intro sc8
  apply SepWP.exists_left; intro sc16
  wp_seg_sync hseg51 (lsmpl.base 6)
  refine SepWP.fold
    (sessionAt_entails_sessionStateAt A.repAlloc (s0.sp - 456#64) (clearPendingGhost G) (clearPending sess))
    (by sep_focus) ?_
  wp_done_call hcl_drop
  wp_call hdrop (⟨s0.sp - 456#64, clearPendingGhost G, (clearPending sess).state⟩,
    M.stepEvents (rustAllocEvents 96 8)
      (M.stepEvents
        (rustAllocEvents (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1)
        (M.stepEvents evs1 st)))
  wp_steps_sync_pool (s0.readReg64 .lr)
  have hhdr_fold : ∀ (q cap ptr : BitVec 64), q ≠ 0 →
      ((recPtr ↦₆₄ 4#64) ∗ ((recPtr + 8#64) ↦₆₄ q) ∗ ((recPtr + 16#64) ↦₆₄ 1#64) ∗
        A.live q 96 8 ∗
        (q ↦₆₄ cap) ∗ ((q + 8#64) ↦₆₄ ptr) ∗
        ((q + 16#64) ↦₆₄ BitVec.ofNat 64
          (encSessionMem (clearPendingGhost G) (clearPending sess)).length) ∗
        CryptoVerification.RustHeap.vecU8Buf A.repAlloc cap ptr
          (encSessionMem (clearPendingGhost G) (clearPending sess)) ∗
        memRegion (q + 24#64) 72) ⊢
      HdrP recPtr 4#64 q 1#64 ∗
        Prev1 A.repAlloc q (encSessionMem (clearPendingGhost G) (clearPending sess)) :=
    fun q cap ptr hq =>
      hdrP_prev1_of_raw_cellsX A.repAlloc recPtr q cap ptr
        (encSessionMem (clearPendingGhost G) (clearPending sess)) hq
  refine SepWP.fold
    (hhdr_fold _ _ _ (by assumption))
    (by sep_focus) ?_
  have h32 : ((recPtr + 32#64) ↦ₛ bs336) ⊢ memRegion (recPtr + 0x20#64) 336 := by
    rw [← hbs336]; exact pointsToBytes_entails_memRegion _ _
  refine SepWP.fold h32 (by sep_focus) ?_
  conv => arg 4; rw [hstack_grow, ← hstack_s3]
  refine SepWP.fold
    (stackAt_archive_pack_344X s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (by sep_focus) ?_
  conv => arg 4; simp only [← AllocCostModel.stepEvents_append, List.append_assoc]
  have hEnv_final := archiveCoreEnv_zero_of_parts (G := G) (sess := sess)
    hf1 (rfl : rustAllocEvents 96 8 = rustAllocEvents 96 8) (by assumption)
  dsimp only [Reg.x24, Reg.x25, Reg.x26, Reg.x27] at hx24 hx25 hx26 hx27
  refine sepWP_eq_pre ?_
    (hcont _ _ (mod8Var (by assumption)) hEnv_final ?_ ?_ ?_ ?_ ?_)
  · dsimp only [mod8Var]; sep_ac_rfl
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · simp only [arm64_norm, *]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals wp_norm_lhs

/-! ## Nonzero-Capacity Tail (`prevCap ≠ 0#64`) -/

set_option maxHeartbeats 800000 in
/-- Relocatable budget-threaded `prevCap ≠ 0#64` tail (in-place store into slot `0` +
`drop_glue::<SessionStructure> [local#1]` + epilogue) on `lsProg_51 H`. -/
theorem archive_tail_nonzero_cap_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H)
    (recPtr prevCap prevPtr : BitVec 64)
    (hcap : prevCap ≠ 0#64)
    (hbound : prevCap.toNat * 24 < 2 ^ 63)
    (hprev_ne : prevPtr ≠ 0#64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (st : M.σ)
    (evs1 : List AllocEvent) (hf1 : FreeOnlyEvs evs1)
    (bs336 : List (BitVec 8)) (hbs336 : bs336.length = 336)
    (capEnc ptrEnc c0 v464 : BitVec 64) (v112 : BitVec 128)
    (s0 s3 : State)
    (post : State → SepProp → Prop)
    (hcl3 : LibsignalCodeLoaded lsmpl s3.mem)
    (hsp_align : s0.spAligned = true)
    (hpc3 : s3.pc = (blkPl_51).base + (archiveEncodeRawCutOff + 4#64))
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 464#64)
    (htr3 : s3.trace = s0.trace)
    (hx19 : s3.readReg64 .x19 = recPtr)
    (_hx20 : s3.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length)
    (hx21 : s3.readReg64 .x21 = s0.sp - 112#64)
    (hx23 : s3.readReg64 .x23 = 0#64)
    (hx24 : s3.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s3.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s3.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s3.readReg64 .x27 = s0.readReg64 .x27)
    (_hx28 : s3.readReg64 .x28 = s0.readReg64 .x28)
    (hx29 : s3.readReg64 .x29 = s0.sp - 64#64)
    (hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hcont : ∀ (sf : State) (evs : List AllocEvent),
      ArchiveCoreEnv prevCap G sess evs →
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = s0.sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      SepWP (lsProg_51 H) (s0.readReg64 .lr) sf
        (prevVecAt A.repAlloc recPtr prevCap prevPtr
            [encSessionMem (clearPendingGhost G) (clearPending sess)] ∗
          ((recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (recPtr + 0x20#64) 336 ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp archiveStackX)
        post) :
    SepWP (lsProg_51 H) (s0.readReg64 .lr) s3
      (archiveMidRawPre A lim
        (M.stepEvents
          (rustAllocEvents (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1)
          (M.stepEvents evs1 st))
        s3 s0 recPtr prevCap prevPtr G sess bs336 capEnc ptrEnc c0 v464 v112
        (A.repAlloc.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)))
      post := by
  have hdrop := dropLocal1_placed_sub_clX (callerProg := lsProg_51 H) hDrop
  change subroutine_ok (lsProg_51 H) (lsmpl.base 6)
    (withLsCl lsmpl (dropLocal1SubSpecX M A lim)) at hdrop
  dsimp only [withLsCl, dropLocal1SubSpecX] at hdrop
  have hsp3_align : s3.spAligned = true := spAligned_of_sub_464_local hsp_align hsp3
  have hseg51 := fun {mid tgt : BitVec 64} {s : State} {Pre : SepProp}
      {post' : State → SepProp → Prop} {oom : State → SepProp} =>
    sepWP_seg_ls_vm (prog := lsProg_51 H) (Q := lsProg_51 (hooksException H))
      blkLib_eq_51 (by rfl) (mid := mid) (target := tgt) (s := s) (Pre := Pre)
      (post := post') (oom := oom)
  simp only [archiveEncodeRawCutOff, arm64_norm] at hpc3
  unfold archiveMidRawPre
  have hcap_beq1 : (prevCap == 0#64) = false := beq_false_of_ne hcap
  have hcap_beq2 : (0#64 == prevCap) = false := beq_false_of_ne (Ne.symm hcap)
  have hcap_bne1 : (prevCap != 0#64) = true := bne_iff_ne.mpr hcap
  have hcap_bne2 : (0#64 != prevCap) = true := bne_iff_ne.mpr (Ne.symm hcap)
  apply sepWP_seq_lscl hcl3 (mid := lsmpl.base 6)
  rw [vecU8At_unpack_88X, memRegion_prev_slot0_cells prevPtr prevCap hcap hbound]
  refine SepWP.fold (cell112_splitX s0.sp _) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro lo112
  apply SepWP.exists_left; intro hi112
  apply SepWP.exists_left; intro sc2
  apply SepWP.exists_left; intro sc1
  apply SepWP.exists_left; intro sc0
  wp_seg_sync hseg51 (lsmpl.base 6)
  refine SepWP.fold
    (sessionAt_entails_sessionStateAt A.repAlloc (s0.sp - 456#64) (clearPendingGhost G) (clearPending sess))
    (by sep_focus) ?_
  wp_done_call hcl_drop
  wp_call hdrop (⟨s0.sp - 456#64, clearPendingGhost G, (clearPending sess).state⟩,
    M.stepEvents
      (rustAllocEvents (encSessionMem (clearPendingGhost G) (clearPending sess)).length 1)
      (M.stepEvents evs1 st))
  wp_steps_sync_pool (s0.readReg64 .lr)
  refine SepWP.fold
    (vecU8_from_cellsX A.repAlloc prevPtr _ _ (encSessionMem (clearPendingGhost G) (clearPending sess)))
    (by sep_focus) ?_
  have hprev_fold :
      ((recPtr ↦₆₄ prevCap) ∗ ((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 1#64) ∗
        A.live prevPtr (prevCap.toNat * 24) 8 ∗
        CryptoVerification.RustHeap.vecU8 A.repAlloc prevPtr
          (encSessionMem (clearPendingGhost G) (clearPending sess)) ∗
        memRegion (prevPtr + 24#64) ((prevCap.toNat - 1) * 24)) ⊢
      prevVecAt A.repAlloc recPtr prevCap prevPtr
        [encSessionMem (clearPendingGhost G) (clearPending sess)] :=
    prevVecAt_one_of_parts A.repAlloc recPtr prevCap prevPtr
      (encSessionMem (clearPendingGhost G) (clearPending sess)) hcap hbound hprev_ne
  refine SepWP.fold hprev_fold (by sep_focus) ?_
  have h32 : ((recPtr + 32#64) ↦ₛ bs336) ⊢ memRegion (recPtr + 0x20#64) 336 := by
    rw [← hbs336]; exact pointsToBytes_entails_memRegion _ _
  refine SepWP.fold h32 (by sep_focus) ?_
  have hstack_s3 :
      stackAt s3.sp serializeSubStackX = stackAt (s0.sp - 464#64) serializeSubStackX := by
    rw [hsp3]
  conv => arg 4; rw [hstack_s3]
  refine SepWP.fold
    (stackAt_archive_pack_344X s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (by sep_focus) ?_
  conv => arg 4; simp only [← AllocCostModel.stepEvents_append, List.append_assoc]
  have hEnv_final := archiveCoreEnv_nonzero_of_parts (G := G) (sess := sess)
    hcap hf1 (by assumption)
  dsimp only [Reg.x24, Reg.x25, Reg.x26, Reg.x27] at hx24 hx25 hx26 hx27
  refine sepWP_eq_pre ?_
    (hcont _ _ hEnv_final ?_ ?_ ?_ ?_ ?_)
  · sep_ac_rfl
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · simp only [arm64_norm, *]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals wp_norm_lhs

/-! ## Top-Level `ArchiveOverPlacedOkX` and `ArchiveOverGenPlacedOk` (Block `51`) -/

private structure TailDepsPlaced [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  grow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
    (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim))
  drop : DropSessionStructureLocal1PlacedOkX M A lim H

set_option maxHeartbeats 800000 in
/-- Relocatable `ArchiveOverPlacedOkX` (Block `51`) from `SerContractsXPlaced`, a Block `51`→`621`
`grow_one` budget contract, `EncodeRawPreallocPlacedOkX`, and `DropSessionStructureLocal1PlacedOkX`. -/
theorem archive_over_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    ArchiveOverPlacedOkX M A lim H := by
  have hDeps : TailDepsPlaced M A lim H := ⟨hGrow, hDrop⟩
  clear hGrow hDrop
  unfold ArchiveOverPlacedOkX withLsCodeLoaded
  rw [archiveOverSpecX_pre_fun_eq M A lim, archiveOverSpecX_post_fun_eq M A lim]
  wp_init x s0
  obtain ⟨⟨recPtr, prevPtr, G, sess⟩, st⟩ := x
  dsimp only [ArchiveOverEnvX] at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hFit : FitsEnv M lim st (ArchiveCoreEnv 0#64 G sess) := by assumption
  have hx0 : s0.readReg64 .x0 = recPtr := by assumption
  have hprev_ne : prevPtr ≠ 0#64 := by assumption
  have hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32 := by
    assumption
  conv => arg 4; rw [hdrP_eq, stackAt_archive_unpackX s0.sp]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_left fun c0 => SepWP.exists_left fun c1 =>
    SepWP.exists_left fun c2 => SepWP.exists_left fun c3 =>
    SepWP.exists_left fun c4 => SepWP.exists_left fun c5 =>
    SepWP.exists_left fun c6 => SepWP.exists_left fun c7 =>
    SepWP.exists_left fun c8 => SepWP.exists_left fun c9 =>
    SepWP.exists_left fun c10 => SepWP.exists_left fun c11 =>
    SepWP.exists_left fun v112 => SepWP.exists_left fun v456 =>
    SepWP.exists_left fun v464 => ?_
  refine sepWP_eq_pre
    (P2 := (recPtr ↦₆₄ 0#64) ∗ ((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 0#64) ∗
      sessionStateReprAt A.repAlloc (recPtr + 0x18#64) G sess ∗ A.pool lim st s0 ∗
      stackAt (s0.sp - 464#64) serializeSubStackX ∗
      ((s0.sp - 464#64) ↦₆₄ v464) ∗ ((s0.sp - 456#64) ↦₆₄ v456) ∗
      memRegion (s0.sp - 448#64) 336 ∗ ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
      ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
      ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
      ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
      ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
      ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
      ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗ emp)
    (by simp only [sepConj_emp]) ?_
  exact archive_head_to_raw_placed_sepWP hC hRaw recPtr 0#64 prevPtr G sess st emp s0
    (s0.readReg64 .lr) _ hcl0 (by assumption) (by assumption) (by assumption) hx0 hlen_enc hFit
    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 v112
    fun s3 evs1 bs336 capEnc ptrEnc hf1 hbs336 _hcap _hptr _hfit_rest hcl3
        hpc3 hrun3 hsp3 htr3 hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs3 =>
      archive_tail_zero_cap_placed_sepWP hDeps.grow hDeps.drop recPtr prevPtr hprev_ne
        G sess st evs1 hf1 hFit bs336 hbs336 capEnc ptrEnc c0 v464 v112 s0 s3 _
        hcl3 (by assumption)
        hpc3 hrun3 hsp3 htr3 hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs3
        fun sf evs q hEnv hpc_sf hrun_sf hsp_sf htr_sf hcs_sf => by
          wp_done

/-- Caller-block-polymorphic `withLsCl` form of `archive_over_placed_ok_of_contracts`. -/
theorem archive_over_placed_cl_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    subroutine_ok callerProg (lsmpl.base 51)
      (withLsCl lsmpl (ArchiveDefsBudget.archiveOverSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (archive_over_placed_ok_of_contracts hC hGrow hRaw hDrop)

set_option maxHeartbeats 800000 in
/-- Relocatable `ArchiveOverGenPlacedOk` (Block `51`) from `SerContractsXPlaced`, a Block `51`→`621`
`grow_one` budget contract, `EncodeRawPreallocPlacedOkX`, and
`DropSessionStructureLocal1PlacedOkX`. -/
theorem archive_over_gen_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    ArchiveOverGenPlacedOk M A lim H := by
  have hDeps : TailDepsPlaced M A lim H := ⟨hGrow, hDrop⟩
  clear hGrow hDrop
  unfold ArchiveOverGenPlacedOk withLsCodeLoaded
  rw [archiveOverGenSpec_pre_fun_eq M A lim, archiveOverGenSpec_post_fun_eq M A lim]
  simp only [prevVecAt_nil_eq]
  wp_init x s0
  obtain ⟨⟨recPtr, prevCap, prevPtr, G, sess⟩, st⟩ := x
  dsimp only [ArchiveOverGenEnv] at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hFit : FitsEnv M lim st (ArchiveCoreEnv prevCap G sess) := by assumption
  have hx0 : s0.readReg64 .x0 = recPtr := by assumption
  have hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32 := by
    assumption
  conv => arg 4; rw [stackAt_archive_unpackX s0.sp]
  by_cases hcap : prevCap = 0#64
  · subst hcap
    conv => arg 4; rw [prevVecAt_zero_nil_eq, hdrP_eq]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_left fun c0 => SepWP.exists_left fun c1 =>
      SepWP.exists_left fun c2 => SepWP.exists_left fun c3 =>
      SepWP.exists_left fun c4 => SepWP.exists_left fun c5 =>
      SepWP.exists_left fun c6 => SepWP.exists_left fun c7 =>
      SepWP.exists_left fun c8 => SepWP.exists_left fun c9 =>
      SepWP.exists_left fun c10 => SepWP.exists_left fun c11 =>
      SepWP.exists_left fun v112 => SepWP.exists_left fun v456 =>
      SepWP.exists_left fun v464 => ?_
    refine sepWP_eq_pre
      (P2 := ⌜prevPtr ≠ 0#64⌝ ∗
        ((recPtr ↦₆₄ 0#64) ∗ ((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 0#64) ∗
          sessionStateReprAt A.repAlloc (recPtr + 0x18#64) G sess ∗ A.pool lim st s0 ∗
          stackAt (s0.sp - 464#64) serializeSubStackX ∗
          ((s0.sp - 464#64) ↦₆₄ v464) ∗ ((s0.sp - 456#64) ↦₆₄ v456) ∗
          memRegion (s0.sp - 448#64) 336 ∗ ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
          ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
          ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
          ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
          ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
          ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
          ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗ emp))
      (by simp only [sepConj_emp]; sep_ac_rfl) ?_
    refine SepWP.pure_elim fun hprev_ne => ?_
    exact archive_head_to_raw_placed_sepWP hC hRaw recPtr 0#64 prevPtr G sess st emp s0
      (s0.readReg64 .lr) _ hcl0 (by assumption) (by assumption) (by assumption) hx0 hlen_enc hFit
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 v112
      fun s3 evs1 bs336 capEnc ptrEnc hf1 hbs336 _hcap _hptr _hfit_rest hcl3
          hpc3 hrun3 hsp3 htr3 hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs3 =>
        archive_tail_zero_cap_placed_sepWP hDeps.grow hDeps.drop recPtr prevPtr hprev_ne
          G sess st evs1 hf1 hFit bs336 hbs336 capEnc ptrEnc c0 v464 v112 s0 s3 _
          hcl3 (by assumption)
          hpc3 hrun3 hsp3 htr3 hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs3
          fun sf evs q hEnv hpc_sf hrun_sf hsp_sf htr_sf hcs_sf => by
            refine SepWP.fold
              (hdrP_prev1_entails_gen A.repAlloc recPtr q
                (encSessionMem (clearPendingGhost G) (clearPending sess)))
              (by sep_focus) ?_
            conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            apply SepWP.exists_left; intro prevCap'
            apply SepWP.exists_left; intro prevPtr'
            conv => arg 4; simp only [sepConj_assoc]
            apply SepWP.pure_elim; intro hprevCap'_ne
            wp_done
  · conv => arg 4; rw [prevVecAt_ne_zero_nil_eq A.repAlloc recPtr prevCap prevPtr hcap, hdrP_eq]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_left fun c0 => SepWP.exists_left fun c1 =>
      SepWP.exists_left fun c2 => SepWP.exists_left fun c3 =>
      SepWP.exists_left fun c4 => SepWP.exists_left fun c5 =>
      SepWP.exists_left fun c6 => SepWP.exists_left fun c7 =>
      SepWP.exists_left fun c8 => SepWP.exists_left fun c9 =>
      SepWP.exists_left fun c10 => SepWP.exists_left fun c11 =>
      SepWP.exists_left fun v112 => SepWP.exists_left fun v456 =>
      SepWP.exists_left fun v464 => ?_
    refine sepWP_eq_pre
      (P2 := ⌜prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
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
          ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗
          (A.repAlloc.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24))))
      (by sep_ac_rfl) ?_
    refine SepWP.pure_elim fun ⟨hbound, hprev_ne⟩ => ?_
    exact archive_head_to_raw_placed_sepWP hC hRaw recPtr prevCap prevPtr G sess st
      (A.repAlloc.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24))
      s0 (s0.readReg64 .lr) _ hcl0 (by assumption) (by assumption) (by assumption) hx0 hlen_enc hFit
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 v112
      fun s3 evs1 bs336 capEnc ptrEnc hf1 hbs336 _hcap_enc _hptr_enc _hfit_rest hcl3
          hpc3 hrun3 hsp3 htr3 hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs3 =>
        archive_tail_nonzero_cap_placed_sepWP hDeps.drop recPtr prevCap prevPtr hcap hbound hprev_ne
          G sess st evs1 hf1 bs336 hbs336 capEnc ptrEnc c0 v464 v112 s0 s3 _
          hcl3 (by assumption)
          hpc3 hrun3 hsp3 htr3 hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs3
          fun sf evs hEnv hpc_sf hrun_sf hsp_sf htr_sf hcs_sf => by
            wp_done

/-- Caller-block-polymorphic `withLsCl` form of `archive_over_gen_placed_ok_of_contracts`. -/
theorem archive_over_gen_placed_cl_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hGrow : subroutine_ok (lsProg_51 H) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    subroutine_ok callerProg (lsmpl.base 51)
      (withLsCl lsmpl (ArchiveDefsBudget.archiveOverGenSpec M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (archive_over_gen_placed_ok_of_contracts hC hGrow hRaw hDrop)

end Placed

end LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveNoneBudget
