/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.CliC.SpqrV1.Varint.SkipField3BranchesPlaced
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpecLemmas.ReachesOutcome
import LibsignalBinary.Proofs.TripleRatchet.InImage.Prost

/-!
# Budget-Threaded Relocatable Leaf Cases 1–6 for `CliC` `skip_field [local#6]`

Threads `RustCliAllocBudget M` across the `[LibsignalPlacement]` base and non-group wire-type
branches of `CliC` `skip_field [local#6]` (Block `546`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length skipBytes skipField)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (SkipFieldGhost bv_len_sub_skip bv_ptr_add_skip bv_ptr_add_skip_top cbz_depth_succ
   cbz_depth_zero memRegion_48_split pointsTo64_pair_entails_memRegion16
   sf_truncate32_ofNat64 skipField_depth_zero skipField_succ_endGroup
   skipField_succ_lengthDelimited skipField_succ_sixtyFourBit skipField_succ_thirtyTwoBit
   skipField_succ_varint sliceCursorAfter sliceCursorAt ule_len_of_ge ule_len_of_lt
   w0_and_255_eq)

namespace LibsignalBinary.Proofs.CliC.SpqrV1.Varint.SkipField3BranchesPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsmpl sepWP_seq_lscl
   withLsCl withLsCodeLoaded)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RecordCodecs.Placed (blkLib_eq_546 blkPC_546 blkPl_546 lsProg_546)
open CryptoVerification.SpqrV1.Varint
  (skipBelow3_err skipBelow3_err_entails skipBelow3_leaf skipBelow3_leaf_entails
   stackAt_skipField3)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
  (SkipField3Env skipField3Spec skipField3SpecAt)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv SkipFieldEnv decodeVarintSliceEvents skipFieldEventsCore)

private theorem sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl
private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl
private theorem mem_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).mem = m := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre calleeSavedVRegs_setMem_pre
  mem_setMem_pre

@[local simp, local arm64_norm]
private theorem bv64_sub_zero (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
private theorem bv64_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

attribute [local simp, local arm64_norm] sf_truncate32_ofNat64

@[local simp, local arm64_norm]
private theorem sf_setWidth32_ofNat64 (n : Nat) :
    (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n :=
  sf_truncate32_ofNat64 n

private theorem skipField3Env_of_none {x : SkipFieldGhost} {evs : List AllocEvent}
    (hnone : skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs = none) :
    SkipField3Env x evs ↔ DecodeErrorFromEnv evs := by
  simp [SkipField3Env, SkipFieldEnv, skipFieldEventsCore, hnone, DecodeErrorFromEnv]

private theorem skipField3Env_of_some {x : SkipFieldGhost} {rest : List (BitVec 8)}
    {evs : List AllocEvent}
    (hsome : skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs = some rest) :
    SkipField3Env x evs ↔ evs = [] := by
  simp [SkipField3Env, SkipFieldEnv, skipFieldEventsCore, hsome]

private theorem skipField3Env_varint_of_dv {d tag : Nat} {bufRef slot ptr : BitVec 64}
    {bs : List (BitVec 8)} {evs : List AllocEvent}
    (hdv : DecodeVarint2Env bs evs) :
    SkipField3Env ⟨.varint, tag, d + 1, bufRef, slot, ptr, bs⟩ evs := by
  dsimp [SkipField3Env, SkipFieldEnv, skipFieldEventsCore]
  rw [skipField_succ_varint]
  dsimp [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents] at hdv
  cases hd : decodeVarint bs <;> simpa [hd] using hdv

private theorem decodeErrorFromEnv_of_dv_none {bs : List (BitVec 8)} {evs : List AllocEvent}
    (hd : decodeVarint bs = none) (hdv : DecodeVarint2Env bs evs) :
    DecodeErrorFromEnv evs := by
  simpa [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hd,
    DecodeErrorFromEnv] using hdv

private theorem decodeVarint2Env_eq_nil {bs : List (BitVec 8)} {v : BitVec 64}
    {rest : List (BitVec 8)} {evs : List AllocEvent}
    (hd : decodeVarint bs = some (v, rest)) (hdv : DecodeVarint2Env bs evs) :
    evs = [] := by
  simpa [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hd] using hdv

theorem subroutine_ok_skipField3_or_lscl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64} {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (h1 : subroutine_ok prog entry (withLsCodeLoaded lsmpl (skipField3SpecAt A lim depth P)))
    (h2 : subroutine_ok prog entry (withLsCodeLoaded lsmpl (skipField3SpecAt A lim depth Q))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (skipField3SpecAt A lim depth (fun x => P x ∨ Q x))) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hPQ, hrest⟩, hmem⟩
  rcases hPQ with hP | hQ
  · refine h1.mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    dsimp only [withLsCodeLoaded]
    simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hP, hrest⟩, hmem⟩
  · refine h2.mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    dsimp only [withLsCodeLoaded]
    simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hQ, hrest⟩, hmem⟩

theorem subroutine_ok_skipField3_imp_lscl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64} {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (himp : ∀ x, P x → Q x)
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl (skipField3SpecAt A lim depth Q))) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (skipField3SpecAt A lim depth P)) := by
  refine subroutine_ok_mono h (fun ⟨x, st⟩ R s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  dsimp only [withLsCodeLoaded] at hpre ⊢
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨⟨himp x hpre.1.1, hpre.1.2⟩, hpre.2⟩

theorem skipField3SpecAt_reaches_outcome_eq_lscl [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (P : SkipFieldGhost → Prop) (x : SkipFieldGhost) (st : M.σ) (R : SepProp) (s0 : State) :
    reaches_outcome prog (withLsCodeLoaded lsmpl (skipField3SpecAt A lim x.depth P)) (x, st) R s0 s0 =
      reaches_outcome prog (withLsCodeLoaded lsmpl (skipField3Spec A lim)) (x, st) R s0 s0 := by
  have hpost : (withLsCodeLoaded lsmpl (skipField3SpecAt A lim x.depth P)).post (x, st) =
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)).post (x, st) := rfl
  have hpan : (withLsCodeLoaded lsmpl (skipField3SpecAt A lim x.depth P)).onPanic (x, st) =
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)).onPanic (x, st) := rfl
  have hexit : (withLsCodeLoaded lsmpl (skipField3SpecAt A lim x.depth P)).onExit (x, st) =
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)).onExit (x, st) := rfl
  have hoom : (withLsCodeLoaded lsmpl (skipField3SpecAt A lim x.depth P)).onOom (x, st) =
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)).onOom (x, st) := rfl
  have hout : ∀ sf,
      SubroutineOutcome (withLsCodeLoaded lsmpl (skipField3SpecAt A lim x.depth P)) (x, st) R s0 sf =
      SubroutineOutcome (withLsCodeLoaded lsmpl (skipField3Spec A lim)) (x, st) R s0 sf := by
    intro sf; dsimp only [SubroutineOutcome]; rw [hpost, hpan, hexit, hoom]
  exact propext ⟨fun h => h.mono_outcome (fun sf hs => hout sf ▸ hs),
    fun h => h.mono_outcome (fun sf hs => (hout sf).symm ▸ hs)⟩

theorem subroutine_ok_skipField3Spec_of_at_depth_lscl [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : ∀ depth, depth < 2 ^ 32 →
      subroutine_ok prog entry
        (withLsCodeLoaded lsmpl (skipField3SpecAt A lim depth (fun _ => True)))) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (skipField3Spec A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' := hpre
  dsimp only [withLsCodeLoaded] at hpre'
  simp only [skipField3Spec, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  have hdepth : x.depth < 2 ^ 32 := hpre'.1.2.2.2.2.2.1
  refine (h x.depth hdepth).mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withLsCodeLoaded]
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨trivial, trivial, hpre'.1⟩, hpre'.2⟩

set_option hygiene false in
local macro "wp_steps_lscl_sync_pool " hcl:term:max mid:term:max hclOut:ident : tactic => `(tactic| (
  apply sepWP_seq_lscl $hcl (mid := $mid)
  wp_steps_sync_pool $mid
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun $hclOut => ?_
  simp only [State.setMem_setMem, mem_setMem_pre] at $hclOut ⊢))

set_option hygiene false in
local macro "skipField3_546_top_err_call_budget"
    fromTarget:term:max wtTerm:term:max depthTerm:term:max hdepthTerm:term:max kind:term:max : tactic => `(tactic| (
  have hfits_from : FitsEnv M lim st DecodeErrorFromEnv := fun evs hevs =>
    hfits_top evs ((skipField3Env_of_none hnone_top).mpr hevs)
  have hknh : KindNoHeap $kind := by decide
  conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v_err0
  wp_steps_lscl_sync_pool hcl0 $fromTarget hcl1
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
  conv => arg 4; rw [skipBelow3_err s0.sp $depthTerm $hdepthTerm]
  wp_call hFromCall (s0.sp - 96#64, $kind, st)
  have hsp_sf : sf.sp = s0.sp - 96#64 := by
    refine Eq.trans ‹sf.sp = _› ?_; wp_norm_lhs
  have hevs_top :=
    (skipField3Env_of_none (x := ⟨$wtTerm, tag, $depthTerm, bufRef, slot, ptr, bs⟩) hnone_top).mpr
      ‹DecodeErrorFromEnv _›
  conv => arg 4; simp only [hsp_sf]
  apply SepWP.fold (skipBelow3_err_entails s0.sp $depthTerm $hdepthTerm) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  wp_done))

/-! ## Case 1: `depth = 0` (`RecursionLimitReached`) -/

theorem skipField3_depth_zero_placed_ok
    [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_546 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpec M A lim))) :
    subroutine_ok (lsProg_546 H) (blkPl_546).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A lim 0 (fun _ => True))) := by
  dsimp only [withLsCl, decodeErrorFromBudgetSpec] at hFromCall
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipField3SpecAt
    simp only [sliceCursorAt, stackAt_skipField3 _ 0 (by decide),
      sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init g s0
  rcases g with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  subst ‹depth = 0›
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hfits_top : FitsEnv M lim st (SkipField3Env ⟨wt, tag, 0, bufRef, slot, ptr, bs⟩) := by
    assumption
  have hcbz := cbz_depth_zero ‹(s0.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 0›
  have hnone_top : skipField (2 * bs.length + 2) 0 tag wt bs = none := skipField_depth_zero _ _ _ _
  rw [hnone_top]; dsimp only
  skipField3_546_top_err_call_budget (lsmpl.base 261) wt 0 (by decide) 0x8000000000000002#64

/-! ## Case 2: `depth = d + 1`, `wt = .endGroup` (`UnexpectedEndGroupTag`) -/

theorem skipField3_endGroup_placed_ok
    [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_546 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (lsProg_546 H) (blkPl_546).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A lim (d + 1) (fun x => x.wt = .endGroup))) := by
  dsimp only [withLsCl, decodeErrorFromBudgetSpec] at hFromCall
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipField3SpecAt
    simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init g s0
  rcases g with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  subst ‹wt = .endGroup›
  subst ‹depth = d + 1›
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hfits_top : FitsEnv M lim st (SkipField3Env ⟨.endGroup, tag, d + 1, bufRef, slot, ptr, bs⟩) := by
    assumption
  have hcbz := cbz_depth_succ ‹(s0.readReg64 (Reg.gpr 3#5)).setWidth 32 = BitVec.ofNat 32 (d + 1)› hdepth
  have hw0 := w0_and_255_eq ‹(s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 WireType.endGroup.toNat›
  dsimp [CryptoVerification.LibsignalProtoCodec.WireType.toNat] at hw0
  have hnone_top : skipField (2 * bs.length + 2) (d + 1) tag .endGroup bs = none :=
    skipField_succ_endGroup _ _ _ _
  rw [hnone_top]; dsimp only
  skipField3_546_top_err_call_budget (lsmpl.base 261) .endGroup (d + 1) hdepth 0x8000000000000009#64

/-! ## Cases 3 & 4: `wt = .sixtyFourBit` (`skipBytes 8`) / `.thirtyTwoBit` (`skipBytes 4`) -/

set_option hygiene false in
local macro "skipField3_546_fixedWidth_body_budget"
    fromTarget:term:max wtVal:term:max nNat:term:max nBv:term:max skipLem:ident : tactic => `(tactic| (
  dsimp only [withLsCl, decodeErrorFromBudgetSpec] at hFromCall
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipField3SpecAt
    simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init g s0
  rcases g with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  subst ‹wt = $wtVal›
  subst ‹depth = d + 1›
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_lt : bs.length < 2 ^ 63 := ‹bs.length < 2 ^ 63›
  have hfits_top : FitsEnv M lim st (SkipField3Env ⟨$wtVal, tag, d + 1, bufRef, slot, ptr, bs⟩) := by
    assumption
  have hcbz := cbz_depth_succ ‹(s0.readReg64 (Reg.gpr 3#5)).setWidth 32 = BitVec.ofNat 32 (d + 1)› hdepth
  have hw0 := w0_and_255_eq ‹(s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = _›
  dsimp [CryptoVerification.LibsignalProtoCodec.WireType.toNat] at hw0
  by_cases hlt : bs.length < $nNat
  · have hule := ule_len_of_lt (n := $nBv) hlt hlen_lt
    have hnone_top : skipField (2 * bs.length + 2) (d + 1) tag $wtVal bs = none := by
      rw [$skipLem:ident]; simp [skipBytes, hlt]
    rw [hnone_top]; dsimp only
    skipField3_546_top_err_call_budget $fromTarget $wtVal (d + 1) hdepth 0x8000000000000007#64
  · have _ := hcl0
    have hule := ule_len_of_ge (n := $nBv) hlt hlen_lt
    have hsub := bv_len_sub_skip (n := $nBv) hlt
    have hadd := bv_ptr_add_skip_top (ptr := ptr) (n := $nBv) hlt
    have hsome_top : skipField (2 * bs.length + 2) (d + 1) tag $wtVal bs = some (bs.drop $nNat) := by
      rw [$skipLem:ident]; simp [skipBytes, hlt]
    have hevs_top : SkipField3Env ⟨$wtVal, tag, d + 1, bufRef, slot, ptr, bs⟩ [] :=
      (skipField3Env_of_some hsome_top).mpr rfl
    rw [hsome_top]; dsimp only
    simp only [sliceCursorAfter]
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    conv => arg 4; rw [show A.pool lim st = A.pool lim (M.stepEvents ([] : List AllocEvent) st) from rfl]
    wp_done))

theorem skipField3_sixtyFourBit_placed_ok
    [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_546 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (lsProg_546 H) (blkPl_546).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A lim (d + 1) (fun x => x.wt = .sixtyFourBit))) := by
  skipField3_546_fixedWidth_body_budget
    (lsmpl.base 261) .sixtyFourBit 8 8#64 skipField_succ_sixtyFourBit

theorem skipField3_thirtyTwoBit_placed_ok
    [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_546 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (lsProg_546 H) (blkPl_546).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A lim (d + 1) (fun x => x.wt = .thirtyTwoBit))) := by
  skipField3_546_fixedWidth_body_budget
    (lsmpl.base 261) .thirtyTwoBit 4 4#64 skipField_succ_thirtyTwoBit

/-! ## Case 5: `depth = d + 1`, `wt = .varint` -/

theorem skipField3_varint_placed_ok
    [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hVarintCall : subroutine_ok (lsProg_546 H) (lsmpl.base 559)
      (withLsCl lsmpl (decodeVarint2Spec A lim)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (lsProg_546 H) (blkPl_546).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A lim (d + 1) (fun x => x.wt = .varint))) := by
  dsimp only [withLsCl, decodeVarint2Spec, decodeVarint2SpecGen] at hVarintCall
  simp only [show 0x40 + (0x40 + decodeErrorHookStack) =
      CryptoVerification.SpqrV1.Varint.decodeVarint2Stack from rfl] at hVarintCall
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipField3SpecAt
    simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init g s0
  rcases g with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  subst ‹wt = .varint›
  subst ‹depth = d + 1›
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_lt : bs.length < 2 ^ 63 := ‹bs.length < 2 ^ 63›
  have hfits_top : FitsEnv M lim st (SkipField3Env ⟨.varint, tag, d + 1, bufRef, slot, ptr, bs⟩) := by
    assumption
  have hfits_dv : FitsEnv M lim st (DecodeVarint2Env bs) := by
    intro evs hevs
    apply hfits_top evs
    dsimp [SkipField3Env, SkipFieldEnv, skipFieldEventsCore]
    rw [skipField_succ_varint]
    dsimp [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents] at hevs
    cases hd_c : decodeVarint bs <;> simpa [hd_c] using hevs
  have hcbz := cbz_depth_succ ‹(s0.readReg64 (Reg.gpr 3#5)).setWidth 32 = BitVec.ofNat 32 (d + 1)› hdepth
  have hw0 := w0_and_255_eq ‹(s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = _›
  dsimp [CryptoVerification.LibsignalProtoCodec.WireType.toNat] at hw0
  rw [skipField_succ_varint]
  conv => arg 4; rw [skipBelow3_leaf s0.sp (d + 1) hdepth]
  wp_steps_lscl_sync_pool hcl0 (lsmpl.base 559) hcl1
  apply SepWP.fold (Entails.of_eq (show ((slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs)) = sliceCursorAt slot ptr bs from rfl)) (by sep_focus)
  wp_call hVarintCall (⟨bufRef, slot, ptr, bs⟩, st)
  have hsp_sf : sf.sp = s0.sp - 96#64 := by
    refine Eq.trans ‹sf.sp = _› ?_; wp_norm_lhs
  have hevs_top :=
    skipField3Env_varint_of_dv (d := d) (tag := tag) (bufRef := bufRef) (slot := slot) (ptr := ptr)
      ‹DecodeVarint2Env bs _›
  cases hd : decodeVarint bs with
  | none =>
    conv => arg 4; simp only [Option.map, sepConj_assoc]
    wp_focus_pure; intro _hx0_sf
    wp_focus_pure; intro _hx1_sf
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem, Option.map]
    wp_done
  | some p =>
    rcases p with ⟨_v, rest⟩
    have hevs_nil := decodeVarint2Env_eq_nil hd ‹DecodeVarint2Env bs _›
    rw [hevs_nil] at hevs_top
    conv => arg 4; simp only [hevs_nil, LibsignalBinary.Heap.AllocCostModel.stepEvents, List.foldl, Option.map, sliceCursorAfter, sepConj_assoc]
    wp_focus_pure; rintro ⟨_hx0_sf, _hx1_sf⟩
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem, Option.map, sliceCursorAfter]
    conv => arg 4; rw [show A.pool lim st = A.pool lim (M.stepEvents ([] : List AllocEvent) st) from rfl]
    wp_done

/-! ## Case 6: `depth = d + 1`, `wt = .lengthDelimited` -/

theorem skipField3_lengthDelimited_placed_ok
    [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_546 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok (lsProg_546 H) (lsmpl.base 559)
      (withLsCl lsmpl (decodeVarint2Spec A lim)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (lsProg_546 H) (blkPl_546).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A lim (d + 1) (fun x => x.wt = .lengthDelimited))) := by
  dsimp only [withLsCl, decodeErrorFromBudgetSpec] at hFromCall
  dsimp only [withLsCl, decodeVarint2Spec, decodeVarint2SpecGen] at hVarintCall
  simp only [show 0x40 + (0x40 + decodeErrorHookStack) =
      CryptoVerification.SpqrV1.Varint.decodeVarint2Stack from rfl] at hVarintCall
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipField3SpecAt
    simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init g s0
  rcases g with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  subst ‹wt = .lengthDelimited›
  subst ‹depth = d + 1›
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_lt : bs.length < 2 ^ 63 := ‹bs.length < 2 ^ 63›
  have hfits_top :
      FitsEnv M lim st (SkipField3Env ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, bs⟩) := by
    assumption
  have hfits_dv : FitsEnv M lim st (DecodeVarint2Env bs) := by
    intro evs hevs
    dsimp [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents] at hevs
    cases hd_c : decodeVarint bs with
    | some _ =>
      rw [hd_c] at hevs; subst hevs; trivial
    | none =>
      rw [hd_c] at hevs
      apply hfits_top evs
      dsimp [SkipField3Env, SkipFieldEnv, skipFieldEventsCore]
      rw [skipField_succ_lengthDelimited, hd_c]
      exact hevs
  have hcbz := cbz_depth_succ ‹(s0.readReg64 (Reg.gpr 3#5)).setWidth 32 = BitVec.ofNat 32 (d + 1)› hdepth
  have hw0 := w0_and_255_eq ‹(s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = _›
  dsimp [CryptoVerification.LibsignalProtoCodec.WireType.toNat] at hw0
  rw [skipField_succ_lengthDelimited]
  conv => arg 4; rw [skipBelow3_leaf s0.sp (d + 1) hdepth]
  wp_steps_lscl_sync_pool hcl0 (lsmpl.base 559) hcl1
  apply SepWP.fold (Entails.of_eq (show ((slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs)) = sliceCursorAt slot ptr bs from rfl)) (by sep_focus)
  wp_call hVarintCall (⟨bufRef, slot, ptr, bs⟩, st)
  have hcl2 : LibsignalCodeLoaded lsmpl sf.mem := by assumption
  have hsp_sf : sf.sp = s0.sp - 96#64 := by
    refine Eq.trans ‹sf.sp = _› ?_; wp_norm_lhs
  have _htr_sf : sf.trace = s0.trace := by
    refine Eq.trans ‹sf.trace = _› ?_; wp_norm_lhs
  have _hx29_sf : sf.readReg64 .x29 = s0.sp - 48#64 := by
    refine Eq.trans ‹sf.readReg64 (Reg.gpr 29#5) = _› ?_; wp_norm_lhs
  have _hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    refine Eq.trans ‹calleeSavedVRegs sf = _› ?_; wp_norm_lhs
  cases hd : decodeVarint bs with
  | none =>
    have _ := hcl2
    have hnone_top :
        skipField (2 * bs.length + 2) (d + 1) tag .lengthDelimited bs = none := by
      rw [skipField_succ_lengthDelimited, hd]
    have hevs_top :=
      (skipField3Env_of_none (x := ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, bs⟩) hnone_top).mpr
        (decodeErrorFromEnv_of_dv_none hd ‹DecodeVarint2Env bs _›)
    conv => arg 4; simp only [sepConj_assoc]
    wp_focus_pure; intro _hx0_sf
    wp_focus_pure; intro _hx1_sf
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  | some p =>
    rcases p with ⟨len, rest⟩
    have hevs_nil := decodeVarint2Env_eq_nil hd ‹DecodeVarint2Env bs _›
    conv => arg 4; rw [hevs_nil]; dsimp only [LibsignalBinary.Heap.AllocCostModel.stepEvents, List.foldl]
    have hrest_le : rest.length ≤ bs.length := Nat.le_of_lt (decodeVarint_length hd)
    have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hlen_lt
    by_cases hlt : rest.length < len.toNat
    · have hule := ule_len_of_lt hlt hrest_lt
      have hnone_top :
          skipField (2 * bs.length + 2) (d + 1) tag .lengthDelimited bs = none := by
        rw [skipField_succ_lengthDelimited, hd]; simp [skipBytes, hlt]
      have hfits_from : FitsEnv M lim st DecodeErrorFromEnv := fun evs hevs =>
        hfits_top evs ((skipField3Env_of_none hnone_top).mpr hevs)
      have hknh : KindNoHeap 0x8000000000000007#64 := by decide
      conv => arg 4; simp only [sliceCursorAfter, sepConj_assoc]
      wp_focus_pure; rintro ⟨_hx0_sf, _hx1_sf⟩
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
      conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro v_err0
      wp_steps_lscl_sync_pool hcl2 (lsmpl.base 261) hcl3
      apply SepWP.fold
        (pointsTo64_pair_entails_memRegion16 slot
          (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length))
        (by sep_focus)
      conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth]
      wp_call hFromCall (s0.sp - 96#64, 0x8000000000000007#64, st)
      have _hsp_sf1 : sf_1.sp = s0.sp - 96#64 := by
        refine Eq.trans ‹sf_1.sp = _› ?_; simp only [arm64_norm, wp_norm, hsp_sf]
      have hevs_top : SkipField3Env ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, bs⟩ _ :=
        (skipField3Env_of_none hnone_top).mpr ‹DecodeErrorFromEnv _›
      apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
      simp only [State.setMem_setMem, skipBytes, hlt, ↓reduceIte]
      wp_done
    · have _ := hcl2
      have hule := ule_len_of_ge hlt hrest_lt
      have hsub := bv_len_sub_skip hlt
      have hadd := bv_ptr_add_skip (ptr := ptr) hrest_le hlt
      have hsome_top :
          skipField (2 * bs.length + 2) (d + 1) tag .lengthDelimited bs =
            some (rest.drop len.toNat) := by
        rw [skipField_succ_lengthDelimited, hd]; simp [skipBytes, hlt]
      have hevs_top : SkipField3Env ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, bs⟩ [] :=
        (skipField3Env_of_some hsome_top).mpr rfl
      conv => arg 4; simp only [sliceCursorAfter, sepConj_assoc]
      wp_focus_pure; rintro ⟨_hx0_sf, _hx1_sf⟩
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
      simp only [State.setMem_setMem, skipBytes, hlt, ↓reduceIte, sliceCursorAfter]
      conv => arg 4; rw [show A.pool lim st = A.pool lim (M.stepEvents ([] : List AllocEvent) st) from rfl]
      wp_done

end LibsignalBinary.Proofs.CliC.SpqrV1.Varint.SkipField3BranchesPlacedBudget
