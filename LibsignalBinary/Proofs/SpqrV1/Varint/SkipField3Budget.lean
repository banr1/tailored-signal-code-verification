/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpecLemmas.ReachesOutcome
import LibsignalBinary.Proofs.TripleRatchet.InImage.Prost

/-!
# Budget-Threaded `prost::encoding::skip_field::<&mut &[u8]> [local#3]`

Defines `SkipField3Env` and `skipField3Spec`, and proves `[LibsignalPlacement]`
`RustCliAllocBudget`-threaded correctness across all `WireType` cases by induction on `depth`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint decodeVarint_length skipBytes skipField skipGroup skip_length)
open CryptoVerification.LibsignalTripleRatchet (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack)
open CryptoVerification.LibsignalTripleRatchet.Prost (IsDropSuffix SkipFieldGhost bv32_sub_one_zeroExtend bv32_zeroExtend_ofNat bv_len_sub_skip bv_ptr_add_skip bv_ptr_add_skip_top cbz_depth_succ cbz_depth_zero decodeVarint_suffix itag_beq_tag_false iwt_beq_4_false iwt_w0_setWidth8 key_shr32_of_ge key_shr32_of_lt key_wt_none key_wt_some memRegion_48_split memRegion_48_split2 pointsTo64_memRegion32_entails_40 pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join sf_truncate32_ofNat64 skipField_depth_zero skipField_succ_endGroup skipField_succ_lengthDelimited skipField_succ_sixtyFourBit skipField_succ_startGroup skipField_succ_thirtyTwoBit skipField_succ_varint skipGroup_of_decodeVarint_none skipGroup_of_endGroup skipGroup_of_key_ge skipGroup_of_ne_endGroup skipGroup_of_tag_zero skipGroup_of_wt_none skip_suffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt suffix_trans tag_cbz_false ule_len_of_ge ule_len_of_lt w0_and_255_eq w1_tag_eq)

namespace LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkLib_eq_263 blkPC_263 blkPl_263 lsmpl)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Varint
  (HighCalleeSaved3 skipBelow3 skipBelow3_err skipBelow3_err_entails skipBelow3_leaf
   skipBelow3_leaf_entails skipField3Stack stackAt_skipField3)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustAllocEvents)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (DecodeVarint2Env decodeVarint2Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv SkipFieldEnv decodeVarintSliceEvents skipFieldEventsCore)

private theorem sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
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

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre calleeSavedVRegs_setMem_pre

@[local simp, local arm64_norm]
private theorem bv64_sub_zero (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
private theorem bv64_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

@[local simp, local arm64_norm]
private theorem trunc32_zext64_and_255 (x : BitVec 64) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x) &&& 255#64) =
      BitVec.setWidth 32 x &&& 255#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

attribute [local simp, local arm64_norm] sf_truncate32_ofNat64

@[local simp, local arm64_norm]
private theorem sf_setWidth32_ofNat64 (n : Nat) :
    (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n :=
  sf_truncate32_ofNat64 n

@[local simp, local arm64_norm]
private theorem iwt_w0_setWidth8_1 (iwt : WireType) :
    (BitVec.zeroExtend 64 ((BitVec.ofNat 64 iwt.toNat).setWidth 32)).setWidth 8 =
      BitVec.ofNat 8 iwt.toNat :=
  (iwt_w0_setWidth8 iwt).1

@[local simp, local arm64_norm]
private theorem iwt_w0_setWidth8_2 (iwt : WireType) :
    (BitVec.ofNat 64 iwt.toNat).setWidth 8 = BitVec.ofNat 8 iwt.toNat :=
  (iwt_w0_setWidth8 iwt).2

/-! ## Envelope, Specifications, and Combinators -/

/-- Callee-fixed allocator event envelope of `skip_field::<&mut &[u8]> [local#3]`. -/
abbrev SkipField3Env (x : SkipFieldGhost) (evs : List AllocEvent) : Prop :=
  SkipFieldEnv x evs

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

private theorem skipField3Env_of_decodeErrorFrom {tag d : Nat} {bufRef slot ptr : BitVec 64}
    {bs : List (BitVec 8)} {evs : List AllocEvent}
    (hnone_top : skipField (2 * bs.length + 2) (d + 1) tag .startGroup bs = none)
    (hevs : DecodeErrorFromEnv evs) :
    SkipField3Env ⟨.startGroup, tag, d + 1, bufRef, slot, ptr, bs⟩ evs :=
  (skipField3Env_of_none hnone_top).mpr hevs

private theorem skipField3Env_of_rec_none {iwt : WireType} {itag tag d : Nat}
    {bufRef slot rptr ptr : BitVec 64} {rest bs : List (BitVec 8)} {evs : List AllocEvent}
    (hs : skipField (2 * rest.length + 2) d itag iwt rest = none)
    (hnone_top : skipField (2 * bs.length + 2) (d + 1) tag .startGroup bs = none)
    (hevs : SkipField3Env ⟨iwt, itag, d, bufRef, slot, rptr, rest⟩ evs) :
    SkipField3Env ⟨.startGroup, tag, d + 1, bufRef, slot, ptr, bs⟩ evs :=
  (skipField3Env_of_none hnone_top).mpr
    ((skipField3Env_of_none (x := ⟨iwt, itag, d, bufRef, slot, rptr, rest⟩) hs).mp hevs)

/-- Budget-threaded contract of `prost::encoding::skip_field::<&mut &[u8]> [local#3]` (Block `263`). -/
def skipField3Spec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SkipFieldGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.tag ∧ x.tag < 2 ^ 32 ∧
      s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 x.depth ∧ x.depth < 2 ^ 32 ∧
      x.bs.length < 2 ^ 63 ∧ FitsEnv M lim st (SkipField3Env x)⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp (skipField3Stack x.depth)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜SkipField3Env x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (skipField3Stack x.depth) ∗
      match skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs with
      | some rest =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Case-restricted budget-threaded contract for `skip_field [local#3]` at fixed `depth`. -/
def skipField3SpecAt {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (depth : Nat) (P : SkipFieldGhost → Prop) :
    Spec (SkipFieldGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜P x ∧ x.depth = depth ∧
      (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.tag ∧ x.tag < 2 ^ 32 ∧
      s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 depth ∧ depth < 2 ^ 32 ∧
      x.bs.length < 2 ^ 63 ∧ FitsEnv M lim st (SkipField3Env x)⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp (skipField3Stack depth)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜SkipField3Env x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (skipField3Stack depth) ∗
      match skipField (2 * x.bs.length + 2) depth x.tag x.wt x.bs with
      | some rest =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

theorem subroutine_ok_skipField3_or {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (h1 : subroutine_ok prog entry (skipField3SpecAt A lim depth P))
    (h2 : subroutine_ok prog entry (skipField3SpecAt A lim depth Q)) :
    subroutine_ok prog entry (skipField3SpecAt A lim depth (fun x => P x ∨ Q x)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre.1.1 with hP | hQ
  · refine h1.mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hP, hpre.1.2⟩, hpre.2⟩
  · refine h2.mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hQ, hpre.1.2⟩, hpre.2⟩

theorem subroutine_ok_skipField3_imp {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (himp : ∀ x, P x → Q x)
    (h : subroutine_ok prog entry (skipField3SpecAt A lim depth Q)) :
    subroutine_ok prog entry (skipField3SpecAt A lim depth P) := by
  refine subroutine_ok_mono h (fun ⟨x, st⟩ R s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨⟨himp x hpre.1.1, hpre.1.2⟩, hpre.2⟩

/-! ## Case 1: `depth = 0` (`RecursionLimitReached`) -/

set_option hygiene false in
local macro "skipField3_top_err_call_budget"
    fromTarget:term:max wtTerm:term:max depthTerm:term:max hdepthTerm:term:max kind:term:max : tactic => `(tactic| (
  have hfits_from : FitsEnv M lim st DecodeErrorFromEnv := fun evs hevs =>
    hfits_top evs ((skipField3Env_of_none hnone_top).mpr hevs)
  have hknh : KindNoHeap $kind := by decide
  conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v_err0
  wp_steps_sync_pool $fromTarget
  simp only [State.setMem_setMem]
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

theorem skipField3_depth_zero_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base
      (skipField3SpecAt A lim 0 (fun _ => True)) := by
  dsimp only [decodeErrorFromBudgetSpec] at hFromCall
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ 0 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init g s0
  rcases g with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  subst ‹depth = 0›
  have hfits_top : FitsEnv M lim st (SkipField3Env ⟨wt, tag, 0, bufRef, slot, ptr, bs⟩) := by
    assumption
  have hcbz := cbz_depth_zero ‹(s0.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 0›
  have hnone_top : skipField (2 * bs.length + 2) 0 tag wt bs = none := skipField_depth_zero _ _ _ _
  rw [hnone_top]; dsimp only
  skipField3_top_err_call_budget (lsmpl.base 261) wt 0 (by decide) 0x8000000000000002#64

/-! ## Case 2: `depth = d + 1`, `wt = .endGroup` (`UnexpectedEndGroupTag`) -/

theorem skipField3_endGroup_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base
      (skipField3SpecAt A lim (d + 1) (fun x => x.wt = .endGroup)) := by
  dsimp only [decodeErrorFromBudgetSpec] at hFromCall
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init g s0
  rcases g with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  subst ‹wt = .endGroup›
  subst ‹depth = d + 1›
  have hfits_top : FitsEnv M lim st (SkipField3Env ⟨.endGroup, tag, d + 1, bufRef, slot, ptr, bs⟩) := by
    assumption
  have hcbz := cbz_depth_succ ‹(s0.readReg64 (Reg.gpr 3#5)).setWidth 32 = BitVec.ofNat 32 (d + 1)› hdepth
  have hw0 := w0_and_255_eq ‹(s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 WireType.endGroup.toNat›
  dsimp [CryptoVerification.LibsignalProtoCodec.WireType.toNat] at hw0
  have hnone_top : skipField (2 * bs.length + 2) (d + 1) tag .endGroup bs = none :=
    skipField_succ_endGroup _ _ _ _
  rw [hnone_top]; dsimp only
  skipField3_top_err_call_budget (lsmpl.base 261) .endGroup (d + 1) hdepth 0x8000000000000009#64

/-! ## Cases 3 & 4: `wt = .sixtyFourBit` / `.thirtyTwoBit` -/

set_option hygiene false in
local macro "skipField3_fixedWidth_body_budget"
    fromTarget:term:max wtVal:term:max nNat:term:max nBv:term:max skipLem:ident : tactic => `(tactic| (
  dsimp only [decodeErrorFromBudgetSpec] at hFromCall
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init g s0
  rcases g with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  subst ‹wt = $wtVal›
  subst ‹depth = d + 1›
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
    skipField3_top_err_call_budget $fromTarget $wtVal (d + 1) hdepth 0x8000000000000007#64
  · have hule := ule_len_of_ge (n := $nBv) hlt hlen_lt
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

theorem skipField3_sixtyFourBit_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base
      (skipField3SpecAt A lim (d + 1) (fun x => x.wt = .sixtyFourBit)) := by
  skipField3_fixedWidth_body_budget (lsmpl.base 261) .sixtyFourBit 8 8#64 skipField_succ_sixtyFourBit

theorem skipField3_thirtyTwoBit_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base
      (skipField3SpecAt A lim (d + 1) (fun x => x.wt = .thirtyTwoBit)) := by
  skipField3_fixedWidth_body_budget (lsmpl.base 261) .thirtyTwoBit 4 4#64 skipField_succ_thirtyTwoBit

/-! ## Case 5: `depth = d + 1`, `wt = .varint` -/

theorem skipField3_varint_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hVarintCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 291) (decodeVarint2Spec A lim))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base
      (skipField3SpecAt A lim (d + 1) (fun x => x.wt = .varint)) := by
  dsimp only [decodeVarint2Spec, DecodeVarint2Budget.decodeVarint2SpecGen] at hVarintCall
  simp only [show 0x40 + (0x40 + decodeErrorHookStack) =
      CryptoVerification.SpqrV1.Varint.decodeVarint2Stack from rfl] at hVarintCall
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init g s0
  rcases g with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  subst ‹wt = .varint›
  subst ‹depth = d + 1›
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
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
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
    wp_focus_pure; intro hx0_sf
    wp_focus_pure; intro hx1_sf
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem, Option.map]
    wp_done
  | some p =>
    rcases p with ⟨v, rest⟩
    have hevs_nil := decodeVarint2Env_eq_nil hd ‹DecodeVarint2Env bs _›
    rw [hevs_nil] at hevs_top
    conv => arg 4; simp only [hevs_nil, LibsignalBinary.Heap.AllocCostModel.stepEvents, List.foldl, Option.map, sliceCursorAfter, sepConj_assoc]
    wp_focus_pure; rintro ⟨hx0_sf, hx1_sf⟩
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem, Option.map, sliceCursorAfter]
    conv => arg 4; rw [show A.pool lim st = A.pool lim (M.stepEvents ([] : List AllocEvent) st) from rfl]
    wp_done

/-! ## Case 6: `depth = d + 1`, `wt = .lengthDelimited` -/

theorem skipField3_lengthDelimited_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    (hVarintCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 291) (decodeVarint2Spec A lim))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base
      (skipField3SpecAt A lim (d + 1) (fun x => x.wt = .lengthDelimited)) := by
  dsimp only [decodeErrorFromBudgetSpec] at hFromCall
  dsimp only [decodeVarint2Spec, DecodeVarint2Budget.decodeVarint2SpecGen] at hVarintCall
  simp only [show 0x40 + (0x40 + decodeErrorHookStack) =
      CryptoVerification.SpqrV1.Varint.decodeVarint2Stack from rfl] at hVarintCall
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init g s0
  rcases g with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  subst ‹wt = .lengthDelimited›
  subst ‹depth = d + 1›
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
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  apply SepWP.fold (Entails.of_eq (show ((slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs)) = sliceCursorAt slot ptr bs from rfl)) (by sep_focus)
  wp_call hVarintCall (⟨bufRef, slot, ptr, bs⟩, st)
  have hsp_sf : sf.sp = s0.sp - 96#64 := by
    refine Eq.trans ‹sf.sp = _› ?_; wp_norm_lhs
  have htr_sf : sf.trace = s0.trace := by
    refine Eq.trans ‹sf.trace = _› ?_; wp_norm_lhs
  have hx29_sf : sf.readReg64 .x29 = s0.sp - 48#64 := by
    refine Eq.trans ‹sf.readReg64 (Reg.gpr 29#5) = _› ?_; wp_norm_lhs
  have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    refine Eq.trans ‹calleeSavedVRegs sf = _› ?_; wp_norm_lhs
  cases hd : decodeVarint bs with
  | none =>
    have hnone_top :
        skipField (2 * bs.length + 2) (d + 1) tag .lengthDelimited bs = none := by
      rw [skipField_succ_lengthDelimited, hd]
    have hevs_top :=
      (skipField3Env_of_none (x := ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, bs⟩) hnone_top).mpr
        (decodeErrorFromEnv_of_dv_none hd ‹DecodeVarint2Env bs _›)
    conv => arg 4; simp only [sepConj_assoc]
    wp_focus_pure; intro hx0_sf
    wp_focus_pure; intro hx1_sf
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
      wp_focus_pure; rintro ⟨hx0_sf, hx1_sf⟩
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
      conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro v_err0
      wp_steps_sync_pool (lsmpl.base 261)
      simp only [State.setMem_setMem]
      apply SepWP.fold
        (pointsTo64_pair_entails_memRegion16 slot
          (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length))
        (by sep_focus)
      conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth]
      wp_call hFromCall (s0.sp - 96#64, 0x8000000000000007#64, st)
      have hsp_sf1 : sf_1.sp = s0.sp - 96#64 := by
        refine Eq.trans ‹sf_1.sp = _› ?_; simp only [arm64_norm, wp_norm, hsp_sf]
      have hevs_top : SkipField3Env ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, bs⟩ _ :=
        (skipField3Env_of_none hnone_top).mpr ‹DecodeErrorFromEnv _›
      apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
      simp only [State.setMem_setMem, skipBytes, hlt, ↓reduceIte]
      wp_done
    · have hule := ule_len_of_ge hlt hrest_lt
      have hsub := bv_len_sub_skip hlt
      have hadd := bv_ptr_add_skip (ptr := ptr) hrest_le hlt
      have hsome_top :
          skipField (2 * bs.length + 2) (d + 1) tag .lengthDelimited bs =
            some (rest.drop len.toNat) := by
        rw [skipField_succ_lengthDelimited, hd]; simp [skipBytes, hlt]
      have hevs_top : SkipField3Env ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, bs⟩ [] :=
        (skipField3Env_of_some hsome_top).mpr rfl
      conv => arg 4; simp only [sliceCursorAfter, sepConj_assoc]
      wp_focus_pure; rintro ⟨hx0_sf, hx1_sf⟩
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
      simp only [State.setMem_setMem, skipBytes, hlt, ↓reduceIte, sliceCursorAfter]
      conv => arg 4; rw [show A.pool lim st = A.pool lim (M.stepEvents ([] : List AllocEvent) st) from rfl]
      wp_done

/-! ## Case 7: `depth = d + 1`, `wt = .startGroup` -/

abbrev skipGroupLoopPre3 {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State) (d : Nat)
    (bufRef slot ptr v_pad : BitVec 64) (bs cur : List (BitVec 8)) : SepProp :=
  A.pool lim st s ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗
    memRegion (s0.sp - 96#64) 48 ∗ ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗ ((s0.sp - 24#64) ↦₆₄ v_pad) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗ skipBelow3 s0.sp (d + 1)

private abbrev skipGroupErrPost3 {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st' : M.σ) (s0 se : State) (d : Nat)
    (bufRef slot ptr v_fp v_lr v_21 v_pad v_20 v_19 : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  A.pool lim st' se ∗ decodeErrorAtStackLen A.repAlloc (se.readReg64 .x0) 0 ∗
    (bufRef ↦₆₄ slot) ∗ memRegion slot 16 ∗ (ptr ↦ₛ bs) ∗ memRegion (s0.sp - 96#64) 48 ∗
    ((s0.sp - 48#64) ↦₆₄ v_fp) ∗ ((s0.sp - 40#64) ↦₆₄ v_lr) ∗ ((s0.sp - 32#64) ↦₆₄ v_21) ∗
    ((s0.sp - 24#64) ↦₆₄ v_pad) ∗ ((s0.sp - 16#64) ↦₆₄ v_20) ∗ ((s0.sp - 8#64) ↦₆₄ v_19) ∗
    skipBelow3 s0.sp (d + 1)

private def SkipGroupErrCont {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (prog : Program) (s0 : State)
    (d tag : Nat) (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))
    (res : Option (List (BitVec 8))) (Q_f : State → SepProp → Prop) : Prop :=
  res = none →
    ∀ (se : State) (evs : List AllocEvent),
      SkipField3Env ⟨.startGroup, tag, d + 1, bufRef, slot, ptr, bs⟩ evs →
      ∀ v_fp v_lr v_21 v_pad v_20 v_19 : BitVec 64,
        se.pc = s0.readReg64 Reg.lr → se.status = .Running → se.sp = s0.sp → se.trace = s0.trace →
        se.readReg64 .x0 ≠ 0#64 → CalleeSavedPreserved s0 se →
        SepWP prog (s0.readReg64 Reg.lr) se
          (skipGroupErrPost3 A lim (M.stepEvents evs st) s0 se d
            bufRef slot ptr v_fp v_lr v_21 v_pad v_20 v_19 bs) Q_f

private def SkipGroupOkCont {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (prog : Program) (s0 : State)
    (d : Nat) (bufRef slot ptr v_pad : BitVec 64) (bs : List (BitVec 8))
    (res : Option (List (BitVec 8))) (Q_f : State → SepProp → Prop) : Prop :=
  ∀ (rest : List (BitVec 8)), res = some rest →
    ∀ (se : State),
      se.pc = s0.readReg64 Reg.lr → se.status = .Running → se.sp = s0.sp → se.trace = s0.trace →
      se.readReg64 .x0 = 0#64 → CalleeSavedPreserved s0 se →
      SepWP prog (s0.readReg64 Reg.lr) se
        (skipGroupLoopPre3 A lim (M.stepEvents ([] : List AllocEvent) st) s0 se d
          bufRef slot ptr v_pad bs rest) Q_f

set_option hygiene false in
local macro "wp_steps_rw_pool263 " mid:term:max stTerm:term:max : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_263).rebase (blkPl_263).base (hooksException H))
    blkLib_eq_263 (mid := $mid)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have _hp := (A.pool_transport lim $stTerm _ _
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))).symm
  wp_conv_pre => rw [_hp]
  clear _hp
  simp only [State.setMem_setMem]))

private theorem spAligned_sub96 {s0 sc : State} (halign : s0.spAligned)
    (hsp : sc.sp = s0.sp - 96#64) : sc.spAligned := by
  simpa only [State.spAligned, hsp, arm64_norm] using halign

private theorem sepWP_call_frame {α : Type} {prog : Program} {entry target_pc ret_pc : BitVec 64}
    {spec : Spec α} (hcall : subroutine_ok prog entry spec) {x : α}
    {s : State} {P T F : SepProp} {φ : Prop} {post : State → SepProp → Prop}
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hφ : φ) (hP : P = T ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hno : spec.onPanic x s = (fun _ => ⌜False⌝) := by rfl)
    (h_no_exit : spec.onExit x = (fun _ _ _ => ⌜False⌝) := by rfl)
    (hoom : spec.onOom x s = (fun _ => ⌜False⌝) := by rfl) :
    SepWP prog target_pc s P post := by
  refine SepWP.call_subroutine_frame hcall (x := x) (F := F) hpc hrun hsp_align hlr ?_ ?_ ?_ hnext ?_
  · intro R hm
    simp only [hspec, sepConj_assoc, satisfies_pure_sepConj]
    simp only [hP, sepConj_assoc] at hm
    exact ⟨hφ, hm⟩
  · intro R' sf _ hp; rw [hno] at hp; exact not_satisfies_false_sepConj hp
  · intro R' code sf _ he; rw [h_no_exit] at he; exact not_satisfies_false_sepConj he
  · intro R' sf _ ho; rw [hoom] at ho; exact False.elim (not_satisfies_false_sepConj ho)

private theorem skipField3_startGroup_err_at_call [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    {d tag : Nat} (hdepth : d + 1 < 2 ^ 32)
    {bufRef slot ptr v_pad kind : BitVec 64} {bs : List (BitVec 8)}
    {st : M.σ} {s0 sc : State} {res : Option (List (BitVec 8))} {Q_f : State → SepProp → Prop}
    (halign0 : s0.spAligned)
    (hfits_top : FitsEnv M lim st (SkipField3Env ⟨.startGroup, tag, d + 1, bufRef, slot, ptr, bs⟩))
    (herr_done : SkipGroupErrCont A lim st ((blkPC_263).rebase (blkPl_263).base H)
      s0 d tag bufRef slot ptr bs res Q_f)
    (hres_none : res = none)
    (hnone_top : skipField (2 * bs.length + 2) (d + 1) tag .startGroup bs = none)
    (hknh : KindNoHeap kind) (hpc : sc.pc = lsmpl.base 261) (hrun : sc.status = .Running)
    (hsp : sc.sp = s0.sp - 96#64) (htr : sc.trace = s0.trace)
    (hx0 : sc.readReg64 .x0 = s0.sp - 96#64)
    (hx30 : sc.readReg64 (Reg.gpr 30#5) = (blkPl_263).base + 204#64)
    (hcs : HighCalleeSaved3 s0 sc) :
    SepWP ((blkPC_263).rebase (blkPl_263).base H) (s0.readReg64 Reg.lr) sc
      (A.pool lim st sc ∗ (bufRef ↦₆₄ slot) ∗ memRegion slot 16 ∗ (ptr ↦ₛ bs) ∗
        ((s0.sp - 96#64) ↦₆₄ kind) ∗ memRegion (s0.sp - 88#64) 40 ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗ ((s0.sp - 24#64) ↦₆₄ v_pad) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗ skipBelow3 s0.sp (d + 1)) Q_f := by
  dsimp only [decodeErrorFromBudgetSpec] at hFromCall
  obtain ⟨hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  have hsp_align : sc.spAligned := spAligned_sub96 halign0 hsp
  have hfits_from : FitsEnv M lim st DecodeErrorFromEnv := fun evs hevs =>
    hfits_top evs (skipField3Env_of_decodeErrorFrom hnone_top hevs)
  conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth, ← hsp]
  refine sepWP_call_frame (x := (s0.sp - 96#64, kind, st))
    (ret_pc := (blkPl_263).base + 204#64) hFromCall rfl hpc hrun hsp_align hx30
    ⟨hx0, hknh, hfits_from⟩
    (by (conv => rhs; arg 1; dsimp only; rw [bv_sub_add_lit s0.sp 96 8]); sep_focus) ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf
  obtain ⟨_, _, _, hx22_sf, hx23_sf, hx24_sf, hx25_sf, hx26_sf, hx27_sf, hx28_sf, _, hvregs_sf⟩ := hcs_sf
  rw [hsp] at hsp_sf
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro evs
  wp_focus_pure; rintro ⟨hx0_ne, htr_sf⟩
  wp_focus_pure; intro hevs
  have htr_sf' : sf.trace = s0.trace := htr_sf.trans htr
  have hevs_top := skipField3Env_of_decodeErrorFrom (tag := tag) (d := d)
    (bufRef := bufRef) (slot := slot) (ptr := ptr) hnone_top hevs
  conv => arg 4; rw [hsp]
  apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
  wp_steps_rw_pool263 (s0.readReg64 (Reg.gpr 30#5)) (M.stepEvents evs st)
  refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [skipGroupErrPost3]; simp only [arm64_norm]; sep_ac_rfl))
    (herr_done hres_none _ evs hevs_top
      (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 21#5)) v_pad
      (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_sf])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, htr_sf'])
      (by simp only [arm64_norm]; exact hx0_ne)
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm, hx22_sf, hx22], by simp only [arm64_norm, hx23_sf, hx23],
        by simp only [arm64_norm, hx24_sf, hx24], by simp only [arm64_norm, hx25_sf, hx25],
        by simp only [arm64_norm, hx26_sf, hx26], by simp only [arm64_norm, hx27_sf, hx27],
        by simp only [arm64_norm, hx28_sf, hx28], by simp only [arm64_norm],
        by simp only [arm64_norm, hvregs_sf, hvregs]⟩)

private theorem skipField3_startGroup_varint_at_call [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hVarintCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (lsmpl.base 291) (decodeVarint2Spec A lim))
    {d tag : Nat} (hdepth : d + 1 < 2 ^ 32) {bufRef slot ptr v_pad : BitVec 64} {bs cur : List (BitVec 8)}
    (hlen_lt : bs.length < 2 ^ 63) (hcur_le : cur.length ≤ bs.length) (hcur_suf : IsDropSuffix bs cur)
    {st : M.σ} {s0 s : State} {res : Option (List (BitVec 8))}
    (hres : skipGroup (2 * bs.length + 1) (d + 1) tag bs = res)
    (hres_cur : skipGroup (2 * cur.length + 1) (d + 1) tag cur = res)
    {Q_f : State → SepProp → Prop} (halign0 : s0.spAligned)
    (hfits_top : FitsEnv M lim st (SkipField3Env ⟨.startGroup, tag, d + 1, bufRef, slot, ptr, bs⟩))
    (herr_done : SkipGroupErrCont A lim st ((blkPC_263).rebase (blkPl_263).base H) s0 d tag bufRef slot ptr bs res Q_f)
    (hpc_s : s.pc = (blkPl_263).base + 232#64) (hrun_s : s.status = .Running)
    (hsp_s : s.sp = s0.sp - 96#64) (htr_s : s.trace = s0.trace)
    (hx19_s : s.readReg64 (Reg.gpr 19#5) = bufRef) (hx20_s : s.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d)
    (hx21_s : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag) (hcs_s : HighCalleeSaved3 s0 s)
    (hsome_cont : ∀ (key : BitVec 64) (rest : List (BitVec 8)), decodeVarint cur = some (key, rest) →
      ∀ (sf : State), sf.pc = (blkPl_263).base + 240#64 → sf.status = .Running →
        sf.sp = s0.sp - 96#64 → sf.trace = s0.trace → sf.readReg64 .x0 = 0#64 → sf.readReg64 .x1 = key →
        sf.readReg64 (Reg.gpr 19#5) = bufRef → sf.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d →
        sf.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag → HighCalleeSaved3 s0 sf →
        SepWP ((blkPC_263).rebase (blkPl_263).base H) (s0.readReg64 Reg.lr) sf
          (skipGroupLoopPre3 A lim st s0 sf d bufRef slot ptr v_pad bs rest) Q_f) :
    SepWP ((blkPC_263).rebase (blkPl_263).base H) (s0.readReg64 Reg.lr) s
      (skipGroupLoopPre3 A lim st s0 s d bufRef slot ptr v_pad bs cur) Q_f := by
  dsimp only [decodeVarint2Spec, DecodeVarint2Budget.decodeVarint2SpecGen] at hVarintCall
  simp only [show 0x40 + (0x40 + decodeErrorHookStack) =
      CryptoVerification.SpqrV1.Varint.decodeVarint2Stack from rfl] at hVarintCall
  obtain ⟨hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s⟩ := hcs_s
  have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hlen_lt
  have hfits_dv : FitsEnv M lim st (DecodeVarint2Env cur) := by
    intro evs hevs; dsimp [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents] at hevs
    cases hd_c : decodeVarint cur with
    | some _ => rw [hd_c] at hevs; subst hevs; trivial
    | none =>
      rw [hd_c] at hevs
      have hnone_top : skipField (2 * bs.length + 2) (d + 1) tag .startGroup bs = none := by
        rw [skipField_succ_startGroup, hres, ← hres_cur, skipGroup_of_decodeVarint_none (d := d) (tag := tag) hd_c]
      exact hfits_top evs ((skipField3Env_of_none hnone_top).mpr hevs)
  let curPtr : BitVec 64 := ptr + BitVec.ofNat 64 (bs.length - cur.length)
  conv => arg 4; rw [skipGroupLoopPre3, sliceCursorAfter_eq_split hcur_le hcur_suf,
    skipBelow3_leaf s0.sp (d + 1) hdepth]
  wp_steps_rw_pool263 (lsmpl.base 291) st
  have hsp_align_s : s.spAligned := spAligned_sub96 halign0 hsp_s
  refine sepWP_call_frame (x := (⟨bufRef, slot, curPtr, cur⟩, st))
    (ret_pc := (blkPl_263).base + 240#64) hVarintCall rfl
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align_s)
    (by simp only [arm64_norm]) ⟨by simp only [arm64_norm], hcur_lt, hfits_dv⟩
    (by (conv => rhs; arg 1; dsimp only; simp only [arm64_norm, hsp_s]); sep_focus) ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf
  obtain ⟨hx19_sf, hx20_sf, hx21_sf, hx22_sf, hx23_sf, hx24_sf, hx25_sf, hx26_sf, hx27_sf, hx28_sf, _, hvregs_sf⟩ := hcs_sf
  simp only [arm64_norm, hsp_s, hx19_s, hx20_s, hx21_s, hx22_s, hx23_s, hx24_s, hx25_s, hx26_s, hx27_s, hx28_s, hvregs_s] at hsp_sf hx19_sf hx20_sf hx21_sf hx22_sf hx23_sf hx24_sf hx25_sf hx26_sf hx27_sf hx28_sf hvregs_sf
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro evs
  wp_focus_pure; intro htr_sf; simp only [arm64_norm] at htr_sf
  have htr_sf' : sf.trace = s0.trace := htr_sf.trans htr_s
  wp_focus_pure; intro hevs
  conv => arg 4; simp only [arm64_norm, hsp_s]
  cases hd : decodeVarint cur with
  | none =>
    have hres_none : res = none := by rw [← hres_cur, skipGroup_of_decodeVarint_none (d := d) (tag := tag) hd]
    have hnone_top : skipField (2 * bs.length + 2) (d + 1) tag .startGroup bs = none := by
      rw [skipField_succ_startGroup, hres, hres_none]
    have hevs_top := skipField3Env_of_decodeErrorFrom (tag := tag) (d := d)
      (bufRef := bufRef) (slot := slot) (ptr := ptr) hnone_top (decodeErrorFromEnv_of_dv_none hd hevs)
    conv => arg 4; simp only [hd, sepConj_assoc]
    wp_focus_pure; intro hx0_one
    wp_focus_pure; intro hx1_ne
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by dsimp only [curPtr]; sep_focus)
    wp_steps_rw_pool263 (s0.readReg64 (Reg.gpr 30#5)) (M.stepEvents evs st)
    refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [skipGroupErrPost3]; simp only [arm64_norm]; sep_ac_rfl))
      (herr_done hres_none _ evs hevs_top
        (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
        (s0.readReg64 (Reg.gpr 21#5)) v_pad (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_sf])
        (by simp only [arm64_norm]) (by simp only [arm64_norm, htr_sf'])
        (by simp only [arm64_norm]; exact hx1_ne)
        ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm, hx22_sf], by simp only [arm64_norm, hx23_sf],
          by simp only [arm64_norm, hx24_sf], by simp only [arm64_norm, hx25_sf],
          by simp only [arm64_norm, hx26_sf], by simp only [arm64_norm, hx27_sf],
          by simp only [arm64_norm, hx28_sf], by simp only [arm64_norm],
          by simp only [arm64_norm, hvregs_sf]⟩)
  | some p =>
    rcases p with ⟨key, rest⟩
    have hevs_nil := decodeVarint2Env_eq_nil hd hevs
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
    conv => arg 4; simp only [hd, hevs_nil, LibsignalBinary.Heap.AllocCostModel.stepEvents, List.foldl, sepConj_assoc]
    wp_focus_pure; rintro ⟨hx0_sf, hx1_sf⟩
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by dsimp only [curPtr]; sep_focus)
    refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [skipGroupLoopPre3]; sep_ac_rfl))
      (hsome_cont key rest hd sf hpc_sf hrun_sf hsp_sf htr_sf' hx0_sf hx1_sf hx19_sf hx20_sf hx21_sf
        ⟨hx22_sf, hx23_sf, hx24_sf, hx25_sf, hx26_sf, hx27_sf, hx28_sf, hvregs_sf⟩)

private theorem skipField3_startGroup_rec_at_call [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : Nat) (hdepth : d + 1 < 2 ^ 32)
    (hrec : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base (skipField3SpecAt A lim d (fun _ => True)))
    {iwt : WireType} {itag tag : Nat} (hitag_lt : itag < 2 ^ 32)
    {bufRef slot ptr v_pad : BitVec 64} {bs rest : List (BitVec 8)}
    (hrest_lt : rest.length < 2 ^ 63) (hrest_le : rest.length ≤ bs.length)
    (hrest_suf : IsDropSuffix bs rest) {st : M.σ} {s0 sc : State} {res : Option (List (BitVec 8))}
    (hres : skipGroup (2 * bs.length + 1) (d + 1) tag bs = res)
    (hres_rec : (match skipField (2 * rest.length + 2) d itag iwt rest with
      | none => none | some rest' => skipGroup (2 * rest'.length + 1) (d + 1) tag rest') = res)
    {Q_f : State → SepProp → Prop} (halign0 : s0.spAligned)
    (hfits_top : FitsEnv M lim st (SkipField3Env ⟨.startGroup, tag, d + 1, bufRef, slot, ptr, bs⟩))
    (herr_done : SkipGroupErrCont A lim st ((blkPC_263).rebase (blkPl_263).base H) s0 d tag bufRef slot ptr bs res Q_f)
    (hpc : sc.pc = (blkPl_263).base) (hrun : sc.status = .Running)
    (hsp : sc.sp = s0.sp - 96#64) (htr : sc.trace = s0.trace)
    (hx0 : (sc.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx1 : (sc.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 itag)
    (hx2 : sc.readReg64 .x2 = bufRef) (hx3 : (sc.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 d)
    (hx30 : sc.readReg64 (Reg.gpr 30#5) = (blkPl_263).base + 304#64)
    (hx19 : sc.readReg64 (Reg.gpr 19#5) = bufRef) (hx20 : sc.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d)
    (hx21 : sc.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag) (hcs : HighCalleeSaved3 s0 sc)
    (hsome_cont : ∀ (rest' : List (BitVec 8)), skipField (2 * rest.length + 2) d itag iwt rest = some rest' →
      ∀ (sn : State), sn.pc = (blkPl_263).base + 232#64 → sn.status = .Running →
        sn.sp = s0.sp - 96#64 → sn.trace = s0.trace →
        sn.readReg64 (Reg.gpr 19#5) = bufRef → sn.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d →
        sn.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag → HighCalleeSaved3 s0 sn →
        SepWP ((blkPC_263).rebase (blkPl_263).base H) (s0.readReg64 Reg.lr) sn
          (skipGroupLoopPre3 A lim st s0 sn d bufRef slot ptr v_pad bs rest') Q_f) :
    SepWP ((blkPC_263).rebase (blkPl_263).base H) (s0.readReg64 Reg.lr) sc
      (skipGroupLoopPre3 A lim st s0 sc d bufRef slot ptr v_pad bs rest) Q_f := by
  dsimp only [skipField3SpecAt] at hrec; dsimp only [skipGroupLoopPre3]
  obtain ⟨hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  have hd_lt : d < 2 ^ 32 := Nat.lt_of_succ_lt hdepth
  have hsp_align : sc.spAligned := spAligned_sub96 halign0 hsp
  let rptr : BitVec 64 := ptr + BitVec.ofNat 64 (bs.length - rest.length)
  let recGhost : SkipFieldGhost := ⟨iwt, itag, d, bufRef, slot, rptr, rest⟩
  have hfits_rec : FitsEnv M lim st (SkipField3Env recGhost) := by
    intro evs hevs; dsimp [SkipField3Env, SkipFieldEnv, skipFieldEventsCore, recGhost] at hevs
    cases hs_c : skipField (2 * rest.length + 2) d itag iwt rest with
    | some _ => rw [hs_c] at hevs; subst hevs; trivial
    | none =>
      rw [hs_c] at hevs
      have hnone_top : skipField (2 * bs.length + 2) (d + 1) tag .startGroup bs = none := by
        rw [skipField_succ_startGroup, hres, ← hres_rec, hs_c]
      exact hfits_top evs (skipField3Env_of_decodeErrorFrom hnone_top hevs)
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
    show skipBelow3 s0.sp (d + 1) = stackAt sc.sp (skipField3Stack d) by rw [hsp]]
  refine sepWP_call_frame (x := (recGhost, st))
    (ret_pc := (blkPl_263).base + 304#64) hrec rfl hpc hrun hsp_align hx30
    ⟨trivial, rfl, hx0, hx1, hitag_lt, hx2, hx3, hd_lt, hrest_lt, hfits_rec⟩
    (by (conv => rhs; arg 1; dsimp only [recGhost, rptr]); sep_focus) ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf
  obtain ⟨hx19_sf, hx20_sf, hx21_sf, hx22_sf, hx23_sf, hx24_sf, hx25_sf, hx26_sf, hx27_sf, hx28_sf, _, hvregs_sf⟩ := hcs_sf
  rw [hsp] at hsp_sf; rw [hx19] at hx19_sf; rw [hx20] at hx20_sf; rw [hx21] at hx21_sf
  rw [hx22] at hx22_sf; rw [hx23] at hx23_sf; rw [hx24] at hx24_sf; rw [hx25] at hx25_sf
  rw [hx26] at hx26_sf; rw [hx27] at hx27_sf; rw [hx28] at hx28_sf; rw [hvregs] at hvregs_sf
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro evs
  wp_focus_pure; intro htr_sf
  have htr_sf' : sf.trace = s0.trace := htr_sf.trans htr
  wp_focus_pure; intro hevs
  conv => arg 4; rw [show stackAt sc.sp (skipField3Stack d) = skipBelow3 s0.sp (d + 1) by rw [hsp]]
  dsimp only [recGhost] at *
  cases hs : skipField (2 * rest.length + 2) d itag iwt rest with
  | none =>
    have hres_none : res = none := by rw [← hres_rec, hs]
    have hnone_top : skipField (2 * bs.length + 2) (d + 1) tag .startGroup bs = none := by
      rw [skipField_succ_startGroup, hres, hres_none]
    have hevs_top := skipField3Env_of_rec_none (tag := tag) (ptr := ptr) hs hnone_top hevs
    conv => arg 4; simp only [hs, sepConj_assoc]
    wp_focus_pure; intro hx0_ne
    have hcbz_sf : (sf.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by dsimp only [rptr]; sep_focus)
    wp_steps_rw_pool263 (s0.readReg64 (Reg.gpr 30#5)) (M.stepEvents evs st)
    refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [skipGroupErrPost3]; simp only [arm64_norm]; sep_ac_rfl))
      (herr_done hres_none _ evs hevs_top
        (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
        (s0.readReg64 (Reg.gpr 21#5)) v_pad (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_sf])
        (by simp only [arm64_norm]) (by simp only [arm64_norm, htr_sf'])
        (by simp only [arm64_norm]; exact hx0_ne)
        ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm, hx22_sf], by simp only [arm64_norm, hx23_sf],
          by simp only [arm64_norm, hx24_sf], by simp only [arm64_norm, hx25_sf],
          by simp only [arm64_norm, hx26_sf], by simp only [arm64_norm, hx27_sf],
          by simp only [arm64_norm, hx28_sf], by simp only [arm64_norm],
          by simp only [arm64_norm, hvregs_sf]⟩)
  | some rest' =>
    have hevs_nil := (skipField3Env_of_some (x := ⟨iwt, itag, d, bufRef, slot, rptr, rest⟩) hs).mp hevs
    have hrest'_le_rest : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hs
    conv => arg 4; simp only [hs, hevs_nil, LibsignalBinary.Heap.AllocCostModel.stepEvents, List.foldl, sepConj_assoc]
    wp_focus_pure; intro hx0_sf
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le_rest) (by dsimp only [rptr]; sep_focus)
    wp_steps_rw_pool263 ((blkPl_263).base + 232#64) st
    refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [skipGroupLoopPre3]; sep_ac_rfl))
      (hsome_cont rest' hs _
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_sf])
        (by simp only [arm64_norm, hsp_sf]) (by simp only [arm64_norm, htr_sf'])
        (by simp only [arm64_norm, hx19_sf]) (by simp only [arm64_norm, hx20_sf])
        (by simp only [arm64_norm, hx21_sf])
        ⟨by simp only [arm64_norm, hx22_sf], by simp only [arm64_norm, hx23_sf],
          by simp only [arm64_norm, hx24_sf], by simp only [arm64_norm, hx25_sf],
          by simp only [arm64_norm, hx26_sf], by simp only [arm64_norm, hx27_sf],
          by simp only [arm64_norm, hx28_sf], by simp only [arm64_norm, hvregs_sf]⟩)

theorem skipField3_startGroup_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    (hVarintCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (lsmpl.base 291) (decodeVarint2Spec A lim))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32)
    (hrec : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base (skipField3SpecAt A lim d (fun _ => True))) :
    subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base
      (skipField3SpecAt A lim (d + 1) (fun x => x.wt = .startGroup)) := by
  unfold skipField3SpecAt
  simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth, sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init g s0
  rcases g with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *; subst ‹wt = .startGroup›; subst ‹depth = d + 1›
  have hlen_lt : bs.length < 2 ^ 63 := ‹bs.length < 2 ^ 63›
  have htag_lt : tag < 2 ^ 32 := ‹tag < 2 ^ 32›
  have hfits_top : FitsEnv M lim st (SkipField3Env ⟨.startGroup, tag, d + 1, bufRef, slot, ptr, bs⟩) := by assumption
  have hcbz := cbz_depth_succ ‹(s0.readReg64 (Reg.gpr 3#5)).setWidth 32 = BitVec.ofNat 32 (d + 1)› hdepth
  have hw0 := w0_and_255_eq ‹(s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = _›
  dsimp [CryptoVerification.LibsignalProtoCodec.WireType.toNat] at hw0
  obtain ⟨htag_zext1, htag_zext2⟩ := bv32_zeroExtend_ofNat htag_lt
  obtain ⟨hd_zext1, hd_zext2⟩ := bv32_zeroExtend_ofNat (Nat.lt_of_succ_lt hdepth)
  obtain ⟨hd_sub1, hd_sub2⟩ := bv32_sub_one_zeroExtend hdepth
  rw [skipField_succ_startGroup]
  generalize hres : skipGroup (2 * bs.length + 1) (d + 1) tag bs = res
  wp_steps_rw_pool263 ((blkPl_263).base + 232#64) st
  have hloop : ∀ (Q_f : State → SepProp → Prop),
      SkipGroupErrCont A lim st ((blkPC_263).rebase (blkPl_263).base H) s0 d tag bufRef slot ptr bs res Q_f →
      SkipGroupOkCont A lim st ((blkPC_263).rebase (blkPl_263).base H) s0 d bufRef slot ptr v_stk_2 bs res Q_f →
      ∀ n (cur : List (BitVec 8)) (s : State),
        cur.length ≤ n → cur.length ≤ bs.length → IsDropSuffix bs cur →
        skipGroup (2 * cur.length + 1) (d + 1) tag cur = res →
        s.pc = (blkPl_263).base + 232#64 → s.status = .Running → s.sp = s0.sp - 96#64 → s.trace = s0.trace →
        s.readReg64 (Reg.gpr 19#5) = bufRef → s.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 d →
        s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tag → HighCalleeSaved3 s0 s →
        SepWP ((blkPC_263).rebase (blkPl_263).base H) (s0.readReg64 Reg.lr) s
          (skipGroupLoopPre3 A lim st s0 s d bufRef slot ptr v_stk_2 bs cur) Q_f := by
    intro Q_f herr_done hok_done n
    induction n with
    | zero =>
      intro cur s hcur_n hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s
      refine skipField3_startGroup_varint_at_call hVarintCall hdepth hlen_lt hcur_le hcur_suf
        hres hres_cur hsp_align hfits_top herr_done hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s ?_
      intro key rest hd
      exact False.elim (Nat.not_lt_zero rest.length (Nat.lt_of_lt_of_le (decodeVarint_length hd) hcur_n))
    | succ n ih =>
      intro cur s hcur_n hcur_le hcur_suf hres_cur hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s
      refine skipField3_startGroup_varint_at_call hVarintCall hdepth hlen_lt hcur_le hcur_suf
        hres hres_cur hsp_align hfits_top herr_done hpc_s hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hcs_s ?_
      intro key rest hd sf hpc_sf hrun_sf hsp_sf htr_sf hx0_sf hx1_sf hx19_sf hx20_sf hx21_sf hcs_sf
      dsimp only [skipGroupLoopPre3]
      obtain ⟨hx22_sf, hx23_sf, hx24_sf, hx25_sf, hx26_sf, hx27_sf, hx28_sf, hvregs_sf⟩ := hcs_sf
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hlen_lt
      have hrest_suf : IsDropSuffix bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      by_cases hk_ge : 2 ^ 32 ≤ key.toNat
      · have hres_none : res = none := by rw [← hres_cur, skipGroup_of_key_ge (d := d) (tag := tag) hd hk_ge]
        have hnone_top : skipField (2 * bs.length + 2) (d + 1) tag .startGroup bs = none := by
          rw [skipField_succ_startGroup, hres, hres_none]
        have hshr := key_shr32_of_ge hk_ge
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1
        wp_steps_rw_pool263 (lsmpl.base 261) st
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (pointsTo64_memRegion32_entails_40 s0.sp key) (by sep_focus)
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (skipField3_startGroup_err_at_call hFromCall hdepth hsp_align hfits_top herr_done
            hres_none hnone_top (kind := 0x8000000000000004#64) (by decide)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_sf])
            (by simp only [arm64_norm, hsp_sf]) (by simp only [arm64_norm, htr_sf])
            (by simp only [arm64_norm]) (by simp only [arm64_norm])
            ⟨by simp only [arm64_norm, hx22_sf], by simp only [arm64_norm, hx23_sf],
              by simp only [arm64_norm, hx24_sf], by simp only [arm64_norm, hx25_sf],
              by simp only [arm64_norm, hx26_sf], by simp only [arm64_norm, hx27_sf],
              by simp only [arm64_norm, hx28_sf], by simp only [arm64_norm, hvregs_sf]⟩)
      · have hshr := key_shr32_of_lt hk_ge
        cases hwt : CryptoVerification.LibsignalProtoCodec.WireType.ofNat? (key.toNat % 8) with
        | none =>
          have hres_none : res = none := by rw [← hres_cur, skipGroup_of_wt_none (d := d) (tag := tag) hd hk_ge hwt]
          have hnone_top : skipField (2 * bs.length + 2) (d + 1) tag .startGroup bs = none := by
            rw [skipField_succ_startGroup, hres, hres_none]
          obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1
          wp_steps_rw_pool263 (lsmpl.base 261) st
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          apply SepWP.fold (pointsTo64_memRegion32_entails_40 s0.sp (key &&& 7#64)) (by sep_focus)
          refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (skipField3_startGroup_err_at_call hFromCall hdepth hsp_align hfits_top herr_done
              hres_none hnone_top (kind := 0x8000000000000003#64) (by decide)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_sf])
              (by simp only [arm64_norm, hsp_sf]) (by simp only [arm64_norm, htr_sf])
              (by simp only [arm64_norm]) (by simp only [arm64_norm])
              ⟨by simp only [arm64_norm, hx22_sf], by simp only [arm64_norm, hx23_sf],
                by simp only [arm64_norm, hx24_sf], by simp only [arm64_norm, hx25_sf],
                by simp only [arm64_norm, hx26_sf], by simp only [arm64_norm, hx27_sf],
                by simp only [arm64_norm, hx28_sf], by simp only [arm64_norm, hvregs_sf]⟩)
        | some iwt =>
          obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
          obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
          have hitag_lt : key.toNat / 8 < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_of_not_le hk_ge)
          obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat hitag_lt
          by_cases hitag0 : key.toNat / 8 < 1
          · have hres_none : res = none := by rw [← hres_cur, skipGroup_of_tag_zero (d := d) (tag := tag) hd hk_ge hwt hitag0]
            have hnone_top : skipField (2 * bs.length + 2) (d + 1) tag .startGroup bs = none := by
              rw [skipField_succ_startGroup, hres, hres_none]
            have htag_zero : key.toNat / 8 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hitag0)
            conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
              sliceCursorAt, memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            apply SepWP.exists_elim; intro v_err0
            wp_steps_rw_pool263 (lsmpl.base 261) st
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
            apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
            refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
              (skipField3_startGroup_err_at_call hFromCall hdepth hsp_align hfits_top herr_done
                hres_none hnone_top (kind := 0x8000000000000005#64) (by decide)
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_sf])
                (by simp only [arm64_norm, hsp_sf]) (by simp only [arm64_norm, htr_sf])
                (by simp only [arm64_norm]) (by simp only [arm64_norm])
                ⟨by simp only [arm64_norm, hx22_sf], by simp only [arm64_norm, hx23_sf],
                  by simp only [arm64_norm, hx24_sf], by simp only [arm64_norm, hx25_sf],
                  by simp only [arm64_norm, hx26_sf], by simp only [arm64_norm, hx27_sf],
                  by simp only [arm64_norm, hx28_sf], by simp only [arm64_norm, hvregs_sf]⟩)
          · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
            by_cases hiwt_eg : iwt = .endGroup
            · subst hiwt_eg; dsimp [CryptoVerification.LibsignalProtoCodec.WireType.toNat] at hand_wt hcc1_wt hcc2_wt
              rw [skipGroup_of_endGroup (d := d) (tag := tag) hd hk_ge hwt hitag0] at hres_cur
              by_cases hitag_eq : key.toNat / 8 = tag
              · simp only [hitag_eq, ↓reduceIte] at hres_cur
                have hres_some : res = some rest := hres_cur.symm
                rw [hitag_eq] at hw1 hw1_2 hw1_zext1 hw1_zext2 hcbz_tag1 hcbz_tag2
                simp only [sliceCursorAfter]
                wp_steps_rw_pool263 (s0.readReg64 (Reg.gpr 30#5)) st
                refine SepWP.weaken_pre (Entails.of_eq rfl)
                  (hok_done rest hres_some _
                    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_sf])
                    (by simp only [arm64_norm]) (by simp only [arm64_norm, htr_sf])
                    (by simp only [arm64_norm])
                    ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
                      by simp only [arm64_norm, hx22_sf], by simp only [arm64_norm, hx23_sf],
                      by simp only [arm64_norm, hx24_sf], by simp only [arm64_norm, hx25_sf],
                      by simp only [arm64_norm, hx26_sf], by simp only [arm64_norm, hx27_sf],
                      by simp only [arm64_norm, hx28_sf], by simp only [arm64_norm],
                      by simp only [arm64_norm, hvregs_sf]⟩)
              · simp only [hitag_eq, ↓reduceIte] at hres_cur
                have hres_none : res = none := hres_cur.symm
                have hnone_top : skipField (2 * bs.length + 2) (d + 1) tag .startGroup bs = none := by
                  rw [skipField_succ_startGroup, hres, hres_none]
                obtain ⟨hne_bv1, hne_bv2⟩ := itag_beq_tag_false hitag_eq hitag_lt htag_lt
                conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
                  sliceCursorAt, memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
                simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
                apply SepWP.exists_elim; intro v_err0
                wp_steps_rw_pool263 (lsmpl.base 261) st
                apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
                apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
                refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                  (skipField3_startGroup_err_at_call hFromCall hdepth hsp_align hfits_top herr_done
                    hres_none hnone_top (kind := 0x8000000000000009#64) (by decide)
                    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_sf])
                    (by simp only [arm64_norm, hsp_sf]) (by simp only [arm64_norm, htr_sf])
                    (by simp only [arm64_norm]) (by simp only [arm64_norm])
                    ⟨by simp only [arm64_norm, hx22_sf], by simp only [arm64_norm, hx23_sf],
                      by simp only [arm64_norm, hx24_sf], by simp only [arm64_norm, hx25_sf],
                      by simp only [arm64_norm, hx26_sf], by simp only [arm64_norm, hx27_sf],
                      by simp only [arm64_norm, hx28_sf], by simp only [arm64_norm, hvregs_sf]⟩)
            · rw [skipGroup_of_ne_endGroup (d := d) (tag := tag) hd hk_ge hwt hitag0 hiwt_eg] at hres_cur
              have hiwt_ne4 := iwt_beq_4_false hiwt_eg
              conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf]
              wp_steps_rw_pool263 (blkPl_263).base st
              apply SepWP.fold (sliceCursorAfter_eq_split hrest_le hrest_suf |>.symm |> Entails.of_eq) (by sep_focus)
              refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [skipGroupLoopPre3]; sep_ac_rfl))
                (skipField3_startGroup_rec_at_call d hdepth hrec hitag_lt hrest_lt hrest_le hrest_suf
                  hres hres_cur hsp_align hfits_top herr_done
                  (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_sf])
                  (by simp only [arm64_norm, hsp_sf]) (by simp only [arm64_norm, htr_sf])
                  (by simp only [arm64_norm]; cases iwt <;> rfl) (by simp only [arm64_norm])
                  (by simp only [arm64_norm]) (by simp only [arm64_norm])
                  (by simp only [arm64_norm]) (by simp only [arm64_norm, hx19_sf])
                  (by simp only [arm64_norm, hx20_sf]) (by simp only [arm64_norm, hx21_sf])
                  ⟨by simp only [arm64_norm, hx22_sf], by simp only [arm64_norm, hx23_sf],
                    by simp only [arm64_norm, hx24_sf], by simp only [arm64_norm, hx25_sf],
                    by simp only [arm64_norm, hx26_sf], by simp only [arm64_norm, hx27_sf],
                    by simp only [arm64_norm, hx28_sf], by simp only [arm64_norm, hvregs_sf]⟩ ?_)
              intro rest' hs sn hpc_sn hrun_sn hsp_sn htr_sn hx19_sn hx20_sn hx21_sn hcs_sn
              rw [hs] at hres_cur; dsimp only at hres_cur
              have hrest'_le_rest : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hs
              have hrest'_le_n : rest'.length ≤ n :=
                Nat.le_of_lt_succ (Nat.lt_of_le_of_lt hrest'_le_rest (Nat.lt_of_lt_of_le hrest_lt_cur hcur_n))
              exact ih rest' sn hrest'_le_n (Nat.le_trans hrest'_le_rest hrest_le)
                (suffix_trans hrest_le hrest_suf hrest'_le_rest ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hs))
                hres_cur hpc_sn hrun_sn hsp_sn htr_sn hx19_sn hx20_sn hx21_sn hcs_sn
  refine SepWP.weaken_pre
    (Entails.of_eq (by dsimp only [skipGroupLoopPre3]; simp only [sliceCursorAfter, Nat.sub_self, BitVec.add_zero]; sep_ac_rfl))
    (hloop _ ?_ ?_ bs.length bs _ (Nat.le_refl _) (Nat.le_refl _) (by simp [IsDropSuffix]) hres
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  · intro hres_none se evs hevs_top v_fp v_lr v_21 v_pad v_20 v_19 hpc_se hrun_se hsp_se htr_se hx0_se hcs_se
    subst hres_none
    obtain ⟨hx19_se, hx20_se, hx21_se, hx22_se, hx23_se, hx24_se, hx25_se, hx26_se, hx27_se, hx28_se, hfp_se, hvregs_se⟩ := hcs_se
    dsimp only [skipGroupErrPost3]
    wp_done
  · intro rest hres_some se hpc_se hrun_se hsp_se htr_se hx0_se hcs_se
    subst hres_some
    have hsome_top : skipField (2 * bs.length + 2) (d + 1) tag .startGroup bs = some rest := by
      rw [skipField_succ_startGroup, hres]
    have hevs_top : SkipField3Env ⟨.startGroup, tag, d + 1, bufRef, slot, ptr, bs⟩ [] :=
      (skipField3Env_of_some hsome_top).mpr rfl
    obtain ⟨hx19_se, hx20_se, hx21_se, hx22_se, hx23_se, hx24_se, hx25_se, hx26_se, hx27_se, hx28_se, hfp_se, hvregs_se⟩ := hcs_se
    dsimp only [skipGroupLoopPre3]
    wp_done

/-! ## Induction on Recursion Depth -/

theorem skipField3_at_depth_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    (hVarintCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 291) (decodeVarint2Spec A lim))
    (depth : Nat) (hdepth : depth < 2 ^ 32) :
    subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (blkPl_263).base
      (skipField3SpecAt A lim depth (fun _ => True)) := by
  induction depth with
  | zero => exact skipField3_depth_zero_placed_ok hFromCall
  | succ d ih =>
    have hrec := ih (by omega)
    have hAll :=
      subroutine_ok_skipField3_or (skipField3_varint_placed_ok hVarintCall d hdepth)
        (subroutine_ok_skipField3_or (skipField3_sixtyFourBit_placed_ok hFromCall d hdepth)
          (subroutine_ok_skipField3_or (skipField3_lengthDelimited_placed_ok hFromCall hVarintCall d hdepth)
            (subroutine_ok_skipField3_or (skipField3_startGroup_placed_ok hFromCall hVarintCall d hdepth hrec)
              (subroutine_ok_skipField3_or (skipField3_endGroup_placed_ok hFromCall d hdepth)
                (skipField3_thirtyTwoBit_placed_ok hFromCall d hdepth)))))
    refine subroutine_ok_skipField3_imp (fun x _ => ?_) hAll
    cases x.wt <;> simp

theorem subroutine_ok_skipField3Spec_of_at_depth {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (h : ∀ depth, depth < 2 ^ 32 →
      subroutine_ok prog entry (skipField3SpecAt A lim depth (fun _ => True))) :
    subroutine_ok prog entry (skipField3Spec A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' := hpre
  simp only [skipField3Spec, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  have hdepth : x.depth < 2 ^ 32 := hpre'.1.2.2.2.2.2.1
  refine (h x.depth hdepth).mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
  simp only [skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨trivial, trivial, hpre'.1⟩, hpre'.2⟩

theorem skipField3_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    (hVarintCall : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 291) (decodeVarint2Spec A lim)) :
    subroutine_ok ((blkPC_263).rebase (blkPl_263).base H)
      (blkPl_263).base (skipField3Spec A lim) :=
  subroutine_ok_skipField3Spec_of_at_depth
    (skipField3_at_depth_placed_ok hFromCall hVarintCall)

end LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
