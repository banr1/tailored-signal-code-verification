/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `prost::encoding::bytes::merge::<Vec<u8>>` Helpers and Epilogues

`RustCliAllocBudget` and `VmPreserved` callee specifications, exact-capacity postcondition
predicates (`bmNextCap`, `bytesMergeExactRawSpecGen`), and `[LibsignalPlacement]` epilogue
lemmas for `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved rustAllocEvents)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv decodeErrorFromBudgetSpecWithStack withVmPreserved)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded lsmpl
   blkPC_7 blkPl_7 withLsCl)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalProtoCodec (mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap bytesBoxU8Buf bytesData bytesPlacedDropFnAddr bytesPlacedVtable bytesPtr
   decodeErrorAtStackLen decodeErrorHookStack framelessMemcpySpec reserveCap withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost SepWP.drop_left SepWP.with_vtableSlot_placed
   SepWPp.bm_call_frame_lscl
   SepWPp.bm_of_sepWP_lscl bmCapCond bmSliceStack bmTotalStack bm_HighCalleeSaved
   bytesBoxU8Buf_nonempty decodeErrorHookStackX fold_bytesBoxU8Buf_nonempty
   fold_stackAt_bytesMergeGen fold_vecU8At_copied savedRegsStack sliceCursorAfter sliceCursorAt
   spAligned_sub_224 stackAt_sliceGen_split subroutine_ok_withLsCl_of_plain
   vecU8At_entails_bmPostVec vecU8At_nil_eq)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.DefsBudget (bytesDropEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (decodeVarintSlowBudgetSpecWithStack sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (subroutine_ok_withStack_of_subroutine_ok withStack)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (decodeVarintSliceSpecGen)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv bmPreBoundBudget bytesMergeEventsCore bytesMergeRawSpec bytesMergeRawSpecGen
   bytesMergeRawSpecX)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Parameterized specifications and post/panic predicates -/

theorem bytesMergeRawSpecGen_base_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    bytesMergeRawSpecGen A lim decodeErrorHookStack true = bytesMergeRawSpec A lim := rfl

theorem bytesMergeRawSpecGen_x_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    bytesMergeRawSpecGen A lim decodeErrorHookStackX true = bytesMergeRawSpecX A lim := rfl

abbrev MergePostGen {M : AllocCostModel} (errStack : Nat) (reqCap : Bool)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BytesMergeGhost) (st : M.σ) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  ((sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (bytesMergeRawSpecGen A lim errStack reqCap).post (x, st) s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev MergePanicGen {M : AllocCostModel} (errStack : Nat) (reqCap : Bool)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BytesMergeGhost) (st : M.σ) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (bytesMergeRawSpecGen A lim errStack reqCap).onPanic (x, st) s0 sf ∗ R)

/-- Deterministic `Vec<u8>` post-capacity after `prost::encoding::bytes::merge::<Vec<u8>, _>`
succeeds with slice `v` (`v.length ≤ cap` overwrites in place; `cap < v.length` reserves
`reserveCap cap 0 v.length`). -/
def bmNextCap (cap vLen : Nat) : Nat :=
  if vLen ≤ cap then cap else reserveCap cap 0 vLen

/-- Exact-capacity postcondition predicate for `bytesMergeExactRawSpecGen` (`reqCap = true`
records both `BytesMergeCapOk cap' restLen` and `cap'.toNat = bmNextCap valCap.toNat vLen`). -/
abbrev bmExactCapCond (reqCap : Bool) (valCap cap' : BitVec 64)
    (vLen restLen : Nat) : Prop :=
  match reqCap with
  | true => BytesMergeCapOk cap' restLen ∧ cap'.toNat = bmNextCap valCap.toNat vLen
  | false => cap'.toNat = bmNextCap valCap.toNat vLen

/-- Exact-capacity output `Vec<u8>` spatial postcondition of `bytesMergeExactRawSpecGen`. -/
def bmExactPostVecGen (reqCap : Bool) (A : RustAlloc) (valPtr valCap : BitVec 64)
    (v rest : List (BitVec 8)) : SepProp :=
  ∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
    ⌜bmExactCapCond reqCap valCap cap' v.length rest.length⌝ ∗
      vecU8At A valPtr cap' ptr' v

theorem vecU8At_entails_bmExactPostVecGen (reqCap : Bool) (A : RustAlloc)
    (valPtr valCap cap' ptr' : BitVec 64) (v rest : List (BitVec 8))
    (hcapOk : bmCapCond reqCap cap' rest.length)
    (hcapEq : cap'.toNat = bmNextCap valCap.toNat v.length) :
    vecU8At A valPtr cap' ptr' v ⊢ bmExactPostVecGen reqCap A valPtr valCap v rest := by
  unfold bmExactPostVecGen
  refine Entails.sepExists_right cap'
    (Entails.sepExists_right ptr' (Entails.pure_right ?_ (Entails.refl _)))
  cases reqCap
  · exact hcapEq
  · exact ⟨hcapOk, hcapEq⟩

theorem bmExactPostVecGen_entails_bmPostVec (reqCap : Bool) (A : RustAlloc)
    (valPtr valCap : BitVec 64) (v rest : List (BitVec 8)) :
    bmExactPostVecGen reqCap A valPtr valCap v rest ⊢
      LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bmPostVec reqCap A valPtr v rest := by
  unfold bmExactPostVecGen
  refine Entails.sepExists_elim fun cap' => Entails.sepExists_elim fun ptr' =>
    Entails.pure_left fun h => ?_
  cases reqCap
  · exact Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))
  · exact Entails.sepExists_right cap'
      (Entails.sepExists_right ptr' (Entails.pure_right h.1 (Entails.refl _)))

/-- Parameterized budget-threaded raw contract of `bytes::merge` strengthening `bmPostVec` with
the deterministic capacity equation `cap'.toNat = bmNextCap x.valCap.toNat v.length`. -/
def bytesMergeExactRawSpecGen {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (errStack : Nat) (reqCap : Bool) :
    Spec (BytesMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜bmPreBoundBudget reqCap lim st s x⌝ ∗
      vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp (0xe0 + (0x50 + errStack))
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜BytesMergeEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (0xe0 + (0x50 + errStack)) ∗
      match mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          bmExactPostVecGen reqCap A.repAlloc x.valPtr x.valCap v rest ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

theorem bytesMergeExactRawSpecGen_post_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (errStack : Nat) (reqCap : Bool)
    (x : BytesMergeGhost) (st : M.σ) (s0 sf : State) :
    (bytesMergeExactRawSpecGen A lim errStack reqCap).post (x, st) s0 sf ⊢
      (bytesMergeRawSpecGen A lim errStack reqCap).post (x, st) s0 sf := by
  dsimp only [bytesMergeExactRawSpecGen, bytesMergeRawSpecGen]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  cases mergeBytes x.wt x.bs with
  | none => exact Entails.refl _
  | some p =>
    rcases p with ⟨v, rest⟩
    exact sepConj_mono_right (sepConj_mono_left
      (bmExactPostVecGen_entails_bmPostVec reqCap A.repAlloc x.valPtr x.valCap v rest))

/-- Budget-threaded raw contract of `bytes::merge` at `bytesMergeStackX` exposing
`cap'.toNat = bmNextCap x.valCap.toNat v.length`. -/
def bytesMergeExactRawSpecX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BytesMergeGhost × M.σ) :=
  bytesMergeExactRawSpecGen A lim decodeErrorHookStackX true

/-- Relocatable budget-threaded exact-capacity contract of `bytes::merge` at
`bytesMergeStackX`. -/
def bytesMergeExactPlacedSpecX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (BytesMergeGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (bytesMergeExactRawSpecX A lim)

/-- `bytes::merge` meets `bytesMergeExactPlacedSpecX` under `[LibsignalPlacement]`. -/
abbrev BytesMergeExactPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
    (blkPl_7).base (bytesMergeExactPlacedSpecX A lim)

abbrev MergeExactPostGen {M : AllocCostModel} (errStack : Nat) (reqCap : Bool)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BytesMergeGhost) (st : M.σ) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  ((sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (bytesMergeExactRawSpecGen A lim errStack reqCap).post (x, st) s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev MergeExactPanicGen {M : AllocCostModel} (errStack : Nat) (reqCap : Bool)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BytesMergeGhost) (st : M.σ) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (bytesMergeExactRawSpecGen A lim errStack reqCap).onPanic (x, st) s0 sf ∗ R)

def bmShimSpecGen (errStack : Nat) : Spec Unit where
  pre := fun _ s => ⌜True⌝ ∗ stackAt s.sp (bmSliceStack errStack)
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗ stackAt s0.sp (bmSliceStack errStack)

def bmMemcpySpecGen (errStack : Nat) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s0.sp (bmSliceStack errStack))
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp (bmSliceStack errStack)

abbrev decodeVarintSlowSpecBMGen {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (errStack : Nat) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × M.σ) :=
  decodeVarintSlowBudgetSpecWithStack M A lim (64 + errStack)

abbrev decodeVarintSliceSpecBMGen {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (errStack : Nat) :
    Spec (CryptoVerification.LibsignalTripleRatchet.Prost.DecodeVarintSliceGhost × M.σ) :=
  decodeVarintSliceSpecGen A lim errStack

def bytesVtableDropSpecBMGenBase {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hStack : Nat) (ptr : BitVec 64)
    (bs : List (BitVec 8)) (off : Nat) : Spec M.σ where
  pre := fun st s =>
    ⌜off ≤ bs.length ∧
      s.readReg64 .x0 = bytesData ptr bs.length ∧
      s.readReg64 .x1 = bytesPtr ptr bs.length + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A.repAlloc ptr bs ∗
    A.pool lim st s ∗
    stackAt s.sp (hStack + 48)
  post := fun st s0 sf =>
    let st' := M.stepEvents (bytesDropEvents bs) st
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool lim st' sf ∗
    stackAt s0.sp (hStack + 48)

def bytesVtableDropSpecBMGen [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hStack : Nat) (ptr : BitVec 64)
    (bs : List (BitVec 8)) (off : Nat) : Spec M.σ where
  pre := fun st s =>
    ⌜off ≤ bs.length ∧
      s.readReg64 .x0 = bytesData ptr bs.length ∧
      s.readReg64 .x1 = bytesPtr ptr bs.length + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
    bytesBoxU8Buf A.repAlloc ptr bs ∗
    A.pool lim st s ∗
    stackAt s.sp (hStack + 48)
  post := fun st s0 sf =>
    let st' := M.stepEvents (bytesDropEvents bs) st
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool lim st' sf ∗
    stackAt s0.sp (hStack + 48)

theorem bytesVtableDrop_placed_of_base [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {hStack : Nat} {ptr : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    (h : subroutine_ok prog entry (withLsCl lsmpl (bytesVtableDropSpecBMGenBase A lim hStack ptr bs off))) :
    subroutine_ok prog entry (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim hStack ptr bs off)) := by
  refine subroutine_ok_outcome_intro fun st R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withLsCl lsmpl (bytesVtableDropSpecBMGenBase A lim hStack ptr bs off)).pre st s0 ∗ R := by
    dsimp only [withLsCl, CryptoVerification.withLsCodeLoaded,
      bytesVtableDropSpecBMGen, bytesVtableDropSpecBMGenBase] at hpre ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨h1, h2, h3, h4, _hlr⟩, hrest⟩
    exact ⟨⟨h1, h2, h3, h4⟩, hrest⟩
  exact h.mono_outcome st R s0 hpc hrun hpre' hal fun _ hout => hout

/-! ## Relocatable `[LibsignalPlacement]` epilogues and Phase 3 -/

theorem epilogue_err_0x0a4_placed_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    (hmerge : mergeBytes x.wt x.bs = none)
    (hevs : ∃ evs, BytesMergeEnv x evs ∧ st_cur = M.stepEvents evs st)
    (hpc : s.pc = (blkPl_7).base + 164#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 ≠ 0#64)
    (hhigh : bm_HighCalleeSaved s0 s) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (decodeErrorAtStackLen A.repAlloc (s.readReg64 .x0) 0 ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergeExactPostGen errStack reqCap A lim x st s0 R)
      (MergeExactPanicGen errStack reqCap A lim x st s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  obtain ⟨h25, h26, h27, h28⟩ := hhigh
  rcases hevs with ⟨evs, hevs_env, rfl⟩
  dsimp only [savedRegsStack] at hpc ⊢
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMergeGen s0.sp errStack hbnd
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self]⟩
  intro hmf
  dsimp only [Reg.x0, bmTotalStack, bmSliceStack] at hx0 hmf ⊢
  simp (config := { decide := true }) only [bytesMergeExactRawSpecGen, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64,
    RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64,
    Reg.x0, hx0, htrace, ↓reduceIte, ne_eq, not_false_eq_true, pure_true, emp_sepConj,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  simp only [hevs_env, pure_true, emp_sepConj]
  convert hmf using 2
  sep_ac_rfl

theorem epilogue_decodeErrorFrom_placed_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hdef : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim errStack)))
    {x : BytesMergeGhost} {st : M.σ} {s0 s : State} {R : SepProp} {w : BitVec 64}
    (hw : KindNoHeap w)
    (hmerge : mergeBytes x.wt x.bs = none)
    (hfits : FitsEnv M lim st (BytesMergeEnv x))
    (hpc : s.pc = (blkPl_7).base + 248#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (((s0.sp - 216#64) ↦₆₄ w) ∗ memRegion (s0.sp - 216#64 + 8#64) 40 ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool lim st s ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergeExactPostGen errStack reqCap A lim x st s0 R)
      (MergeExactPanicGen errStack reqCap A lim x st s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hfits_de : FitsEnv M lim st DecodeErrorFromEnv := by
    refine hfits.mono fun evs he => ?_
    simpa only [BytesMergeEnv, bytesMergeEventsCore, hmerge, DecodeErrorFromEnv] using he
  dsimp only [savedRegsStack] at hpc hdef ⊢
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := lsmpl.base 261)
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl_call hro_call
  refine SepWPp.bm_call_frame_lscl (x := (s0.sp - 216#64, w, st))
    (T := ((s0.sp - 216#64) ↦₆₄ w) ∗ memRegion (s0.sp - 216#64 + 8#64) 40 ∗
      A.pool lim st _ ∗ stackAt (s0.sp - 224#64) errStack)
    hdef hcl_call hro_call
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [decodeErrorFromBudgetSpecWithStack, arm64_norm, hsp]; rfl)
    (by simp (config := { decide := true }) only [KindNoHeap, wp_norm, arm64_norm, hsp, hw, hfits_de, and_self])
    (by rw [stackAt_sliceGen_split s0.sp errStack errStack (Nat.le_add_left errStack 0x50) hbnd]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (by intro _ _ hm; dsimp only [decodeErrorFromBudgetSpecWithStack] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
  intro sf_de hpcf hrunf hspf hcsf _ _
  have hhigh' : bm_HighCalleeSaved s0 sf_de := hhigh.of_calleeSaved hcsf
  obtain ⟨h25, h26, h27, h28⟩ := hhigh'
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf
  simp (config := { decide := true }) only [decodeErrorFromBudgetSpecWithStack, arm64_norm, hsp, htrace]
  refine SepWPp.exists_elim fun evs => ?_
  refine SepWPp.pure_elim fun ⟨⟨hx0, htr⟩, hevs_de⟩ => ?_
  have hevs_bm : BytesMergeEnv x evs := by
    simpa only [BytesMergeEnv, bytesMergeEventsCore, hmerge, DecodeErrorFromEnv] using hevs_de
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) (bmSliceStack errStack))
    (by rw [stackAt_sliceGen_split s0.sp errStack errStack (Nat.le_add_left errStack 0x50) hbnd]; exact Entails.refl _) (by sep_focus)
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMergeGen s0.sp errStack hbnd
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self]⟩
  intro hmf
  dsimp only [bmTotalStack, bmSliceStack] at hmf
  simp (config := { decide := true }) only [bytesMergeExactRawSpecGen, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64,
    RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64,
    Reg.x0, hx0, htr, ↓reduceIte, ne_eq, not_false_eq_true, pure_true, emp_sepConj,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  simp only [hevs_bm, pure_true, emp_sepConj]
  convert hmf using 2
  sep_ac_rfl

theorem epilogue_vtableDrop_0x2d8_placed_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hdrop_le : hStack + 48 ≤ bmSliceStack errStack)
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim hStack tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hevs : ∃ evs, BytesMergeEnv x evs ∧ M.stepEvents (bytesDropEvents v) st_cur = M.stepEvents evs st)
    (hcapOk : bmCapCond reqCap cap' rest.length)
    (hcapEq : cap'.toNat = bmNextCap x.valCap.toNat v.length)
    (hpc : s.pc = (blkPl_7).base + 728#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length + BitVec.ofNat 64 v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx24 : s.readReg64 .x24 = bytesPlacedVtable tmpPtr v.length) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr cap' ptr' v ∗
        bytesBoxU8Buf A.repAlloc tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergeExactPostGen errStack reqCap A lim x st s0 R)
      (MergeExactPanicGen errStack reqCap A lim x st s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  rcases hevs with ⟨evs, hevs_env, hevs_eq⟩
  dsimp only [savedRegsStack] at hpc hVtableDrop ⊢
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := bytesPlacedDropFnAddr tmpPtr v.length)
  apply SepWP.with_vtableSlot_placed tmpPtr v.length hro
  wp_steps
  apply SepWP.drop_left
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl_call hro_call
  refine SepWPp.bm_call_frame_lscl (x := st_cur)
    (T := bytesBoxU8Buf A.repAlloc tmpPtr v ∗ A.pool lim st_cur _ ∗ stackAt (s0.sp - 224#64) (hStack + 48))
    hVtableDrop hcl_call hro_call
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [bytesVtableDropSpecBMGen, arm64_norm, hsp]; rfl)
    (by
      simp only [Nat.le_refl, Nat.sub_self, BitVec.ofNat_eq_ofNat, true_and]
      simp only [wp_norm, arm64_norm, blkPl_7]
      apply lsRetAddr624_blockPlacement_base_add <;> decide)
    (by rw [stackAt_sliceGen_split s0.sp errStack (hStack + 48) hdrop_le hbnd]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (by intro _ _ hm; dsimp only [bytesVtableDropSpecBMGen] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
  intro sf_dr hpcf hrunf hspf hcsf _ _
  have hhigh' : bm_HighCalleeSaved s0 sf_dr := hhigh.of_calleeSaved hcsf
  obtain ⟨h25, h26, h27, h28⟩ := hhigh'
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf
  simp (config := { decide := true }) only [bytesVtableDropSpecBMGen, hevs_eq, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun htr => ?_
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) (bmSliceStack errStack))
    (by rw [stackAt_sliceGen_split s0.sp errStack (hStack + 48) hdrop_le hbnd]; exact Entails.refl _) (by sep_focus)
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMergeGen s0.sp errStack hbnd
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_focus)
  apply SepWP.fold
    (vecU8At_entails_bmExactPostVecGen reqCap A.repAlloc x.valPtr x.valCap cap' ptr' v rest hcapOk hcapEq)
    (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self]⟩
  intro hmf
  dsimp only [bmTotalStack, bmSliceStack] at hmf
  simp (config := { decide := true }) only [bytesMergeExactRawSpecGen, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64,
    RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64,
    Reg.x0, htr, ↓reduceIte, pure_true, emp_sepConj, sepExists_sepConj_left,
    sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  simp only [hevs_env, pure_true, emp_sepConj]
  convert hmf using 2
  sep_ac_rfl

theorem phase3_from_0x2b4_placed_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hdrop_le : hStack + 48 ≤ bmSliceStack errStack)
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (blkPl_7.ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen errStack)))
    {x : BytesMergeGhost} {st st_cur : M.σ} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpecBMGen A lim hStack tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hevs : ∃ evs, BytesMergeEnv x evs ∧ M.stepEvents (bytesDropEvents v) st_cur = M.stepEvents evs st)
    (hcapOk : bmCapCond reqCap cap' rest.length)
    (hcapEq : cap'.toNat = bmNextCap x.valCap.toNat v.length)
    (hcap' : v.length ≤ cap'.toNat)
    (hv_len : v.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_7).base + 692#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx23 : s.readReg64 .x23 = 0#64)
    (hx24 : s.readReg64 .x24 = bytesPlacedVtable tmpPtr v.length) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc x.valPtr cap' ptr' [] ∗
        bytesBoxU8Buf A.repAlloc tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergeExactPostGen errStack reqCap A lim x st s0 R)
      (MergeExactPanicGen errStack reqCap A lim x st s0 R) := by
  rcases v with _ | ⟨b0, v'⟩
  · have hep := fun {s : State} =>
      @epilogue_vtableDrop_0x2d8_placed_gen _ M A lim H hStack errStack reqCap hbnd hdrop_le x st st_cur s0 s R [] rest tmpPtr cap' ptr' hVtableDrop hmerge hevs hcapOk hcapEq
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_7).base + bv% (728))
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    refine SepWPp.weaken_pre ?_ (hep
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      hhigh hcl1 hro1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx21])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx24]))
    exact Entails.of_eq (by simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64])
  · set v := b0 :: v'
    have hep := fun {s : State} =>
      @epilogue_vtableDrop_0x2d8_placed_gen _ M A lim H hStack errStack reqCap hbnd hdrop_le x st st_cur s0 s R v rest tmpPtr cap' ptr' hVtableDrop hmerge hevs hcapOk hcapEq
    have hpos : 0 < v.length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
    have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlen_ne : (BitVec.ofNat 64 v.length == 0#64) = false := by
      apply beq_false_of_ne
      intro h
      have h2 := congrArg BitVec.toNat h
      rw [hlen_toNat] at h2
      exact absurd h2 (by dsimp [v]; omega)
    have hbytesPtr : bytesPtr tmpPtr v.length = tmpPtr := by
      unfold bytesPtr
      have : v.length ≠ 0 := by omega
      simp [this]
    rw [vecU8At_nil_eq A.repAlloc x.valPtr cap' ptr' v hpos hcap', sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, hcap_lt, hptr'⟩ => ?_
    rw [bytesBoxU8Buf_nonempty A.repAlloc tmpPtr v hpos]
    refine SepWPp.weaken_pre (P' := ⌜tmpPtr ≠ 0#64 ∧ v.length < 2 ^ 63⌝ ∗
      ((x.valPtr ↦₆₄ cap') ∗ ((x.valPtr + 8#64) ↦₆₄ ptr') ∗ ((x.valPtr + 16#64) ↦₆₄ 0#64) ∗
        A.repAlloc.live ptr' cap'.toNat 1 ∗ memRegion ptr' v.length ∗
        memRegion (ptr' + BitVec.ofNat 64 v.length) (cap'.toNat - v.length) ∗
        A.repAlloc.live tmpPtr v.length 1 ∗ (tmpPtr ↦ₛ v) ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool lim st_cur s ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)) (Entails.of_eq (by sep_ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨htmp_ne, hv_lt63⟩ => ?_
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := blkPl_7.ρ "memcpy")
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hlen_ne])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    refine SepWPp.bm_call_frame_lscl (x := (ptr', tmpPtr, v))
      (T := memRegion ptr' v.length ∗ (tmpPtr ↦ₛ v) ∗ stackAt (s0.sp - 224#64) (bmSliceStack errStack))
      hmc hcl1 hro1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hlen_ne])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by simp (config := { decide := true }) only [bmMemcpySpecGen, arm64_norm, hsp]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm, hlen_toNat, and_self])
      (by sep_focus)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (by intro _ _ hm; dsimp only [bmMemcpySpecGen] at hm; rw [sepConj_assoc] at hm; exact False.elim (not_satisfies_false_sepConj hm)) ?_
    intro sf_mc hpcf hrunf hspf hcsf hclf hrof
    have hhigh' : bm_HighCalleeSaved s0 sf_mc := hhigh.of_calleeSaved hcsf
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, _, _, _, _, h29f⟩ := hcsf
    simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf h19f h20f h21f h22f h23f h24f h29f
    simp (config := { decide := true }) only [bmMemcpySpecGen, arm64_norm, hsp, htrace]
    refine SepWPp.pure_elim fun ⟨_, htr, hvm_mc⟩ => ?_
    have hpool_mc : A.pool lim st_cur s = A.pool lim st_cur sf_mc := by
      have hvm_s : VmPreserved sf_mc s := by
        simpa only [LibsignalBinary.Proofs.Placed.BudgetVmSteps.vmPreserved_setPC,
          LibsignalBinary.Proofs.Placed.BudgetVmSteps.vmPreserved_setPState,
          LibsignalBinary.Proofs.Placed.BudgetVmSteps.vmPreserved_writeReg64] using hvm_mc.symm
      exact A.pool_of_vmPreserved hvm_s
    rw [hpool_mc]
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_7).base + bv% (728))
    wp_steps_sync_pool ((blkPl_7).base + bv% (728))
    have hfb := fold_bytesBoxU8Buf_nonempty A.repAlloc tmpPtr v hpos htmp_ne hv_lt63
    dsimp only [RustCliAllocBudget.repAlloc] at hfb
    apply SepWP.fold hfb (by sep_focus)
    have hfv := fold_vecU8At_copied A.repAlloc x.valPtr cap' ptr' v hpos hcap' hcap_lt hptr'
    dsimp only [RustCliAllocBudget.repAlloc] at hfv
    apply SepWP.fold hfv (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hcl2 hro2
    refine SepWPp.weaken_pre ?_ (hep
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by obtain ⟨h25, h26, h27, h28⟩ := hhigh'; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f, hx21, h20f, hx20, hbytesPtr])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h22f, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24f, hx24]))
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## Shim and `memcpy` stack-lifting bridges -/

theorem bmShim_placed_of_base [LibsignalPlacement] {prog : Program} {addr : BitVec 64}
    {errStack : Nat} (hshim : subroutine_ok prog addr sessionShimBudgetSpec) :
    subroutine_ok prog addr (withLsCl lsmpl (bmShimSpecGen errStack)) := by
  apply subroutine_ok_withLsCl_of_plain
  have h := subroutine_ok_withStack_of_subroutine_ok hshim (bmSliceStack errStack)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack sessionShimBudgetSpec (bmSliceStack errStack)).pre x s0 ∗ R := by
    dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack,
      sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec,
      bmShimSpecGen] at hpre ⊢
    simpa only [pure_true, emp_sepConj, sepConj_assoc] using hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex | hoom)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack,
      sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec,
      bmShimSpecGen] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem bmMemcpy_placed_of_frameless [LibsignalPlacement] {prog : Program} {addr : BitVec 64}
    {errStack : Nat}
    (hmc : subroutine_ok prog addr (withVmPreserved framelessMemcpySpec)) :
    subroutine_ok prog addr (withLsCl lsmpl (bmMemcpySpecGen errStack)) := by
  apply subroutine_ok_withLsCl_of_plain
  have h := subroutine_ok_withStack_of_subroutine_ok hmc (bmSliceStack errStack)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨
      (withStack (withVmPreserved framelessMemcpySpec) (bmSliceStack errStack)).pre x s0 ∗ R := by
    dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack,
      withVmPreserved, framelessMemcpySpec, bmMemcpySpecGen] at hpre ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex | hoom)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack,
      withVmPreserved, framelessMemcpySpec, bmMemcpySpecGen] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost.2.2⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem bmMemcpy_placed_of_region [LibsignalPlacement] {prog : Program} {addr : BitVec 64}
    {errStack : Nat}
    (hmc : subroutine_ok prog addr sessionMemcpyRegionBudgetSpec) :
    subroutine_ok prog addr (withLsCl lsmpl (bmMemcpySpecGen errStack)) :=
  bmMemcpy_placed_of_frameless hmc

end LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget
